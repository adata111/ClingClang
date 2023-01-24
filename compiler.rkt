#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

(define (uniquify-exp env)
  (lambda (e)
    (match e

      [(Var x)                          ; if the expression is a Var struct, find the referenced value of the Var-struct's symbol in the environment
        (dict-ref env x)]

      [(Int n) (Int n)]                 ; if the expression is an Int struct object, just return the same

      [(Let x e body)
        (cond                           ; check if the symbol being defined by Let already has another reference in the environment
        [(dict-has-key? env x)          ; if key already exists in env, make a new symbol for this key and save in environment
            (let ([new-sym (gensym x)])                                                 ; generate new symbol for x
              (let ([new-env (dict-set env x (Var new-sym))])                           ; make a new environment mapping x to Var struct of new-sym
                (Let new-sym ((uniquify-exp new-env) e) ((uniquify-exp new-env) body))  ; recursively uniquify Let exp and body
              ))]

        [else                           ; if key does not exist in env, map this symbol to it's own Var struct
          (let ([new-env (dict-set env x (Var x))])                                     ; add this symbol's Var struct to env to show that it should reference itself
            (Let x ((uniquify-exp new-env) e) ((uniquify-exp new-env) body))            ; recursively uniquify let exp and body
          )]
        )
      ]

      [(Prim op es)                     ; if the expression is an operator and operands, uniquify all operands
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)

  (printf "\n\nRemoving complex operands ~v\n" p)

  (define (make-var var-change)
    (cond
      [(symbol? var-change) (Var var-change)]
      [else var-change])
    )

  (define (rco_atom exp-to-atom)
    (match exp-to-atom
      [(Int a) (values (Int a) '())]    ; If the expressions are simple already
      [(Var a) (values (Var a) '())]    ; return them as it is with an empty environment


      [(Let x e body)       ; to convert the let into an atomic: (1) assign a tmp to the simplified expression e, (2) make the body an atomic and assign to a variable body-var (3) return the body-var and environment with body-var
        (let* ([exp-simple (gensym "clingclang")] [exp-simple (rco_exp e)])
              (let-values ([(tmp-body body-env) (rco_atom body)]) (values tmp-body (dict-set body-env x exp-simple))))    ; extract the body's symbol and env with let-values and return the body's symbol along with the env with the newly let'ed variable 
      ]

      [(Prim op es) (let* ([prim-atm (gensym "clingclang")] [es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))] ; if it is a primitive, first get the atomic exps of all operands
                            [full-env                                                                           ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops  (list (make-var (car each-ret)))))]
                            )
                          (values prim-atm (dict-set full-env prim-atm (Prim op all-op-atms))))]                ; return the symbol for the entire prim expression along with the environment 
    ))

  (define (get-symbol-func inp-sym)
  (match inp-sym
    [(Var x) (x)]
    [else inp-sym]
  )
  )

  (define (recursively-add-lets env inp-exp)
    (match inp-exp                                            ; if this is an Prim op, add the defintions of the operands from the environment
      [(Prim op es) (for/fold ([result (Prim op es)])         ; use for/fold to get the nested Lets for 1/2/more operands, the initial result is the prim as it is, in case no Let's happen
                                ([each-opd es])
                                (match each-opd               ; wrap the result around a Let only if it is a Var symbol
                                  [(Var v)
                                    (cond
                                      [(dict-has-key? env v) (Let v (recursively-add-lets env (dict-ref env v)) result)]
                                      [else result])          ; if this symbol is not in the env, it has already Let'ed before, return the result as it is
                                  ]
                                  [_ result]))
        ]
      [_ inp-exp]
    )
  )

  (define (rco_exp exp-to-exp)
    (match exp-to-exp
      [(Int a) (Int a)]
      [(Var a) (Var a)]
      [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
      ;[(Prim op es) (let* ([es-rets (for/list ([each-e es]) (rco_atom each-e))]
      [(Prim op es) (let* ([es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))]

                            [full-env                                                                         ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops  (list (make-var (car each-ret)))))]
                          )
                          (recursively-add-lets full-env (Prim op all-op-atms))                               ; wrap this primitive op es around lets that define the operands of this Prim
                    )]
    )
  )
  
  (match p
    [(Program info body) (Program info (rco_exp body))]
  ))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Return r) (Return r)]
    [(Let x rhs body) (explicate_assign x rhs (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [_ e]
  )
)

(define (explicate_assign x e cont)
  (match e
    [(Var a) (Seq (Assign (Var x) (Var a)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Prim op es) (Seq (Assign (Var x) e) cont)]
    [(Let y rhs body) (explicate_assign y rhs (explicate_assign x body cont))]
  )
)

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info `((start . ,(explicate_tail body))))])
)

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
     ("uniquify", uniquify, interp-Lvar, type-check-Lvar)
     ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
     ("explicate control", explicate-control, interp-Cvar, type-check-Cvar)
     ))
