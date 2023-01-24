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
  (printf "Entered rco_atom with ~v\n-----\n" exp-to-atom)
    (match exp-to-atom
      [(Int a) (values (Int a) '())]    ; If the expressions are simple already
      [(Var a) (values (Var a) '())]    ; return them as it is with an empty environment


      [(Let x e body)       ; to convert the let into an atomic: (1) assign a tmp to the simplified expression e, (2) make the body an atomic and assign to a variable body-var (3) return the body-var and environment with body-var
        (let* ([exp-simple (gensym "clingclang")] [exp-simple (begin (printf "Entering rco_exp from rco_atom let exp-simple with ~v\n----\n" e) (rco_exp e))])
              (let-values ([(tmp-body body-env) (rco_atom body)]) (values tmp-body (dict-set body-env x exp-simple))))    ; extract the body's symbol and env with let-values and return the body's symbol along with the env with the newly let'ed variable 
      ]

      [(Prim op es) (let* ([prim-atm (gensym "clingclang")] [es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))] ; if it is a primitive, first get the atomic exps of all operands
                            [full-env                                                                           ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops  (list (make-var (car each-ret)))))]
                            )
                          (values prim-atm (dict-set full-env prim-atm (Prim op all-op-atms))))]                ; return the symbol for the entire prim expression along with the environment 
    )
  )

  (define (rco_exp exp-to-exp)
    (printf "Entered rco_exp with ~v\n-----\n" exp-to-exp)
    (match exp-to-exp
      [(Int a) (Int a)]
      [(Var a) (Var a)]
      [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
      ;[(Prim op es) (let* ([es-rets (for/list ([each-e es]) (rco_atom each-e))]
      [(Prim op es) (let* ([es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))]

                            [full-env                                                                           ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops  (list (make-var (car each-ret)))))]
                          )
                          (for/foldr ([result (Prim op all-op-atms)]) ([each-entry full-env]) (Let (car each-entry) (cdr each-entry) result))
                    )]
    )
  )
  
  (match p
    [(Program info body) (Program info (begin (printf "Entering from program info with ~v\n\n" body) (rco_exp body)))] ; TODO do for/each exp
                                                        ; info will have alist of vars after explicate_control
  ))






(define (explicate_tail e)
  (printf "\n\nExplTail ~v\n---\n" e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Return r) (Return r)]
    [(Let x rhs body) (explicate_assign x rhs (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [_ e]
  )
)

;     [(Let y rhs body) (Seq (Assign (Var x) (explicate_assign rhs y body)) (explicate_tail cont))] doubtful line in assign

(define (explicate_assign x e cont)
(printf "\n\nExplAssign x:~v\ne:~v\ncont:~v\n---\n"x e cont)
  (match e
    [(Var a) (Seq (Assign (Var x) (Var a)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign y rhs (explicate_assign x body cont))]
    [(Prim op es) (Seq
       (Assign (Var x) e) cont)]
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
     ;; ("uniquify", uniquify, interp-Lvar, type-check-Lvar)
     ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
     ;; ("explicate control", explicate-control, interp-Cvar, type-check-Cvar)
     ))


; ; (define file (command-line #:args (filename) filename))
; (define file "tests/var_test_18.rkt")
; (define ast (read-program file))

; (debug-level 1)
; (AST-output-syntax 'concrete-syntax)

; (define (opt passes ast)
;   (pretty-print ast)
;   (match passes
;     ['() ast]
;     [(list (list name fun interp type-check) more ...)
;      (println (string-append "Applying " name))
;      (opt more (type-check (fun ast)))]
;     [(list (list name fun interp) more ...)
;      (println (string-append "Applying " name))
;      (opt more (fun ast))]
;     [(list (list name fun) more ...)
;      (println (string-append "Applying " name))
;      (opt more (fun ast))]))

; (define final (opt compiler-passes ast))
