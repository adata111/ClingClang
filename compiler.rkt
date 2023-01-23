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
 
  (define (rco_atom exp-to-atom env)
    ;(printf "\n\nEntered RA exp:~v env:~v\n" exp-to-atom env)
    ; (match exp-to-atom
    ;   [(Prim op es)
    ;     (begin(
    ;       (printf "RA prim ~v ~v\n" op es)
    ;       (let* (
    ;         [temp (gensym "clingclang")]
    ;         [temp-list (for/list ([e es]) (rco_atom e env))]
    ;         [ret-prim (Prim op (for/list ([t temp-list]) (begin (printf "Making ret-prim ~v\n" (car t)) (car t))))]
    ;         [ret-env (append env (list (append (for/list ([t temp-list]) (cadr t)))))]
    ;       )
    ;       (begin (printf "Body of let* has temp:~v t-list:~v ret-prim:~v ret-env:~v\n"temp temp-list ret-prim ret-env) (list temp (append ret-env (list* temp ret-prim))))
    ;       )
    ;     ))
    ;   ]
    ;   [(Let x e body) (Let x e body)]
    ;   [(Var a) (Var a) ]
    ;   [(Int n) (list (Int n) '()) ]
    ; )

    (define (match-return ax)
        (match (car ax)
          [(Var a) (Var a)]
          [(Int a) (Int a)]
          [(var a) (dict-ref (cadr ax) a)]
        )
    )

    (match exp-to-atom
      [(Prim op es)
        (begin
          (printf "Matched prim Ratom op:~v es:~v\n" op es)
          (let* ([temp-symbol (gensym "clingclang")]
                [temp-rco-atom-list (for/list ([e es]) (rco_atom e env))]
                [ops-list (for/list ([atom-ret temp-rco-atom-list])
                                    (

                                      match-return atom-ret

                                      ; (match (car atom-ret)
                                      ;   [(Var a) (Var a)]
                                      ;   [(Int a) (Int a)]
                                      ;   [(var a) (dict-ref (cadr atom-ret) a)]
                                      ; )

                                    ))
                                    ] ; construct the ops from the rco_atom outputs
                [ret-exp (Prim op ops-list)]
                )
            (list temp-symbol (dict-set env temp-symbol (Let temp-symbol ret-exp (Var temp-symbol)))) ; return the atomic and the environment
          )
        )
      ]
      [(Let x e body) (let* ([temp-symbol (gensym "clingclang")]
                            [temp-expr (rco_exp (Let x e body))])
                            (list temp-symbol (dict-set env temp-symbol temp-expr))
      )]

      [(Var a) (list (Var a) env)]
      [(Int n) (list (Int n) env)]
    )
  )

  (define (func boom)
  (printf "in func ~v\n" boom)
  (printf "in func result ~v\n" (rco_atom boom '()))
    (let ([rco-atom-ret (rco_atom boom '())]) 
                (cond
                  [(null? (cadr rco-atom-ret)) (
                      match (car rco-atom-ret) 
                      [(Var a) (Var a)]
                      [(Int a) (Int a)]
                        )]
                  [else (dict-ref (cadr rco-atom-ret) (car rco-atom-ret))]
                )
  ))

  (define (rco_exp exp-to-exp)
    (match exp-to-exp

      [(Prim op es) (begin  (Prim op (for/list ([each-e es]) (begin (printf "exp iter each-e:~v \n" each-e) (func each-e)))))]

      ; [(Prim op es) (Prim op (for/list ([each-e es]) ((lambda (e) (let ([rco-atom-ret (rco_atom e '())]) (
      ;                                                                                     (cond
      ;                                                                                       [(null? (cadr rco-atom-ret)) (
      ;                                                                                           match (car rco-atom-ret) 
      ;                                                                                           [(Var a) (Var a)]
      ;                                                                                           [(Int a) (Int a)]
      ;                                                                                             )]
      ;                                                                                       [else (dict-ref (cadr rco-atom-ret) (car rco-atom-ret))]
      ;                                                                                     )
                                      
      ;                                    ))) each-e )))]
      [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
      [(Int a) (Int a)]
      [(Var a) (Var a)]
      )
  )
  
  (match p
    [(Program info body) (Program info (rco_exp body))] ; TODO do for/each exp
                                                        ; info will have alist of vars after explicate_control
  ))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
     ;; ("uniquify", uniquify, interp-Lvar, type-check-Lvar)
     ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
     ;; ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ))
