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

(define (flip p)
  (define (flip-e e)
    (match e
      [(Int n) (Int n)]
      [(Var x) (Var x)]
      [(Prim op (list e1 e2)) (Prim op (list (flip-e e2) (flip-e e1)))]
      [(Prim op es) (Prim op (for/list [(e es)] (flip-e e)))]
      [(Let x rhs body) (Let x (flip-e rhs) (flip-e body))]
      [_ (error "Nothing matches")]))

  (match p
    [(Program info body)
     (Program info (flip-e body))]))


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

;; remove-complex-opera* : R1 -> R1

; ;; Replace all non-atomic operands with atomic operands
; (define (remove-complex-opera* p)

;   (define (rco_atom exp-to-atom)

;   )

;   (define (rco_exp exp-to-exp)
;     ; Take an expression in Lvar and 
;   )
  
;   (match p
;     [(Program info body) (Program info (rco_exp body))] ; TODO do for/each exp
;                                                         ; info will have alist of vars after explicate_control
;   ))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
     ;; ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ))
