#lang racket

(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "priority_queue.rkt")
(require "interp.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))

;; uniquify : R1 -> R1
(define (uniquify p)

  (define (uniquify-exp e env)
      (match e
        [(Var x) (dict-ref env x)]        ; if the expression is a Var struct, find the referenced value of the Var-struct's symbol in the environment
        [(Int n) (Int n)]                 ; if the expression is an Int struct object, just return the same
        [(Bool n) (Bool n)]                 ; if the expression is a Bool struct object, just return the same
        [(Let x e body)
          (cond                           ; check if the symbol being defined by Let already has another reference in the environment
            [(dict-has-key? env x)          ; if key already exists in env, make a new symbol for this key and save in environment
                (let ([new-sym (gensym x)])                                                 ; generate new symbol for x
                  (let ([new-env (dict-set env x (Var new-sym))])                           ; make a new environment mapping x to Var struct of new-sym
                    (Let new-sym (uniquify-exp e env) (uniquify-exp body new-env))  ; recursively uniquify Let exp and body. Exp needs the old env, body needs the new-env
                  ))]
            [else                           ; if key does not exist in env, map this symbol to it's own Var struct
              (let ([new-env (dict-set env x (Var x))])                                     ; add this symbol's Var struct to env to show that it should reference itself
                (Let x (uniquify-exp e env) (uniquify-exp body new-env))            ; recursively uniquify let exp and body
              )]
          )
        ]
        [(If cnd e1 e2) (If (uniquify-exp cnd env) (uniquify-exp e1 env) (uniquify-exp e2 env))]
        [(Prim op es)                     ; if the expression is an operator and operands, uniquify all operands
          (Prim op (for/list ([opd es]) (uniquify-exp opd env)))])
  )

  (match p
    [(Program info e) (Program info (uniquify-exp e '()))])
)
