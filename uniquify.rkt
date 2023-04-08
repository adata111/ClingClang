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
        [(Var x) (cond [(dict-has-key? env x) (dict-ref env x)] [else (Var x)])]        ; if the expression is a Var struct, find the referenced value of the Var-struct's symbol in the environment
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
          (Prim op (for/list ([opd es]) (uniquify-exp opd env)))]
        [(Apply fun-exp arg-exps) (Apply  (uniquify-exp fun-exp env)
                                          (for/list ([each-exp arg-exps])
                                                    (uniquify-exp each-exp env)))]
        )
  )

  (define (make-new-env-with-args old-env param-list)                     ; If any parameter is the same as some other function name, give that parameter a new symbol and return the updated environment
    (for/fold ([new-env old-env]) ([each-param param-list])
                                  (match each-param [`(,param-sym : ,t)   ; Each param is a "tuple" of param-symbol and the param-type
                                                    (cond [(dict-has-key? old-env param-sym)  ; If this param exists in the environment, generate a new symbol and return the updated environment
                                                            (let ([new-sym (gensym param-sym)]) (dict-set new-env param-sym (Var new-sym)))]
                                                          [else new-env])]))                  ; If this param doesn't exist in the environment, return the same environment
  )

  (define (replace-param-list param-list new-env)             ; If any param in the param-list is the same as some other function, they have a new symbol in new-env that they should be replaced with

    (define (get-symbol-func inp-sym)
      (match inp-sym
        [(Var x) x]
        [else inp-sym]
      )
    )

    (for/list ([each-param param-list]) (match each-param                 ; Reconstruct the entire param-list by replacing the necessary ones
                                              [`(,param-sym : ,t)         ; Each param is a "tuple" of param-symbol and the param-type
                                                (cond                     ; If this param has to be replaced, create the new "tuple" and replace it in the param-list
                                                    [(dict-has-key? new-env param-sym) `(,(get-symbol-func (dict-ref new-env param-sym)) : ,t)]
                                                    [else `(,param-sym : ,t)])]))
  )

  (define (uniquify-each-function fun-def all-fun-names)                                    ; Uniquifies the parameter list and the body of the given function to not have a local variable with the same name as some other function
    (match fun-def
      [(Def fun-name param-list ret-type fun-info fun-body)
        (let* ( [new-env-all-fun-names (make-new-env-with-args all-fun-names param-list)]   ; Get an updated environment if any of the parameters of this function is the same as some other function name 
                [new-param-list (replace-param-list param-list new-env-all-fun-names)]      ; Replace the parameters in the param-list by looking at the new environment (if any of the params are other function names)
                [new-fun-body (uniquify-exp fun-body new-env-all-fun-names)])               ; Replace the variables in the body of the function by looking at the new environment (if any of those variables are other function names)
              (Def fun-name new-param-list ret-type fun-info new-fun-body))]
    )
  )

  (match p
    [(ProgramDefs info defs) (let* ([all-fun-names                                                                    ; Get the function name symbols of all functions
                                      (for/fold ([fun-names '()]) ([def defs])                                        ; Go through each function definition and store the function name as a Var
                                                                  (match def [(Def fun-name _ _ _ _)
                                                                              (dict-set fun-names fun-name (Var fun-name))]))]
                                    [new-defs (for/list ([def defs]) (uniquify-each-function def all-fun-names))])    ; Replace other occurrences of these function names in the parameter list or in the body of other functions
                            (ProgramDefs info new-defs))])
)

