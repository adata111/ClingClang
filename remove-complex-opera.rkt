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


; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)

  (define (make-var var-change)
    (cond
      [(symbol? var-change) (Var var-change)]
      [else var-change])
    )

  (define (rco_atom exp-to-atom)
    ; (printf "Got rco_atom: ~v\n" exp-to-atom)
    (match exp-to-atom
      [(Int a) (values (Int a) '())]      ; If the expressions are simple already
      [(Var a) (values (Var a) '())]      ; return them as it is
      [(Bool a) (values (Bool a) '())]    ; with an empty environment

      [(FunRef fun-name arity)            ; FunRef is supposed to be a complex expression, assign the FunRef to a symbol and return the environment
        (let* (
                [prim-atm (gensym "clingclang")]
                [new-env (list (cons prim-atm (FunRef fun-name arity)))]
              )
              (values prim-atm new-env))]

      [(Let x e body)       ; to convert the let into an atomic: (1) assign a tmp to the simplified expression e, (2) make the body an atomic and assign to a variable body-var (3) return the body-var and environment with body-var
        (let-values ([(tmp-body body-env) (rco_atom body)]) (values tmp-body (cons ( cons x (rco_exp e)) body-env)))    ; extract the body's symbol and env with let-values and return the body's symbol along with the env with the newly let'ed variable 
      ]

      [(If cnd e1 e2)
        (let* (
                [prim-atm (gensym "clingclang")]
                [new-env (list (cons prim-atm (If (rco_exp cnd) (rco_exp e1) (rco_exp e2))))]
              )
              (values prim-atm new-env))]

      [(Prim op es) (let* ( [prim-atm (gensym "clingclang")]
                            [es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))] ; if it is a primitive, first get the atomic exps of all operands
                            [full-env                                                                           ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops (list (make-var (car each-ret)))))]
                            [new-env (append full-env (list (cons prim-atm (Prim op all-op-atms))))]
                            )
                          (values prim-atm new-env))]                ; return the symbol for the entire prim expression along with the environment 

      [(Apply fun-exp arg-exps) 
      (let* (     [prim-atm (gensym "clingclang")]
                  [arg-rets (for/fold ([ret-vals '()]) ([each-arg (append (list fun-exp) arg-exps)]) (let-values([(arg-sym arg-env) (rco_atom each-arg)]) (append ret-vals (list (list arg-sym arg-env)))))]
                  [full-env                                                                         ; combine the environments of the atomicized arguments of the function
                      (for/fold ([full-env '()]) ([each-ret arg-rets]) (append full-env (cadr each-ret)))]
                  [all-op-atms                                                                      ; get all the atomicized arguments. First element of all-op-atms is the function expression (first expression that has to return a function)
                      (for/fold ([all-ops '()]) ([each-ret arg-rets]) (append all-ops (list (make-var (car each-ret)))))]
                          [new-env (append full-env (list (cons prim-atm (Apply (car all-op-atms) (cdr all-op-atms)))))]
                          )
                          (values prim-atm new-env))] 

    ))

  (define (get-symbol-func inp-sym)
    (match inp-sym
      [(Var x) x]
      [(FunRef f _) f]
      [else inp-sym]
    )
  )

  (define (has-been-letted? inp-exp inp-sym)                                  ; check if this symbol has been letted in this expression or somewhere in its subexpressions
    (match inp-exp
      [(Let x e body) (or (equal? x inp-sym) (or (has-been-letted? e inp-sym) (has-been-letted? body inp-sym)))]  ; the symbol is either in this let body, or in the rhs, or the body
      [_ #f]
    )
  )

  (define (recursively-add-lets env inp-exp used-syms)                  ; function to add all environment variables in nested Let's
    (for/foldr  ([result inp-exp])
                ([(each-env-var each-env-entry) (in-dict env)])         ; go through all entries in the environment dictionary
                (cond                                                   ; check if this particular symbol has been let'ed already, don't Let again if so
                  [(has-been-letted? result each-env-var) result]
                  [else (Let each-env-var each-env-entry result)]
                )
    )
  )

  (define (rco_exp exp-to-exp)
    (match exp-to-exp
      [(Int a) (Int a)]
      [(Var a) (Var a)]
      [(Bool a) (Bool a)]
      [(FunRef fname arity) (FunRef fname arity)]

      [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
      [(If cnd e1 e2) (If (rco_exp cnd) (rco_exp e1) (rco_exp e2))]
      [(Prim op es) (let* ( [es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))]
                            [full-env                                                                         ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops (list (make-var (car each-ret)))))]
                            [letted-exp (recursively-add-lets full-env (Prim op all-op-atms) (for/list ([each-opd all-op-atms]) (get-symbol-func each-opd)))]          ; wrap the the atomic operands that are not used in the expression, but have been let'ed somewhere in the actual expression
                          )
                          letted-exp                               ; wrap this primitive op es around lets that define the operands of this Prim
                    )]
      [(Apply fun-exp arg-exps) 
        (let* (   [arg-rets (for/fold ([ret-vals '()]) ([each-arg (append (list fun-exp) arg-exps)]) (let-values([(arg-sym arg-env) (rco_atom each-arg)]) (append ret-vals (list (list arg-sym arg-env)))))]
                  [full-env                                                                         ; combine the environments of the atomicized arguments of the function
                      (for/fold ([full-env '()]) ([each-ret arg-rets]) (append full-env (cadr each-ret)))]
                  [all-op-atms                                                                      ; get all the atomicized arguments. First element of all-op-atms is the function expression (first expression that has to return a function)
                      (for/fold ([all-ops '()]) ([each-ret arg-rets]) (append all-ops (list (make-var (car each-ret)))))]
                  [letted-exp (recursively-add-lets full-env (Apply (car all-op-atms) (cdr all-op-atms)) (for/list ([each-opd all-op-atms]) (get-symbol-func each-opd)))]          ; wrap the atomic arguments that are not used in the expression, but have been let'ed somewhere in the actual arguments
                                  )
                                  letted-exp                               ; wrap this Apply around lets that define the arguments of this Apply
                            )]
    )
  )
  
  (match p
    [(ProgramDefs info defs)
      (ProgramDefs info (for/list ([def defs]) (match def [(Def fun-name param-list ret-type fun-info fun-body)
                                                            (Def fun-name param-list ret-type fun-info (rco_exp fun-body))])))
    ]
  ))
