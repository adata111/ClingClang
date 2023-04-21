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
 
;; limit-functions : R1 -> R1
(define (limit-functions p)

  (define (limit-functions-exp exp env tup)
    (match exp
      [(Var x) (cond  [(dict-has-key? env x) (let ([tup-index (dict-ref env x)])                          ; check if this Var is a function argument
                                              (if (eq? tup-index -1)                                      ; check if this Var is one of the first 5 arguments
                                                  (Var x)                                                 ; if it is, then leave the reference as it is
                                                  (Prim 'vector-ref (list (Var tup) (Int tup-index)))))]  ; otherwise, replace it with the reference in the 6th vector argument
                      [else (Var x)])]
      [(FunRef x n) (cond  [(dict-has-key? env x) (let ([tup-index (dict-ref env x)])                     ; similar as the case for Var, except it is for FunRef
                                              (if (eq? tup-index -1)
                                                  (FunRef x n)
                                                  (Prim 'vector-ref (list (Var tup) (Int tup-index)))))]
                      [else (FunRef x n)])]
      [(HasType e T) (HasType (limit-functions-exp e env tup) T)]
      [(Let x e letbody) (Let x (limit-functions-exp e env tup) (limit-functions-exp letbody env tup))]
      [(If cnd e1 e2) (If (limit-functions-exp cnd env tup) (limit-functions-exp e1 env tup) (limit-functions-exp e2 env tup))]
      [(Prim op args) (Prim op (for/list ([arg args]) (limit-functions-exp arg env tup)))]
      [(Apply fun-exp arg-exps)
        (let* ( [new-fun-exp (limit-functions-exp fun-exp env tup)]                                       ; the Apply function expression could use any of the function arguments too
                [new-arg-exps (for/list ([arg arg-exps]) (limit-functions-exp arg env tup))])
              (cond 
                [(<= (length new-arg-exps) 6)
                    (Apply new-fun-exp new-arg-exps)]
                [else                                                                                     ; if the Apply has more than 6 arguments
                    (let* ( [first-five-args (take new-arg-exps 5)]                                       ; separate the first 5 arguments from the remaining arguments
                            [remaining-args (drop new-arg-exps 5)]
                            [limited-args (append first-five-args (list (Prim 'vector remaining-args)))]) ; construct the list of arguments where the 6th argumet is a vector of the remaining arguments
                          (Apply new-fun-exp limited-args))]))]
      [_ exp]
    )
  )

  (define (limit-functions-internal fun-def)
    (match fun-def
      [(Def fun-name param-list ret-type fun-info fun-body)
        (match param-list
          [(list `[,params : ,param-types] ...)
            (cond
              [(<= (length param-list) 6) (let* ( [sixth-arg-tup ""]                                                            ; there are less than or equal to 6 arguments, there's no tuple needed
                                                  [limit-env (for/fold ([tmp '()]) ([param params]) (dict-set tmp param -1))]   ; map each arugment symbol to -1, since they don't need to be referenced in the 6th tuple argument
                                                  [limited-body (limit-functions-exp fun-body limit-env sixth-arg-tup)])        ; get the updated function-body
                                                (Def fun-name param-list ret-type fun-info limited-body))]
              [else (let* ( [sixth-arg-tup (gensym 'clingclangvec)]                                                             ; name the vector that will be the 6th argument
                            [first-five-params (take params 5)]                                                                 ; take the first 5 parameters from the list of all parameters
                            [remaining-params (drop params 5)]                                                                  ; take the remaining parameters from the list of all parameters
                            [first-five-param-types (take param-types 5)]                                                       ; similarly for the parameter types
                            [remaining-param-types (drop param-types 5)]
                            [new-params (append first-five-params (list sixth-arg-tup))]                                        ; the new parameters are the 5 individual parameters and the tuple
                            [new-param-types (append first-five-param-types (list (append `(Vector) remaining-param-types)))]   ; the 6th parameter type is a Vector of the remaining parameter types
                            [new-param-list (for/fold ([tmp-params '()])                                                        ; create the new param-list for the Def struct
                                                      ([each-param new-params] [each-type new-param-types])
                                                      (append tmp-params (list `[,each-param : ,each-type])))]
                            [limit-env-first-five (for/fold ([tmp '()]) ([each-param first-five-params]) (dict-set tmp each-param -1))] ; map the first 5 arugment symbols to -1, since they don't need to be referenced in the 6th tuple argument
                            [limit-env-full (for/fold ([tmp limit-env-first-five])
                                                      ([each-param remaining-params] [ind-in-tup (in-naturals)])                        ; map the remaining arguments to 1,2,.... which is their index in the 6th tuple argument
                                                      (dict-set tmp each-param ind-in-tup))]
                            [limited-body (limit-functions-exp fun-body limit-env-full sixth-arg-tup)]                                  ; get the update function body
                            )
                          (Def fun-name new-param-list ret-type fun-info limited-body))])]
        )]
    )
  )

  (match p
    [(ProgramDefs info defs)
      (let* ([new-defs (for/list ([def defs]) (limit-functions-internal def))])
        (ProgramDefs info new-defs))])
)

