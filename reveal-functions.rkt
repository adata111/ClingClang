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

;; reveal-functions : R1 -> R1
(define (reveal-functions p)        ; Recursively replace all (Var f) references with (FunRef f arity) if the symbol f denotes a function
                                    ; Recurses similar to the shrink pass
  (define (reveal-functions-internal e all-funs)
    (match e
      [(Var x) (cond  [(dict-has-key? all-funs e) (dict-ref all-funs e)]          ; If expression is a symbol, check if it is a function symbol, if yes, then replace it with the FunRef instance from all-funs
                      [else (Var x)])]                                            ; if expression is not a symbol, leave it as is

      [(Let x e letbody) (Let x (reveal-functions-internal e all-funs) (reveal-functions-internal letbody all-funs))]
      [(If cnd e1 e2) (If (reveal-functions-internal cnd all-funs)
                          (reveal-functions-internal e1 all-funs)
                          (reveal-functions-internal e2 all-funs))]
      [(Prim op args)
        (Prim op (for/list ([each-arg args]) (reveal-functions-internal each-arg all-funs)))]

      [(Apply fun-exp arg-exps) (Apply  (reveal-functions-internal fun-exp all-funs)
                                        (for/list ([each-exp arg-exps])
                                                  (reveal-functions-internal each-exp all-funs)))]

      [(Def fun-name param-list ret-type fun-info fun-body)
          (Def fun-name param-list ret-type fun-info (reveal-functions-internal fun-body all-funs))]

      [_ e]
    )
  )

  (match p
    [(ProgramDefs info defs)
      (let* ( [all-fun-names                                                                    ; Get the function name symbols of all functions
                  (for/fold ([fun-names '()]) ([def defs])
                                              (match def [(Def fun-name param-list _ _ _)
                                                          (dict-set fun-names fun-name (FunRef fun-name (length param-list)))]))] ; Calculate (FunRef `function_name` arity) for each (Var `function_name`)
              [new-defs (for/list ([def defs]) (reveal-functions-internal def all-fun-names))]) ; Replace each (Var `function_name`) reference with the (FunRef fun-name) instance
        (ProgramDefs info new-defs))])
)

