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

(define (shrink p)            ; converts 'and and 'or to `If` statements, recursively calls itself on every other operation

  (define (shrink-body body)
    (match body
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool n) (Bool n)]
      [(Void) (Void)]

      [(Let x e letbody) (Let x (shrink-body e) (shrink-body letbody))]
      [(If cnd e1 e2) (If (shrink-body cnd) (shrink-body e1) (shrink-body e2))]
      [(Prim 'and (list e1 e2)) (If e1 e2 (Bool #f))]
      [(Prim 'or (list e1 e2)) (If e1 (Bool #t) e2)]
      [(Prim op args)
        (Prim op (for/list ([e args]) (shrink-body e)))]
      [(HasType e t) (HasType (shrink-body e) t)]
      [(Apply fun-exp arg-exps) (Apply  (shrink-body fun-exp)
                                        (for/list ([each-exp arg-exps])
                                                  (shrink-body each-exp)))]
      ; [_ body]
    )
  )

  (match p
    ; [(Program info body) (Program info (shrink-body body))]

    [(ProgramDefsExp info defs main-exp)
      (let*  ([mainDef (Def 'main '() 'Integer '() main-exp)]
              [all-defs (append defs (list mainDef))]
              [new-defs (for/list ([each-def all-defs])
                                  (match each-def [ (Def fun-name param-list ret-type fun-info fun-body)
                                                    (Def fun-name param-list ret-type fun-info (shrink-body fun-body))]))])
            (ProgramDefs info new-defs))
    ]
    
    )
)