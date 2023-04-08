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

;; explicate-control : R1 -> C0
(define (explicate-control p)

  (define basic-blocks '())

  (define (create_block tail)       ; tail is already a Seq/Return in Cif
    (match tail
      [(Goto label) (Goto label)]
      [else
        (let  ([label (gensym 'block)])
              (set! basic-blocks (cons (cons label tail) basic-blocks))
              ; (printf "Created ~v for ~v\n---\n" label tail)
              (Goto label))]
    )
  )

  (define (explicate_pred cnd thn els)
    ; (printf "explicate_pred cnd:~v\nthn:~v\nels:~v\n---\n" cnd thn els)
    (let ([thn-block (create_block thn)]
          [els-block (create_block els)])
          (match cnd
            [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) thn-block els-block)]
            [(Let x rhs body) (explicate_assign x rhs (explicate_pred body thn-block els-block))]
            [(Prim 'not (list e)) (explicate_pred e els-block thn-block)]
            [(Prim op es) ;#:when (or (eq? op 'eq?) (eq? op '<))
              (IfStmt (Prim op es) thn-block els-block)]
            [(Bool b) (if b thn-block els-block)]
            [(If cnd^ thn^ els^) (explicate_pred cnd^ (explicate_pred thn^ thn-block els-block) (explicate_pred els^ thn-block els-block))]
            [else (error "explicate_pred unhandled case" cnd)]
          )
    )
  )

  (define (explicate_assign x e cont)                             ; TODO testcase check: (let ([x (not #f)]) (if x 42 0))
    (match e
      [(Var a) (Seq (Assign (Var x) (Var a)) cont)]
      [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
      [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
      [(Prim op es) (Seq (Assign (Var x) e) cont)]
      [(Let y rhs body) (explicate_assign y rhs (explicate_assign x body cont))]
      [(If cnd e1 e2)
                    (let* ( [goto_cont_block (create_block cont)]
                            [then_branch (explicate_assign x e1 goto_cont_block)]
                            [else_branch (explicate_assign x e2 goto_cont_block)])
                          (explicate_pred cnd then_branch else_branch))
      ]
    )
  )

  (define (explicate_tail e)
    (match e
      [(Var x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Bool b) (Return (Bool b))]
      [(Return r) (Return r)]
      [(Let x rhs body) (explicate_assign x rhs (explicate_tail body))]
      [(If cnd e1 e2) (let* ( [then_branch (explicate_tail e1)]
                              [else_branch (explicate_tail e2)])
                            (explicate_pred cnd then_branch else_branch))
      ]
      [(Prim op es) (Return (Prim op es))]
      [_ e]
    )
  )

  (match p
    [(Program info body) (CProgram info
    (let* ( [start-body (explicate_tail body)]
            [full-app-body (cons (cons 'start start-body) basic-blocks)])
          (begin
            ; (printf "Start body: ~v\n" start-body)
            full-app-body))
    )])
)