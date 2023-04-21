#lang racket

(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "priority_queue.rkt")
(require "interp.rkt")
(require "interp-Lvec.rkt")
(require "type-check-Lvec.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))

;; expose-allocation : R1 -> R1
(define (expose-allocation p)

  (define (expose-allocation-exp e)
    (match e
      [(Let x e body) (Let x (expose-allocation-exp e) (expose-allocation-exp body))]
      [(If cnd e1 e2)
        (If (expose-allocation-exp cnd) (expose-allocation-exp e1) (expose-allocation-exp e2))]
      [(Prim op es)
        (Prim op (for/list ([e es]) (expose-allocation-exp e)))]
      [(Apply fun-name args)
        (Apply (expose-allocation-exp fun-name) (for/list ([arg args]) (expose-allocation-exp arg)))]
      [(HasType v type)
        (begin (printf "vector: ~v\n" v)
          (match v
            [(Prim 'vector es)
              (let* ([vec-inits
                        (for/list ([vec-ele es])
                                (begin (cons (gensym 'vecinit) vec-ele) ))]
                      [vec-length (length es)]
                      [req-bytes (* (+ 1 vec-length) 8)]
                      [vec-name (gensym 'alloc)]
                      [vec-sets (for/foldr ([fin-vec (Var vec-name)])
                                           ([ele-name-exp vec-inits]
                                            [vec-ind (in-range vec-length)])
                                           (set! fin-vec (Let (gensym '_)
                                                  (Prim 'vector-set! (list (Var vec-name) (Int vec-ind) (Var (car ele-name-exp)))) fin-vec))
                                  fin-vec)]
                      [allocate-vec (Let vec-name (Allocate vec-length type) vec-sets)]
                      [collect-space (Let (gensym '_)
                                      (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int req-bytes)))
                                                          (GlobalValue 'fromspace_end)))
                                          (Void)
                                          (Collect req-bytes)) allocate-vec)]
                    )
                    (begin
                      ; (printf "vector inits ~v\n" vec-inits)
                      ; (printf "vector length ~v\n" vec-length)
                      ; (printf "vector sets ~v\n" vec-sets)
                      ; (printf "allocate vector ~v\n" allocate-vec)
                      (for/foldr ([fin-exp collect-space])
                                           ([ele-name-exp vec-inits])
                                           (set! fin-exp (Let (car ele-name-exp)
                                                              (expose-allocation-exp (cdr ele-name-exp)) fin-exp))
                                  fin-exp)
                    )


            )
            ]
          )
        )
      ]
      [_ e]
    )
  )

  (define (expose-allocation-each-function fun-def all-fun-names)                                    ; Uniquifies the parameter list and the body of the given function to not have a local variable with the same name as some other function
    (match fun-def
      [(Def fun-name param-list ret-type fun-info fun-body)
        (let* ( [new-fun-body (expose-allocation-exp fun-body)])               ; Replace the variables in the body of the function by looking at the new environment (if any of those variables are other function names)
              (Def fun-name param-list ret-type fun-info new-fun-body))]
    )
  )

  (match p
    [(ProgramDefs info defs) (let* ([all-fun-names                                                                    ; Get the function name symbols of all functions
                                      (for/fold ([fun-names '()]) ([def defs])                                        ; Go through each function definition and store the function name as a Var
                                                                  (match def [(Def fun-name _ _ _ _)
                                                                              (dict-set fun-names fun-name (Var fun-name))]))]
                                    [new-defs (for/list ([def defs]) (expose-allocation-each-function def all-fun-names))])    ; Replace other occurrences of these function names in the parameter list or in the body of other functions
                            (ProgramDefs info new-defs))])
)

