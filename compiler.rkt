#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "priority_queue.rkt")
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

(define (shrink p)            ; converts 'and and 'or to `If` statements, recursively calls itself on every other operation

  (define (shrink-body body)
    (match body
      [(Let x e letbody) (Let x (shrink-body e) (shrink-body letbody))]
      [(If cnd e1 e2) (If (shrink-body cnd) (shrink-body e1) (shrink-body e2))]
      [(Prim 'and (list e1 e2)) (If e1 e2 (Bool #f))]
      [(Prim 'or (list e1 e2)) (If e1 (Bool #t) e2)]
      [(Prim op args)
        (Prim op (for/list ([e args]) (shrink-body e)))]
      [_ body]
    )
  )

  (match p
    [(Program info body) (Program info (shrink-body body))])
)


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
    ))

  (define (get-symbol-func inp-sym)
    (match inp-sym
      [(Var x) x]
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
    )
  )
  
  (match p
    [(Program info body) (Program info (rco_exp body))]
  ))

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

  (define (explicate_assign x e cont)
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
            (printf "Start body: ~v\n" start-body)
            full-app-body))
    )])
)

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)

  (define (boolean->integer b)
    (case b
      ((#f) 0)
      ((#t) 1)
    )
  )

  (define (atm-to-pseudo-x86 atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [(Bool b) (Imm (boolean->integer b))]
    )
  )

  (define (expr-to-instr-list x expr)               ; convert the assign expression into x86 instructions and assign it to x
    (match expr
      [(Prim 'read '())                             ; if it is a read operation, call the read_int function, the result of read_int is stored in rax, assign it to x
        (list
          (Callq 'read_int 0)
          (Instr 'movq (list (Reg 'rax) (Var x))) 
        )
      ]
      [(Prim '+ (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Var x))) 
          (Instr 'addq (list (atm-to-pseudo-x86 arg2) (Var x)))
        )
      ]
      [(Prim '- (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Var x))) 
          (Instr 'subq (list (atm-to-pseudo-x86 arg2) (Var x)))
        )
      ]
      [(Prim '- (list arg1)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Var x)))
          (Instr 'negq (list (Var x))) 
        )
      ]
      ; TODO x = (not x)
      [(Prim 'not (list (Var x))) (list
          (Instr 'xorq (list (Imm 1) (Var x)))
        )
      ]
      ; x = (not a)
      [(Prim 'not (list a)) (list
          (Instr 'movq (list a (Var x)))
          (Instr 'xorq (list (Imm 1) (Var x)))
        )
      ]
      [(Prim 'eq? (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'sete (Reg 'al))
          (Instr 'movzbq (list (Reg 'al) (Var x)))
        )
      ]
      
      [(Int n) (list 
          (Instr 'movq (list (Imm n) (Var x)))
        )
      ]
      [(Var a) (list 
          (Instr 'movq (list (Var a) (Var x))) 
        )
      ]
      [(Bool b) (list 
          (Instr 'movq (list (Imm (boolean->integer b)) (Var x)))
        )
      ]
      [(Goto label)(list 
          (Instr Jmp label)
        )
      ]
    )
  )

  (define (ifstmt-to-instr-list stmt)
    (match stmt
      [(IfStmt (Prim 'eq? (list arg1 arg2)) (Goto then-label) (Goto else-label))
        (append
          (list 
            (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
            (JmpIf 'e then-label)
            (Jmp else-label)
          )
        )
      ]
      [(IfStmt (Prim '< (list arg1 arg2)) (Goto then-label) (Goto else-label))
        (append
          (list 
            (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
            (JmpIf 'l then-label)
            (Jmp else-label)
          )
        )
      ]
      [(IfStmt (Prim '<= (list arg1 arg2)) (Goto then-label) (Goto else-label))
        (append
          (list 
            (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
            (JmpIf 'le then-label)
            (Jmp else-label)
          )
        )
      ]
      [(IfStmt (Prim '> (list arg1 arg2)) (Goto then-label) (Goto else-label))
        (append
          (list 
            (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
            (JmpIf 'g then-label)
            (Jmp else-label)
          )
        )
      ]
      [(IfStmt (Prim '>= (list arg1 arg2)) (Goto then-label) (Goto else-label))
        (append
          (list 
            (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
            (JmpIf 'ge then-label)
            (Jmp else-label)
          )
        )
      ]
    )
  )

  (define (make-instr-seq stmt)
    (match stmt
      [(Assign (Var x) e) (expr-to-instr-list x e)]             ; the line is just an assignment, convert the expression to x86 code and assign it to x
      [(IfStmt cnd thn els) (ifstmt-to-instr-list stmt)] ; convert the if statement into x86 code
    )
  )

  (define (make-ret-instr ret-expr)       ; convert the expression to x86, store the return value in %rax, and jump to the conclusion label since the entire block has now ended with this return statement
    (match ret-expr
      [(Prim 'read '()) 
        (list
          (Callq 'read_int 0)
          (Jmp 'conclusion)
        )
      ]
      [(Prim '+ (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax))) 
          (Instr 'addq (list (atm-to-pseudo-x86 arg2) (Reg 'rax)))
          (Jmp 'conclusion)
        )
      ]
      [(Prim '- (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax))) 
          (Instr 'subq (list (atm-to-pseudo-x86 arg2) (Reg 'rax)))
          (Jmp 'conclusion)
        )
      ]
      [(Prim '- (list arg1)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax)))
          (Instr 'negq (list (Reg 'rax))) 
          (Jmp 'conclusion)
        )
      ]
      [(Prim 'not (Var x)) (list
          (Instr 'movq (list (Var x) (Reg 'rax))) 
          (Instr 'xorq (list (Imm 1) (Reg 'rax)))
          (Jmp 'conclusion)
        )
      ]
      [(Int n) 
        (list 
          (Instr 'movq (list (Imm n) (Reg 'rax))) 
          (Jmp 'conclusion)
        )
      ]
      [(Var x) 
        (list 
          (Instr 'movq (list (Var x) (Reg 'rax))) 
          (Jmp 'conclusion)
        )
      ]
      [(Bool b) (list 
          (Instr 'movq (list (Imm (boolean->integer b)) (Reg 'rax)))
          (Jmp 'conclusion)
        )
      ]
    )
  )

  (define (unpack-seq block)                                          ; block is always either just a return statement, a Seq with an assign and a tail, or an IfStmt that has GoTo's to other blocks
    (printf "--------\nEntered unpack seq \n ~v\n++++++++++\n" block)
    (match block
      [(Return e)                                                     ; if the entire (remaining) block is just a single return, make a return x86 instruction for that expression
            (make-ret-instr e)
      ]
      [(Seq first-line tailz)                                         ; if the remaining block is (Seq line (Seq line .....)), convert the line and recursively call unpack-seq on the tail of the block 
        (append (make-instr-seq first-line) (unpack-seq tailz))       ; both make-instr-seq and unpack-seq return a list of the x86 instructions
      ]
      [(IfStmt cnd thn els)
          (begin
          ; (printf "Matched IfStmt in unpack-seq if ~v then goto ~v else goto ~v\n-----\n" cnd thn els)
          (make-instr-seq block))
      ]
    )
  )

  (define (make-pseudo-x86 blocks)
    (for/fold ([instr-blocks-dict '()])
              ([(label block) (in-dict blocks)])    ; go through each (label, block) in the body and converts the blocks from Cvar to pseudo-x86
              (dict-set instr-blocks-dict label (Block '() (unpack-seq block)))
    )
  )

  (match p
    [(CProgram info body) (X86Program info (make-pseudo-x86 body))]
  )
)

(define (uncover-live p)

  (define (is-var-reg? inp-arg)
    (or (Var? inp-arg) (Reg? inp-arg))
  )

  (define (get-read-vars instr)
    (match instr
      [(Instr 'movq (list s d)) (if (is-var-reg? s) (set s) (set))]
      [(Instr 'addq (list s d)) (if (is-var-reg? s) (set s d) (set d))]
      [(Instr 'subq (list s d)) (if (is-var-reg? s) (set s d) (set d))]
      [(Instr 'negq (list s)) (if (is-var-reg? s) (set s) (set))]
      [(Jmp 'conclusion) (set (Reg 'rax) (Reg 'rsp))]
      [_ (set)]
    )
  )

  (define (get-write-vars instr)
    (match instr
      [(Instr instr (list s d)) (set d)]
      [(Instr 'negq (list s)) (if (is-var-reg? s) (set s) (set))]
      [(Jmp 'conclusion) (set)]
      [(Callq call-label arity) (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
      [_ (set)]
    )
  ) ; Duplicated again inside build-interference

  (define (calc-lbefore instr lafter)
    ;lafter is the set lbefore of the next instruction
    ;returns set for current instr
    ; (printf "Calc before called for instr: ~v  with lafter: ~v\n" instr lafter)
    (let ([read-vars (get-read-vars instr)]
          [write-vars (get-write-vars instr)])
          (set-union (set-subtract lafter write-vars) read-vars)))

  (define (uncover-live-block-make-list block-body-list)
    ; function that makes the lbefore for first instr in a block, and recursively makes lbefores for subsequent instructions
    ; params: list of remaining instructions
    ; returns: lbefores (a list of sets of live variables) for all remaining instructions
    (match block-body-list
        [(list singular-instr) (list (calc-lbefore singular-instr (set)))]          ; if only a single instruction is left, make lbefore for that instr, input lafter is null
        [_ (let ([lafter (uncover-live-block-make-list (cdr block-body-list))])     ; recursively call this function to make the list of sets for all subsequent instructions
                        (append (list (calc-lbefore (car block-body-list) (car lafter))) lafter))] ; get the lbefore of the first instruction with the last prepended lafter, and prepend it to lbefores of subsequent instructions

      )
  )

  (define (uncover-live-block-make-info block)
    ; makes the info for each block to have a list of sets of live-after for each instruction
    ; returns {"all-live-after": list(set(live-vars-instr-1), set(live-vars-instr-2), ....)}
    (match block
      [(Block info block-body) (Block (dict-set '() 'all-live-after
                                        (uncover-live-block-make-list block-body))
                                      block-body)]
    ))
  

  (define (uncover-live-blocks blocks)
    ; uncover-live-blocks adds liveness information to the info of each block in body
    ; TODO take care of jmp instructions - lbefore of jmp should be lbefore of the first instruction of label you jmp to
    (for/fold ([instr-blocks-dict '()])
              ([(label block) (in-dict blocks)])    ; go through each (label, block) in the body
              (dict-set instr-blocks-dict label (uncover-live-block-make-info block) )   ; update the info of every block
    )
  )

  (match p
    [(X86Program info body) (X86Program info (uncover-live-blocks body))]
  )
)

(define (build-interference p)

  (define (get-write-vars instr)
    (define (is-var-reg? inp-arg)
      (or (Var? inp-arg) (Reg? inp-arg))
    )
    (match instr
      [(Instr instr (list s d)) (set d)]
      [(Instr 'negq (list s)) (if (is-var-reg? s) (set s) (set))]
      [(Jmp 'conclusion) (set)]
      [(Callq call-label arity) (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
      [_ (set)]
    )
  ) ; Duplicated from uncover-live

  (define (check-add-if-edge-interference instr live-loc interference-graph)
    ; (printf "  Instr: ~v  L-after-elem: ~v\n  ---\n" instr live-loc)
    (match instr
      [(Instr 'movq (list s d))                                                           ; If it is a movq instruction, check for the case when the variable is clashing with itself
                                (if (or (equal? live-loc d) (equal? live-loc s))          ; Check if live location is the same as the source or the destination of the movq instruction
                                    interference-graph                                             ; if it is, then return the interference-graph as it is
                                    (begin (add-edge! interference-graph live-loc d) interference-graph))]  ; else, add an edge between the live location and the destination of movq. add-edge! adds edge imperatively
      [_
          (for/fold ([new-graph interference-graph])                                    ; For every other instruction, add edge between write-set and the live location
                    ([write-loc (get-write-vars instr)])                                ; Iterate through the write-set
                    (if (equal? live-loc write-loc)                                     ; Check if live location is the same as the write-set element instruction
                      new-graph                                                         ; if it is, then return the interference-graph as it is
                      (begin (add-edge! new-graph live-loc write-loc) new-graph)))]     ; else, add an edge between the live location and the write-set lement. add-edge! adds edge imperatively
    ))

  (define (compute-if-edge-interference instr l-after old-graph)
    ; (printf "Instr: ~vL-after: ~v\n---\n" instr l-after)
    (for/fold ([interference-graph old-graph])
              ([l-after-elem l-after])
              (check-add-if-edge-interference instr l-after-elem interference-graph))
  )

  (define (build-inference-graph instrs l-afters old-graph)
    (for/fold ([interference-graph old-graph])
              ([instr instrs] [l-after l-afters])
              (compute-if-edge-interference instr l-after interference-graph))
  )

  (define (build-interference-block block interference-graph)
    (match block
      [(Block info block-body) (build-inference-graph block-body (dict-ref info 'all-live-after) interference-graph)] ; make the inference graph for this particular block with the l-afters of this block
    )
  )

  (define (build-interference-blocks info blocks)

    (dict-set info 'conflicts
      (for/fold ([interference-graph (undirected-graph '())])
                ([(label block) (in-dict blocks)])    ; go through each (label, block) in the body
                (build-interference-block block interference-graph)   ; build the interference graph of the entire program by going through each block
      )
    )
  )

  (match p
    [(X86Program info body) (X86Program (build-interference-blocks info body) body)]
  )
)

(define (allocate-registers p)

  (define (get-lowest-available-color used-colors)          ; finds the lowest available color after getting the colors of all neighboring colored nodes
    (for/first ([i (in-naturals)]                           ; start searching from color 0
                  #:when (not (set-member? used-colors i))) ; stop the for/first loop when a natural number is found that is not a used color
                  i))                                       ; return this color

  (define (propagate-color-to-neighbors vertex new-color neighbors old-adjacent-colors)   ; when a vertex is colored, update the adjacent-colors of all its neighbours
    (for/fold ([adjacent-colors old-adjacent-colors])
              ([neighbor neighbors])
              (dict-set adjacent-colors neighbor
                        (set-union (dict-ref adjacent-colors neighbor) (set new-color)))) ; get the current set of adjacent colors of the neighbour and add the color of the current vertex
  )

  (define (update-pq priority-q vertex neighbors handle-map colors)   ; update the saturation of the vertices in the priority queue
    (for ([neighbor neighbors])
          (if (not (dict-has-key? colors neighbor))                               ; colored neighbors would not be in the priority queue
                (pqueue-decrease-key! priority-q (dict-ref handle-map neighbor))  ; decrease the priority of the neighbour
                neighbor))                                                        ; dummy else condition for the if block
  )

  (define (get-colors-of-neighbors vertex old-graph colors) ; return a set containing the colours of the neighbors of vertex
    (for/fold ([adj-colors (set)])
              ([neighbor (get-neighbors old-graph vertex)])   ; go through each neighbor of the vertex
              (if (dict-has-key? colors neighbor)             ; if the neighbor has a color, add it to the adjacent map of this vertex
                          (set-union adj-colors (set (dict-ref colors neighbor)))
                  adj-colors)))

  (define (initialize-adjacent old-graph vertices self-colors)  ; will return a dictionary where each vertex has the colors of it's neighbors
    (for/fold ([adjacent-map '()])
              ([vertex vertices])    ; go through each vertex to initialize its adjacent map
              (dict-set adjacent-map vertex (get-colors-of-neighbors vertex old-graph self-colors))
    )
  )

  (define (add-to-pq-and-handle-map priority-q handle-map vertex num-adjacent colors)   ; add vertex to the pq, map the handle in the pq to the vertex
    (if (dict-has-key? colors vertex) (values priority-q handle-map)                    ; if this vertex is colored already, do not add anything to the priority-q. Its mostly just going to be the registers that do not get allocated (rax, rsp, etc)
      (let* ([new-handle (pqueue-push! priority-q num-adjacent)]                        ; push this vertex into the priority-q and get the handle
            [new-handle-map (dict-set (dict-set handle-map                              ; set the dict[handle]=vertex and dict[vertex]=handle
                                      new-handle
                                      vertex) vertex new-handle)]
                                      )
            (values priority-q new-handle-map)) ; return values to be unpacked by a let*-values in allocate-registers-blocks where this is called
    )
  )                                  

  (define (initialize-pq vertices adjacent-map colors)
    (for/fold ([priority-q (make-pqueue >)] [handle-map '()])                       ; initialize a priority queue and an empty handle-map
              ([vertex vertices])
              (add-to-pq-and-handle-map priority-q handle-map vertex
                                        (set-count (dict-ref adjacent-map vertex)) colors)) ; calculate the number of colored neighbors to use as the value for the priority queue
  )

  (define (color-graph self-colors old-graph adjacent-colors priority-q handle-map )
    (if (equal? 0 (pqueue-count priority-q)) self-colors                              ; if there are no vertices left in the priority-q, return the color-map as it is
    (let*-values (
            [(num-neighbors vertex-handle) (pqueue-pop-node! priority-q)]                     ; get the handle of most saturated vertex from the priority queue
            [(cur-vertex) (dict-ref handle-map vertex-handle)]                                ; use the handle of the priority queue to find the actual vertex in the handle-map
            [(new-color) (get-lowest-available-color (dict-ref adjacent-colors cur-vertex))]  ; assign the lowest possible color to this variable
            [(new-color-map) (dict-set self-colors cur-vertex new-color)]                     ; make a new color map with the newly assigned color of this variable
            [(new-adjacent-colors) (propagate-color-to-neighbors cur-vertex                   ; rebuild the adjacent-colors map by propagating the color of this node to all of its neighbors
                                                                new-color
                                                                (get-neighbors old-graph cur-vertex) 
                                                                adjacent-colors)]
            [(_) (update-pq priority-q cur-vertex (get-neighbors old-graph cur-vertex) handle-map new-color-map)]  ; update the priority queue to take the new saturation values into account
            )
            (color-graph new-color-map old-graph  ; remove the newly colored vertex from the graph and call color-graph recursively
                          new-adjacent-colors priority-q handle-map))
  ))

  (define (get-used-callee all-callee color-map)                                  ; get all the used callee-saved registers
    (for/fold ([used-callees '()])
              ([(var var-color) (in-dict color-map)])                             ; go through all the entries in color-map, each entry is the var/reg and its color
              (if (and (dict-has-key? all-callee var-color) (> var-color -1) (not (Reg? var)))  ; if this color corresponds to a callee-saved, and the color corresponds to a Reg that can be allocated, and the entry is not the register itself
                  (append used-callees (list (dict-ref all-callee var-color)))                  ; then this is a used callee-saved register
                  used-callees
              )))

  (define (allocate-registers-blocks info old-graph) ; performs the first call to color-graph by initializing the required values
    (let*-values (
            [(callee-saved) (list (cons -5 (Reg 'r15)) (cons -3 (Reg 'rbp)) (cons -2 (Reg 'rsp))
                                    (cons 7 (Reg 'rbx)) (cons 8 (Reg 'r12))
                                    (cons 9 (Reg 'r13)) (cons 10 (Reg 'r14)))]
            [(caller-saved) (list (cons -4 (Reg 'r11)) (cons -1 (Reg 'rax))
                                    (cons 0 (Reg 'rcx)) (cons 1 (Reg 'rdx)) (cons 2 (Reg 'rsi))
                                    (cons 3 (Reg 'rdi)) (cons 4 (Reg 'r8)) (cons 5 (Reg 'r9))
                                    (cons 6 (Reg 'r10)))]
            [(self-colors) (list  (cons (Reg 'r15) -5) (cons (Reg 'r11) -4)
                                    (cons (Reg 'rbp) -3) (cons (Reg 'rsp) -2) (cons (Reg 'rax) -1)
                                    (cons (Reg 'rcx) 0) (cons (Reg 'rdx) 1) (cons (Reg 'rsi) 2)
                                    (cons (Reg 'rdi) 3) (cons (Reg 'r8) 4) (cons (Reg 'r9) 5)
                                    (cons (Reg 'r10) 6) (cons (Reg 'rbx) 7) (cons (Reg 'r12) 8)
                                    (cons (Reg 'r13) 9) (cons (Reg 'r14) 10))]                          ; currently these registers are mapped to colors
            [(adjacent-map) (initialize-adjacent old-graph (get-vertices old-graph) self-colors)]       ; initialize the interfering colors for other variables due to the above registers
            [(priority-q handle-map) (initialize-pq (get-vertices old-graph) adjacent-map self-colors)] ; initialize the priority queue to check the most saturated variables so far
            [(info-colormap) (dict-set info 'color-map (color-graph self-colors
                                                  old-graph
                                                  adjacent-map priority-q handle-map))]
            [(info-callee) (dict-set info-colormap 'used-callee (set->list (list->set (get-used-callee callee-saved (dict-ref info-colormap 'color-map) ))))] ; get the used callee-saved registers and deduplicate the list by converting to a set
          ) info-callee)
  )

  (match p
    [(X86Program info body) (X86Program (allocate-registers-blocks info (dict-ref info 'conflicts)) body)]
  )
)

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)

  (define (create-var-location-dict color-map register-colors num-callee)                 ; for each variable in locals-types, map to either the correct register or a stack location
    (for/fold ([var-loc-dict '()] [offset (* num-callee -8)] [color-to-stack '()])        ; initialize the offset by the stack space used by pushing the callee-saved registers since callee-saved registers are pushed before the variables on the stack
              ([(var var-color) (in-dict color-map)]) 
              (if (dict-has-key? register-colors var-color)                               ; if this is a color that corresponds to a register location
                  (values (dict-set var-loc-dict var (dict-ref register-colors var-color)) offset color-to-stack) ; use the register. Otherwise it is a stack location
                  (if (dict-has-key? color-to-stack var-color)                            ; check if this particular stack location has already been allocated in the offset
                      (values (dict-set var-loc-dict var (Deref 'rbp (dict-ref color-to-stack var-color))) offset color-to-stack) ; if it has already been allocated, use the same stack location by checking in color-to-stack
                      (let ([new-offset (- offset 8)])                                    ; otherwise, allocate space for this stack location to the offset
                          (values (dict-set var-loc-dict var (Deref 'rbp new-offset))
                                  new-offset
                                  (dict-set color-to-stack var-color new-offset))))       ; save to color-to-stack that this stack location has been allocated space
                  )))

  (define (format-offset total-offset num-callee)                ; calculate the total stack space that should be allocated, aligned to 16 bytes. total-offset is negative
    (let 
      ([aligned-offset-tot (cond 
                            [(zero? (remainder (- total-offset) 16)) (- total-offset)]
                            [else (+ 8 (- total-offset))])
        ])
      (- aligned-offset-tot (* 8 num-callee))
    )
  )

  (define (replace-var-with-loc block loc-dict)   ; replace variables in a block with their locations

    (define (replace-each-arg arg)                ; if an individual symbol is a variable, find its location
      (match arg
        [(Var x) (dict-ref loc-dict arg)]
        [_ arg]
      )
    )

    (define (replace-exp exp)                     ; for an expression, replace each argument with its stack location if it is a variable
      (match exp
        [(Instr name arg-list) (Instr name (for/list ([each-arg arg-list]) (replace-each-arg each-arg)))]
        [_ exp]
      )
    )

    (match block
      [(Block info block-lines) (Block info (for/list ([line block-lines]) (replace-exp line)))])
  )

  (define (make-x86-var var-loc-dict body-dict)
    (for/fold ([new-body-dict '()])
              ([(label block) (in-dict body-dict)]) 
              (dict-set new-body-dict label (replace-var-with-loc block var-loc-dict))
    )
  )

  (match p
    [(X86Program info body) 
        (let*-values (
          [(register-colors) (list  (cons -5 (Reg 'r15)) (cons -4 (Reg 'r11))
                                    (cons -3 (Reg 'rbp)) (cons -2 (Reg 'rsp)) (cons -1 (Reg 'rax))
                                    (cons 0 (Reg 'rcx)) (cons 1 (Reg 'rdx)) (cons 2 (Reg 'rsi))
                                    (cons 3 (Reg 'rdi)) (cons 4 (Reg 'r8)) (cons 5 (Reg 'r9))
                                    (cons 6 (Reg 'r10)) (cons 7 (Reg 'rbx)) (cons 8 (Reg 'r12))
                                    (cons 9 (Reg 'r13)) (cons 10 (Reg 'r14)))]                        ; the colors are mapped to these registers
          [(var-locs total-offset temp) (create-var-location-dict (dict-ref info 'color-map) register-colors (length (dict-ref info 'used-callee)))]  ; make a dict of each variable and their locations
          [(new-info) (dict-set info 'stack-space (format-offset total-offset (length (dict-ref info 'used-callee))))]        ; add the total stack-space that is needed for all the variables as an entry in the info of the X86Program
        )
        (X86Program new-info (make-x86-var var-locs body))   ; replace the variables in the body with the locations
      )]
  )
)

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)

  (define (make-x86 body-dict info)

    (define (patch-line line)
      (match line
        [(Instr operator (list (Deref 'rbp offset1) (Deref 'rbp offset2)))                  ; if the instruction operates on two stack locations, add %rax as an intermediate
                          (list
                            (Instr 'movq (list (Deref 'rbp offset1) (Reg 'rax)))
                            (Instr operator (list (Reg 'rax) (Deref 'rbp offset2))))]
        [(Instr operator (list (Imm n) (Deref 'rbp offset))) #:when (> n (expt 2 16))       ; if one of the immediate values is > 2^16, use rax as an intermediate (edge case mentioned in EoC)
          (list (Instr 'movq (list (Imm n) (Reg 'rax)))
                (Instr operator (list (Reg 'rax) (Deref 'rbp offset)))
          )
        ]
        [(Instr 'movq (list (Reg s) (Reg d))) (if (equal? s d) (list) (list line))]         ; if it is a trivial movq, remove this line
        [_ (list line)]
      )
    )

    (define (patch-block block)                                   ; patch each line with path-line and reconstruct the list of all instructions
      (match block
        [(Block info block-lines) (Block '() (                    ; remove the info section of the block
            for/fold ([new-block-lines '()]) ([line block-lines]) (append new-block-lines (patch-line line))))])  ; patch-line returns a list of the (patched) instructions
    )

    (for/fold ([new-body-dict '()])                               ; for each (label, block), patch each block
              ([(label block) (in-dict body-dict)]) 
              (dict-set new-body-dict label (patch-block block))
    )
  )

  (match p
    [(X86Program info body) (X86Program info (make-x86 body info))]
  )
)

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  
  (define (make-prelude-conclusion body-dict info)

    (define push-used-callees                             ; construct the instructions to push all the used callee-saved registers in the prelude
      (for/fold ([push-callee-instrs '()])                               
                ([callee (dict-ref info 'used-callee)]) 
                (append push-callee-instrs (list (Instr 'pushq (list callee))))
      )
    )

    (define pop-used-callees                              ; construct the instructions to pop all the used callee-saved registers in the conclusion
      (for/fold ([pop-callee-instrs '()])                               
                ([callee (dict-ref info 'used-callee)]) 
                (append (list (Instr 'popq (list callee))) pop-callee-instrs)
      )
    )

    (define main-body       (Block '() (append            ; update rbp to rsp, push used callee-saved registers, move rsp to allocate stack space for all variables, jump to start
                                        (list (Instr 'pushq (list (Reg 'rbp))) (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                                        push-used-callees
                                        (list (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))) (Jmp 'start))))
    )

    (define conclusion-body (Block '() (append      ; move rsp back to the rbp of this frame, pop all used callee-saved registers, get the rbp of previous frame, return
                                        (list (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                        pop-used-callees
                                        (list (Instr 'popq (list (Reg 'rbp))) (Retq))))
    )

    (dict-set (dict-set body-dict 'main main-body) 'conclusion conclusion-body )
  )

  (match p
    [(X86Program info body) (X86Program info (make-prelude-conclusion body info))]
  )
)

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
    ("shrink", shrink, interp-Lif, type-check-Lif)
    ("uniquify", uniquify, interp-Lif, type-check-Lif)
    ("remove complex opera*", remove-complex-opera*, interp-Lif, type-check-Lif)
    ("explicate control", explicate-control, interp-Cif, type-check-Cif)
    ("instruction selection", select-instructions, interp-pseudo-x86-0)
    ;  ("uncover live", uncover-live, interp-pseudo-x86-0)
    ;  ("build interference", build-interference, interp-pseudo-x86-0)
    ;  ("allocate registers", allocate-registers, interp-pseudo-x86-0)
    ;  ("assign homes", assign-homes, interp-x86-0)
    ;  ("patch instructions", patch-instructions, interp-x86-0)
    ;  ("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
     ))
