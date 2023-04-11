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

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)

  (define arg-regs (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))

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
      [(Prim 'not (list arg1)) (list
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Var x)))
          (Instr 'xorq (list (Imm 1) (Var x)))
        )
      ]
      [(Prim 'eq? (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'e (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Var x)))
        )
      ]
      [(Prim '< (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'l (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Var x)))
        )
      ]
      [(Prim '<= (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'le (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Var x)))
        )
      ]
      [(Prim '> (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'g (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Var x)))
        )
      ]
      [(Prim '>= (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'ge (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Var x)))
        )
      ]
      [(Call fun-name args)
        (let ([fun-arg-ins (for/list ([arg args] [reg arg-regs]) (Instr 'movq (list (atm-to-pseudo-x86 arg) reg)))])
          (append fun-arg-ins (list ; (TailJmp fun-name (length args))
                                    (IndirectCallq fun-name (length args))
                                    (Instr 'movq (list (Reg 'rax) (Var x))))))
      ]
      [(Int n) (list 
          (Instr 'movq (list (Imm n) (Var x)))
        )
      ]
      [(Var a) (list 
          (Instr 'movq (list (Var a) (Var x))) 
        )
      ]
      [(FunRef a n) (list 
          (Instr 'leaq (list (Global a) (Var x))) 
        )
      ]
      [(Bool b) (list 
          (Instr 'movq (list (Imm (boolean->integer b)) (Var x)))
        )
      ]
      [(Goto label) (list (Jmp label))]
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

  (define (make-ret-instr ret-expr conclusion-label)       ; convert the expression to x86, store the return value in %rax, and jump to the conclusion label since the entire block has now ended with this return statement
    (match ret-expr
      [(Prim 'read '()) 
        (list
          (Callq 'read_int 0)
          (Jmp conclusion-label)
        )
      ]
      [(Prim '+ (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax))) 
          (Instr 'addq (list (atm-to-pseudo-x86 arg2) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim '- (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax))) 
          (Instr 'subq (list (atm-to-pseudo-x86 arg2) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim '- (list arg1)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax)))
          (Instr 'negq (list (Reg 'rax))) 
          (Jmp conclusion-label)
        )
      ]
      ; TODO x = (not x)
      [(Prim 'not (list (Var x))) (list
          (Instr 'xorq (list (Imm 1) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      ; x = (not a)
      [(Prim 'not (list arg1)) (list
          (Instr 'movq (list (atm-to-pseudo-x86 arg1) (Reg 'rax)))
          (Instr 'xorq (list (Imm 1) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim 'eq? (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'e (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim '< (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'l (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim '<= (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'le (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim '> (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'g (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Prim '>= (list arg1 arg2)) (list
          (Instr 'cmpq (list (atm-to-pseudo-x86 arg2) (atm-to-pseudo-x86 arg1)))
          (Instr 'set (list 'ge (Reg 'al)))
          (Instr 'movzbq (list (Reg 'al) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
      [(Int n) 
        (list 
          (Instr 'movq (list (Imm n) (Reg 'rax))) 
          (Jmp conclusion-label)
        )
      ]
      [(Var x) 
        (list 
          (Instr 'movq (list (Var x) (Reg 'rax))) 
          (Jmp conclusion-label)
        )
      ]
      [(FunRef a n) (list 
          (Instr 'leaq (list (Global a) (Reg 'rax))) 
          (Jmp conclusion-label)
        )
      ]
      [(Bool b) (list 
          (Instr 'movq (list (Imm (boolean->integer b)) (Reg 'rax)))
          (Jmp conclusion-label)
        )
      ]
    )
  )

  (define (unpack-seq fun-name block)                                          ; block is always either just a return statement, a Seq with an assign and a tail, or an IfStmt that has GoTo's to other blocks
    ; (printf "--------\nEntered unpack seq \n ~v\n++++++++++\n" block)
    (match block
      [(Return e)                                                     ; if the entire (remaining) block is just a single return, make a return x86 instruction for that expression
            (make-ret-instr e (symbol-append fun-name 'conclusion))
      ]
      [(Seq first-line tailz)    
          (begin
          ; (printf "Matched seq in unpack-seq first line ~v \ntails ~v\n-----\n" first-line tailz)                                     ; if the remaining block is (Seq line (Seq line .....)), convert the line and recursively call unpack-seq on the tail of the block 
          (append (make-instr-seq first-line) (unpack-seq fun-name tailz))       ; both make-instr-seq and unpack-seq return a list of the x86 instructions
          )
      ]
      [(IfStmt cnd thn els)
          (begin
          ; (printf "Matched IfStmt in unpack-seq if ~v then goto ~v else goto ~v\n-----\n" cnd thn els)
          (make-instr-seq block))
      ]
      [(Goto label)                                                     ; if the entire (remaining) block is just a single Goto, make a jump x86 instruction for that label
            (list (Jmp label))
      ]
      [(TailCall fun-name args)      
        (let ([fun-arg-ins (for/list ([arg args] [reg arg-regs]) (Instr 'movq (list (atm-to-pseudo-x86 arg) reg)))])
          (append fun-arg-ins (list (TailJmp fun-name (length args)))))
      ]
    )
  )

  (define (select-instructions-def def)
    (match def
    [(Def fun-name (list `[,params : ,param-types] ...) ret-type fun-info fun-body)
      (let* ( [pseudo-x86-blocks (for/fold  ([instr-blocks-dict '()])
                                            ([(label block) (in-dict fun-body)])
                                            (dict-set instr-blocks-dict label (Block '() (unpack-seq fun-name block))))
              ]
              [load-function-arguments (for/list  ([arg params] [reg arg-regs])
                                                  (Instr 'movq (list reg (Var arg))))]
              [start-block (match (dict-ref pseudo-x86-blocks (symbol-append fun-name 'start))
                                  [(Block info body) (Block info (append load-function-arguments body))])]
              [final-pseudo-x86-blocks (dict-set pseudo-x86-blocks (symbol-append fun-name 'start) start-block)]
              [pseudo-fun-info-params (dict-set fun-info 'num-params (length params))]
              [pseudo-fun-info-params-types (dict-set pseudo-fun-info-params 'locals-types (append (dict-ref fun-info 'locals-types) (map cons params param-types)))]
              )
            (Def fun-name '() ret-type pseudo-fun-info-params-types final-pseudo-x86-blocks))]
    )
  )

  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (select-instructions-def def)))]
  )
)
