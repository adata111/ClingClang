#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

(define (uniquify-exp env)
  (lambda (e)
    (match e

      [(Var x)                          ; if the expression is a Var struct, find the referenced value of the Var-struct's symbol in the environment
        (dict-ref env x)]

      [(Int n) (Int n)]                 ; if the expression is an Int struct object, just return the same

      [(Let x e body)
        (cond                           ; check if the symbol being defined by Let already has another reference in the environment
        [(dict-has-key? env x)          ; if key already exists in env, make a new symbol for this key and save in environment
            (let ([new-sym (gensym x)])                                                 ; generate new symbol for x
              (let ([new-env (dict-set env x (Var new-sym))])                           ; make a new environment mapping x to Var struct of new-sym
                (Let new-sym ((uniquify-exp new-env) e) ((uniquify-exp new-env) body))  ; recursively uniquify Let exp and body
              ))]

        [else                           ; if key does not exist in env, map this symbol to it's own Var struct
          (let ([new-env (dict-set env x (Var x))])                                     ; add this symbol's Var struct to env to show that it should reference itself
            (Let x ((uniquify-exp new-env) e) ((uniquify-exp new-env) body))            ; recursively uniquify let exp and body
          )]
        )
      ]

      [(Prim op es)                     ; if the expression is an operator and operands, uniquify all operands
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)

  (define (make-var var-change)
    (cond
      [(symbol? var-change) (Var var-change)]
      [else var-change])
    )

  (define (rco_atom exp-to-atom)
    (match exp-to-atom
      [(Int a) (values (Int a) '())]    ; If the expressions are simple already
      [(Var a) (values (Var a) '())]    ; return them as it is with an empty environment


      [(Let x e body)       ; to convert the let into an atomic: (1) assign a tmp to the simplified expression e, (2) make the body an atomic and assign to a variable body-var (3) return the body-var and environment with body-var
        (let-values ([(tmp-body body-env) (rco_atom body)]) (values tmp-body (dict-set body-env x (rco_exp e))))    ; extract the body's symbol and env with let-values and return the body's symbol along with the env with the newly let'ed variable 
      ]

      [(Prim op es) (let* ([prim-atm (gensym "clingclang")] [es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))] ; if it is a primitive, first get the atomic exps of all operands
                            [full-env                                                                           ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops  (list (make-var (car each-ret)))))]
                            )
                          (values prim-atm (dict-set full-env prim-atm (Prim op all-op-atms))))]                ; return the symbol for the entire prim expression along with the environment 
    ))

  (define (get-symbol-func inp-sym)
  (match inp-sym
    [(Var x) (x)]
    [else inp-sym]
  )
  )

  (define (recursively-add-lets env inp-exp)
    (match inp-exp                                            ; if this is an Prim op, add the defintions of the operands from the environment
      [(Prim op es) (for/foldr ([result (Prim op es)])         ; use for/foldr to get the nested Lets for 1/2/more operands, the initial result is the prim as it is, in case no Let's happen
                                ([each-opd es])
                                (match each-opd               ; wrap the result around a Let only if it is a Var symbol
                                  [(Var v)
                                    (cond
                                      [(dict-has-key? env v) (Let v (recursively-add-lets env (dict-ref env v)) result)]
                                      [else result])          ; if this symbol is not in the env, it has already Let'ed before, return the result as it is
                                  ]
                                  [_ result]))
        ]
      [_ inp-exp]
    )
  )

  (define (rco_exp exp-to-exp)
    (match exp-to-exp
      [(Int a) (Int a)]
      [(Var a) (Var a)]
      [(Let x e body) (Let x (rco_exp e) (rco_exp body))]
      ;[(Prim op es) (let* ([es-rets (for/list ([each-e es]) (rco_atom each-e))]
      [(Prim op es) (let* ([es-rets (for/fold ([ret-vals '()]) ([each-e es]) (let-values([(op-sym op-env) (rco_atom each-e)]) (append ret-vals (list (list op-sym op-env)))))]

                            [full-env                                                                         ; combine the environments of the atomicized operands
                                (for/fold ([full-env '()]) ([each-ret es-rets]) (append full-env (cadr each-ret)))]
                            [all-op-atms                                                                      ; get all the atomicized operands
                                (for/fold ([all-ops '()]) ([each-ret es-rets]) (append all-ops  (list (make-var (car each-ret)))))]
                          )
                          (recursively-add-lets full-env (Prim op all-op-atms))                               ; wrap this primitive op es around lets that define the operands of this Prim
                    )]
    )
  )
  
  (match p
    [(Program info body) (Program info (rco_exp body))]
  ))

;; explicate-control : R1 -> C0
(define (explicate-control p)

  (define (explicate_tail e)
    (match e
      [(Var x) (Return (Var x))]
      [(Int n) (Return (Int n))]
      [(Return r) (Return r)]
      [(Let x rhs body) (explicate_assign x rhs (explicate_tail body))]
      [(Prim op es) (Return (Prim op es))]
      [_ e]
    )
  )

  (define (explicate_assign x e cont)
    (match e
      [(Var a) (Seq (Assign (Var x) (Var a)) cont)]
      [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
      [(Prim op es) (Seq (Assign (Var x) e) cont)]
      [(Let y rhs body) (explicate_assign y rhs (explicate_assign x body cont))]
    )
  )

  (match p
    [(Program info body) (CProgram info `((start . ,(explicate_tail body))))])
)


;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)

  (define (atm-to-pseudo-x86 atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
    )
  )

  (define (expr-to-instr-list x expr)               ; convert the expression into x86 instructions and assign it to x
    (match expr
      [(Prim 'read '())                             ; if it is a read operation, call the read_int function, the result of read_int is stored in rax, assign it to x
        (list
          (Callq 'read_int 0)
          (Instr 'movq (list (Reg 'rax) (Var x))) 
        )
      ]
      [(Prim '+ (list arg1 arg2)) 
        (list 
          (Instr 'movq (list (atm-to-pseudo-x86 arg2) (Var x))) 
          (Instr 'addq (list (atm-to-pseudo-x86 arg1) (Var x)))
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
      [(Int n) (list 
          (Instr 'movq (list (Imm n) (Var x)))
        )
      ]
      [(Var a) (list 
          (Instr 'movq (list (Var a) (Var x))) 
        )
      ]

    )
  )

  (define (make-instr stmt)
    (match stmt
      [(Assign (Var x) e) (expr-to-instr-list x e)]           ; every line is just an assignment, convert the expression to x86 code and assign it to x
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
          (Instr 'movq (list (atm-to-pseudo-x86 arg2) (Reg 'rax))) 
          (Instr 'addq (list (atm-to-pseudo-x86 arg1) (Reg 'rax)))
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
    )
  )

  (define (unpack-seq block)
    (match block
      [(Return e)                                                     ; if the entire block is just a single return, make a return x86 instruction for that expression
            (make-ret-instr e)
      ]
      [(Seq first-line tailz)                                         ; if the remaining block is (Seq line (Seq line .....)), convert the line and recursively call unpack-seq on the tail of the block 
        (append (make-instr first-line) (unpack-seq tailz))           ; both make-instr and unpack-seq return a list of the x86 instructions
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
    [_ (set)]
    )
  )

  (define (calc-lbefore instr lafter)
    ;lafter is the set lbefore of the next instruction
    ;returns set for current instr
    ;(printf "Calc before called for instr: ~v  with lafter: ~v\n" instr lafter)
    (let ([read-vars (get-read-vars instr)]
          [write-vars (get-write-vars instr)]
    )
    (set-union (set-subtract lafter write-vars) read-vars)
    )
    
  )

  (define (uncover-live-block-make-list block-body-list)
    ; function that makes the lbefore for first instr in a block, and recursively makes lbefores for subsequent instructions
    ; params: list of remaining instructions
    ; returns: lbefores (a list of sets of live variables) for all remaining instructions
    ; (printf "Recursive uncover-make-list called for ~v\n" (car block-body-list))
    (match block-body-list
        [(list singular-instr) (list (calc-lbefore singular-instr (set)))]          ; if only a single instruction is left, make lbefore for that instr, input lafter is null
        [_ (let ([lafter (uncover-live-block-make-list (cdr block-body-list))])     ; recursively call this function to make the list of sets for all subsequent instructions
                        (append (list (calc-lbefore (car block-body-list) (car lafter))) lafter))] ; get the lbefore of the first instruction with the last prepended lafter, and prepend it to lbefores of subsequent instructions
                ; (append (list (calc-lbefore (car block-body-list) '())) lafter))] ; get the lbefore of the first instruction with the last prepended lafter, and prepend it to lbefores of subsequent instructions

      )
  )

  (define (uncover-live-block-make-info block)
    ; makes the info for each block to have a list of sets of live-after for each instruction
    ; returns {"all-live-after": list(set(live-vars-instr-1), set(live-vars-instr-2), ....)}
    (match block
      [(Block info block-body) (Block (dict-set '() 'all-live-after
                                        (uncover-live-block-make-list block-body))
                                      block-body)]
      ; (for/foldr ([all-live-after '()])
      ; ([each-ins block-body])
      ; (begin (printf "Each ins: ~v\n" each-ins)
      ;       ()))]
    ))
  

  (define (uncover-live-blocks blocks)
    ; uncover-live-blocks adds liveness information to the info of each block in body
    ; TODO take care of jmp instructions - lbefore of jmp should be lbefore of the first instruction of label you jmp to
    (for/fold ([instr-blocks-dict '()])
              ([(label block) (in-dict blocks)])    ; go through each (label, block) in the body
              (dict-set instr-blocks-dict label (uncover-live-block-make-info block) )   ; update the info of every block
              ; (dict-set instr-blocks-dict label (Block (dict-set '() "func" (list (set "oooo"))) block))   ; update the info of every block

    )
  )

  (match p
    [(X86Program info body) (X86Program info (uncover-live-blocks body))]
  )
)

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)

  (define (create-var-stack-dict info)                ; for each variable in locals-types, map it to the offset value from %rbp
    (for/fold ([var-stack-dict '()] [offset 0])
              ([(var var-datatype) (in-dict info)]) 
              (values (dict-set var-stack-dict var (- offset 8)) (- offset 8))))

  (define (format-offset total-offset)                ; calculate the total stack space that should be allocated, aligned to 16 bytes
    (cond 
      [(zero? (remainder (- total-offset) 16)) (- total-offset)]
      [else (+ 8 (- total-offset))]))

  (define (replace-var-with-stack block offset-dict)  ; replace variables in a block with their stack locations by looking up their offsets in offset-dict

    (define (replace-each-arg arg)                    ; if an individual symbol is a variable, find its location on the stack
      (match arg
        [(Var x) (Deref 'rbp (dict-ref offset-dict x))]
        [_ arg]
      )
    )

    (define (replace-exp exp)                         ; for an expression, replace each argument with its stack location if it is a variable
      (match exp
        [(Instr name arg-list) (Instr name (for/list ([each-arg arg-list]) (replace-each-arg each-arg)))]
        [_ exp]
      )
    )

    (match block
      [(Block info block-lines) (Block info (for/list ([line block-lines]) (replace-exp line)))])
  )

  (define (make-x86-var var-stack-dict body-dict)
    (for/fold ([new-body-dict '()])
              ([(label block) (in-dict body-dict)]) 
              (dict-set new-body-dict label (replace-var-with-stack block var-stack-dict))
    )
  )

  (match p
    [(X86Program info body) 
        (let*-values (
          [(var-stack-offsets total-offset) (create-var-stack-dict (dict-ref info 'locals-types))]    ; make a dict of each variable and the offset on the stack
          [(new-info) (dict-set '() 'stack-space (format-offset total-offset))]                       ; add the total stack-space that is needed for all the variables as the only entry in the info of the X86Program
        )
        (X86Program new-info (make-x86-var var-stack-offsets body))   ; replace the variables in the body with the stack offsets
      )]
  )
)


;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)

  (define (make-x86 body-dict)

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
        [_ (list line)]
      )
    )

    (define (patch-block block)                                   ; patch each line with path-line and reconstruct the list of all instructions
      (match block
        [(Block info block-lines) (Block info (
            for/fold ([new-block-lines '()]) ([line block-lines]) (append new-block-lines (patch-line line))))])  ; patch-line returns a list of the (patched) instructions
    )

    (for/fold ([new-body-dict '()])                               ; for each (label, block), patch each block
              ([(label block) (in-dict body-dict)]) 
              (dict-set new-body-dict label (patch-block block))
    )
  )

  (match p
    [(X86Program info body) (X86Program info (make-x86 body))]
  )
)

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  
  (define (make-prelude-conclusion body-dict info)

    (define main-body (Block '() (list                                                        ; update rbp to rsp, move rsp to allocate stack space for all variables, jump to start
                        (Instr 'pushq (list (Reg 'rbp)))
                        (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                        (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                        (Jmp 'start)
                        )))
    (define conclusion-body (Block '() (list                                                  ; move rsp back to the rbp of this frame, get the rbp of previous frame, return
                        (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                        (Instr 'popq (list (Reg 'rbp)))
                        (Retq)
                        )))

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
     ("uniquify", uniquify, interp-Lvar, type-check-Lvar)
     ("remove complex opera*", remove-complex-opera*, interp-Lvar, type-check-Lvar)
     ("explicate control", explicate-control, interp-Cvar, type-check-Cvar)
     ("instruction selection", select-instructions, interp-pseudo-x86-0)
     ("uncover live", uncover-live, interp-pseudo-x86-0)
     ("assign homes", assign-homes, interp-x86-0)
     ("patch instructions", patch-instructions, interp-x86-0)
     ("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
     ))
