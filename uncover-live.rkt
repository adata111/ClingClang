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

(define (uncover-live p)

  (define label->live (dict-set '() 'conclusion (set (Reg 'rax) (Reg 'rsp))))         ; lbefore of the conclusion is %rax and %rsp

  (define arg-regs (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8) (Reg 'r9)))

  (define (is-var-reg? inp-arg)
    (or (Var? inp-arg) (Reg? inp-arg))
  )

  (define (get-read-vars instr)
    (match instr
      [(Instr 'movq (list s d)) (if (is-var-reg? s) (set s) (set))]
      [(Instr 'addq (list s d)) (if (is-var-reg? s) (set s d) (set d))]
      [(Instr 'subq (list s d)) (if (is-var-reg? s) (set s d) (set d))]
      [(Instr 'negq (list s)) (if (is-var-reg? s) (set s) (set))]
      [(Instr 'cmpq (list a b)) (if (is-var-reg? a) (if (is-var-reg? b) (set a b) (set a)) (if (is-var-reg? b) (set b) (set)))]
      [(Instr 'set (list cc d)) (set)]
      [(Instr 'movzbq (list s d)) (if (is-var-reg? s) (set s) (set))]
      [(Instr 'xorq (list imm sd)) (if (is-var-reg? sd) (set sd) (set))]
      [(Jmp label) (dict-ref label->live label)]
      [(JmpIf cc label) (dict-ref label->live label)]
      [(Callq fun-name n)         (list->set (take arg-regs n))]
      [(IndirectCallq fun-name n) (list->set (take arg-regs n))]
      [(TailJmp fun-name n)       (list->set (take arg-regs n))]
      [_ (set)]
    )
  )

  (define (get-write-vars instr)
    (match instr
      [(Instr instr (list s d)) (set d)]
      [(Instr 'negq (list s)) (if (is-var-reg? s) (set s) (set))]
      [(Jmp 'conclusion) (set)]
      [(Instr 'cmpq (list a b)) (set)]
      [(Instr 'set (list cc d)) (if (is-var-reg? d) (set d) (set))]
      [(Instr 'movzbq (list s d)) (if (is-var-reg? d) (set d) (set))]
      [(Instr 'xorq (list imm sd)) (if (is-var-reg? sd) (set sd) (set))]
      [(Callq call-label arity)       (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
      [(IndirectCallq fun-name arity) (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
      [(TailJmp call-label arity)     (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
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

          ; TODO for JmpIf, do set-union

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

  (define (get-connected-blocks block)                                                ; finds all the other blocks that this block connects to
    (match block
      [(Block info block-body)
                (for/fold   ([outgoing-block-conns '()])
                            ([each-ins block-body])
                            (match each-ins                                           ; for each instruction in this block, any JmpIf
                              [(JmpIf cc label) (cons label outgoing-block-conns)]    ; of Jmp instruction denotes that this block connects to some other block
                              [(Jmp label) (cons label outgoing-block-conns)]
                              ; [(TailJmp label arity) (cons label outgoing-block-conns)]
                              [_ outgoing-block-conns]))
      ])
  )

  (define (uncover-live-block-make-info-cfg tsorted-cfg label block)
    ; makes the info for each block to have a list of sets of live-after for each instruction
    ; returns {"all-live-after": list(set(live-vars-instr-1), set(live-vars-instr-2), ....)}
    (match block
      [(Block info block-body)  (let ([live-vars-list (uncover-live-block-make-list block-body)])
                                      (begin
                                        (printf "uncover-live-block-make-info-cfg: ~v\n" label)
                                        (set! label->live (dict-set label->live label (car live-vars-list)))
                                        (Block (dict-set '() 'all-live-after live-vars-list) block-body)))]
    )  
  )

  (define (make-cfg-and-uncover-live def)                         ; makes the control flow graph of all the blocks in the function
    (match def [(Def fun-name param-list ret-type fun-info fun-body) 
      (Def fun-name param-list ret-type fun-info
        (let* ([edge-list
                (for/fold ([edge-list '()])             ; start with an initial empty edge list between all blocks in the program
                  ([(label block) (in-dict fun-body)])    ; go through each (label, block) in the body
                  (append edge-list (for/list ([each-connected-block (get-connected-blocks block)]) (list label each-connected-block)))   ; get the outgoing edges from every block, add the tuple of (label,outgoing_block) to the edge list
                )]
              [cfg (make-multigraph edge-list)]
              [transposed-cfg (transpose cfg)]
              [tsorted-cfg (tsort transposed-cfg)]
              [_ (set! label->live (dict-set label->live (symbol-append fun-name 'conclusion) (set (Reg 'rax) (Reg 'rsp)) ))]
              [tsorted-cfg-without-conclusion (remove (symbol-append fun-name 'conclusion) tsorted-cfg)]
              [blocks-to-go-through (append tsorted-cfg-without-conclusion (set->list (set-subtract
                                                                                            (list->set (dict-keys fun-body))
                                                                                            (list->set tsorted-cfg-without-conclusion))))]  ; The blocks that are not in the tsorted graph should also be uncovered
              [uncovered-blocks (for/fold ([instr-blocks-dict '()])
                                          ([label blocks-to-go-through])    ; go through each label in the top-sorted order except the conclusion block
                                          (dict-set instr-blocks-dict label (uncover-live-block-make-info-cfg tsorted-cfg label (dict-ref fun-body label)))   ; update the info of every block
                )]
              )
        ; (printf "Edge-list: ~v\n----\n" edge-list)
        ; (printf "Multigraph: ~v\n" (get-vertices cfg))
        ; (printf "Multigraph: ~v\n---\n" (for/list ([vertex (in-vertices cfg)]) (get-neighbors cfg vertex)))
        ; (printf "Transposed Multigraph: ~v\n---\n" (get-vertices transposed-cfg))
        ; (printf "Transposed Multigraph: ~v\n---\n" (for/list ([vertex (in-vertices transposed-cfg)]) (get-neighbors transposed-cfg vertex)))
        ; (printf "Tsorted transposed multigraph: ~v\n----\n" tsorted-cfg)
        ; (printf "Label->live: ~v\n----\n" label->live)
        ; (printf "blocks-to-go-through: ~v\n----\n" blocks-to-go-through)
        uncovered-blocks
      ))]
    )
  )

  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (make-cfg-and-uncover-live def)))]
  )

)