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

(define (build-interference p)

  (define (loc-ptr? loc locals-types)
    (match loc
      [(Var x) (match (dict-ref locals-types x)
                      [`(Vector ,types ...) #t]
                      [_ #f]
      )]
      [_ #f]
    )
  ) ; duplicated in allocate-registers.rkt

  (define (is-var-reg? inp-arg)
    (or (Var? inp-arg) (Reg? inp-arg))
  )

  (define (get-write-vars instr live-loc locals-types)
    (match instr
      [(Instr instr (list s d)) (set d)]
      [(Instr 'negq (list s)) (if (is-var-reg? s) (set s) (set))]
      [(Jmp 'conclusion) (set)]
      [(Instr 'cmpq (list a b)) (set)]
      [(Instr 'set (list cc d)) (if (is-var-reg? d) (set d) (set))]
      [(Instr 'movzbq (list s d)) (if (is-var-reg? d) (set d) (set))]
      [(Instr 'xorq (list imm sd)) (if (is-var-reg? sd) (set sd) (set))]

      [(Callq call-label arity)       (if (loc-ptr? live-loc locals-types) 
                                          (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))
                                          (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)
                                              (Reg 'r15) (Reg 'rbp) (Reg 'rsp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))]
      [(IndirectCallq fun-name arity) (if (loc-ptr? live-loc locals-types) 
                                          (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))
                                          (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)
                                              (Reg 'r15) (Reg 'rbp) (Reg 'rsp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))]


      [(TailJmp call-label arity)     (set (Reg 'rax) (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11))]
      [_ (set)]
    )
  ) ; Duplicated from uncover-live

  (define (check-add-if-edge-interference instr live-loc interference-graph locals-types)
    ; (printf "  Instr: ~v  L-after-elem: ~v\n  ---\n" instr live-loc)
    (match instr
      [(Instr 'movq (list s d))                                                           ; If it is a movq instruction, check for the case when the variable is clashing with itself
                                (if (or (equal? live-loc d) (equal? live-loc s))          ; Check if live location is the same as the source or the destination of the movq instruction
                                    interference-graph                                             ; if it is, then return the interference-graph as it is
                                    (begin (add-edge! interference-graph live-loc d) interference-graph))]  ; else, add an edge between the live location and the destination of movq. add-edge! adds edge imperatively
      [_
          (for/fold ([new-graph interference-graph])                                    ; For every other instruction, add edge between write-set and the live location
                    ([write-loc (get-write-vars instr live-loc locals-types)])                                ; Iterate through the write-set
                    (if (equal? live-loc write-loc)                                     ; Check if live location is the same as the write-set element instruction
                      new-graph                                                         ; if it is, then return the interference-graph as it is
                      (begin (add-edge! new-graph live-loc write-loc) new-graph)))]     ; else, add an edge between the live location and the write-set lement. add-edge! adds edge imperatively
    ))

  (define (compute-if-edge-interference instr l-after old-graph locals-types)
    ; (printf "Instr: ~vL-after: ~v\n---\n" instr l-after)
    (for/fold ([interference-graph old-graph])
              ([l-after-elem l-after])
              (check-add-if-edge-interference instr l-after-elem interference-graph locals-types))
  )

  (define (build-inference-graph instrs l-afters old-graph locals-types)
    (for/fold ([interference-graph old-graph])
              ([instr instrs] [l-after l-afters])
              (compute-if-edge-interference instr l-after interference-graph locals-types))
  )

  (define (build-interference-block block interference-graph locals-types)
    (match block
      [(Block info block-body) (build-inference-graph block-body (dict-ref info 'all-live-after) interference-graph locals-types)] ; make the inference graph for this particular block with the l-afters of this block
    )
  )

  (define (build-interference-def def)
    (match def
      [(Def fun-name param-list ret-type fun-info fun-body)
        (let* ( [fun-locals (dict-ref fun-info 'locals-types)]
                [new-fun-info (dict-set fun-info 'conflicts
                                                      (for/fold ([interference-graph (undirected-graph '())])
                                                                ([(label block) (in-dict fun-body)])    ; go through each (label, block) in the body
                                                                (build-interference-block block interference-graph fun-locals)   ; build the interference graph of the entire program by going through each block
                                                      )
                        )])
              (Def fun-name param-list ret-type new-fun-info fun-body))]
    )
  )

  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (build-interference-def def)))]
  )

)