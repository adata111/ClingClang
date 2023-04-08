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

  (define (is-var-reg? inp-arg)
    (or (Var? inp-arg) (Reg? inp-arg))
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