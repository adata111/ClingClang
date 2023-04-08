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
        [(Instr 'cmpq (list a (Imm b))) (list
                                          (Instr 'movq (list (Imm b) (Reg 'rax)))
                                          (Instr 'cmpq (list a (Reg 'rax))))]
        [(Instr 'movzbq (list s d)) #:when (not (Reg? d))
                                  (list
                                    (Instr 'movq (list d (Reg 'rax)))
                                    (Instr 'movzbq (list s (Reg 'rax))))]
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