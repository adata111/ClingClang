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