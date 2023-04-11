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
  
  (define (make-prelude-conclusion body-dict info fun-name)

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
                                        (list (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))) (Jmp (symbol-append fun-name 'start)))))
    )

    (define conclusion-body (Block '() (append      ; move rsp back to the rbp of this frame, pop all used callee-saved registers, get the rbp of previous frame, return
                                        (list (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                                        pop-used-callees
                                        (list (Instr 'popq (list (Reg 'rbp))) (Retq))))
    )

    (define (expand-tail-jmp target)                ; expand the tail jump instruction to pop current frame
      (append
        (list (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
        pop-used-callees
        (list (Instr 'popq (list (Reg 'rbp))) (IndirectJmp target)))
    )

    (define (process-block block)                                 ; process each line and change tailjmp instruction
      (match block
        [(Block info block-lines) (Block '() (                    ; remove the info section of the block
            for/fold ([new-block-lines '()]) 
                      ([line block-lines]) 
                      (append new-block-lines (match line
                                          [(TailJmp reg arity) (expand-tail-jmp reg)]
                                          [_ (list line)]))))])  
    )

    (define process-body 
      (for/fold ([new-body-dict '()])                               ; for each (label, block), process each block
              ([(label block) (in-dict body-dict)]) 
              (dict-set new-body-dict label (process-block block))
      )
    )

    
    (dict-set (dict-set process-body fun-name main-body) (symbol-append fun-name 'conclusion) conclusion-body )
  )

  (define (make-prelude-conclusion-def def)
    (match def
      [(Def fun-name param-list ret-type fun-info fun-body)
        (Def fun-name '() ret-type fun-info (make-prelude-conclusion fun-body fun-info fun-name))]
    )
  )

  (match p
    [(ProgramDefs info defs)
     (let ([new-defs (for/list ([d defs]) (make-prelude-conclusion-def d))])
      (X86Program info (append-map Def-body new-defs)))]
  )
)