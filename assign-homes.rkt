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
      (if (dict-has-key? loc-dict arg)            ; if it exists in the variable-location dictionary
            (match arg
              [(Var x) (dict-ref loc-dict arg)]
              [_ arg]
            )
            arg
      )
    )

    (define (replace-exp exp)                     ; for an expression, replace each argument with its stack location if it is a variable
      (match exp
        [(Instr name arg-list) (Instr name (for/list ([each-arg arg-list]) (replace-each-arg each-arg)))]

        [(Callq fun-name n) (Callq (replace-each-arg fun-name) n)]
        [(IndirectCallq fun-name n) (IndirectCallq (replace-each-arg fun-name) n)]
        [(TailJmp fun-name n) (TailJmp (replace-each-arg fun-name) n)]

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

  (define (assign-homes-def def)
    (match def
      [(Def fun-name param-list ret-type fun-info fun-body)
        (let*-values (
                      [(register-colors) (list (cons -6 (Reg 'al)) (cons -5 (Reg 'r15)) (cons -4 (Reg 'r11))
                                                (cons -3 (Reg 'rbp)) (cons -2 (Reg 'rsp)) (cons -1 (Reg 'rax))
                                                (cons 0 (Reg 'rcx)) (cons 1 (Reg 'rdx)) (cons 2 (Reg 'rsi))
                                                (cons 3 (Reg 'rdi)) (cons 4 (Reg 'r8)) (cons 5 (Reg 'r9))
                                                (cons 6 (Reg 'r10)) (cons 7 (Reg 'rbx)) (cons 8 (Reg 'r12))
                                                (cons 9 (Reg 'r13)) (cons 10 (Reg 'r14)))]                        ; the colors are mapped to these registers
                      [(var-locs total-offset temp) (create-var-location-dict (dict-ref fun-info 'color-map) register-colors (length (dict-ref fun-info 'used-callee)))]  ; make a dict of each variable and their locations
                      [(new-info) (dict-set fun-info 'stack-space (format-offset total-offset (length (dict-ref fun-info 'used-callee))))]        ; add the total stack-space that is needed for all the variables as an entry in the info of the X86Program
                      [(new-body) (make-x86-var var-locs fun-body)]
                    )
              (Def fun-name param-list ret-type fun-info new-body))]
    )
  )

  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (assign-homes-def def)))]
  )
)