#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "priority_queue.rkt")
(require "interp.rkt")
; (require "interp-Lint.rkt")
; (require "interp-Lvar.rkt")
; (require "interp-Cvar.rkt")
; (require "interp-Lif.rkt")
; (require "interp-Cif.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cfun.rkt")
; (require "type-check-Lvar.rkt")
; (require "type-check-Cvar.rkt")
; (require "type-check-Lif.rkt")
; (require "type-check-Cif.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))

(require "shrink.rkt")
(require "uniquify.rkt")
(require "reveal-functions.rkt")
(require "remove-complex-opera.rkt")
(require "explicate-control.rkt")
(require "select-instructions.rkt")
(require "uncover-live.rkt")
(require "build-interference.rkt")
(require "allocate-registers.rkt")
(require "assign-homes.rkt")
(require "patch-instructions.rkt")
(require "prelude-and-conclusion.rkt")

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
     ;; Uncomment the following passes as you finish them.
    ("shrink", shrink, interp-Lfun, type-check-Lfun)
    ("uniquify", uniquify, interp-Lfun, type-check-Lfun)
    ("reveal-functions", reveal-functions, interp-Lfun-prime, type-check-Lfun)
    ("remove complex opera*", remove-complex-opera*, interp-Lfun-prime, type-check-Lfun)
    ("explicate control", explicate-control, interp-Cfun, type-check-Cfun)
    ("instruction selection", select-instructions, interp-pseudo-x86-3)
    ("uncover live", uncover-live, interp-pseudo-x86-3)
    ; ("build interference", build-interference, interp-pseudo-x86-3)
    ; ("allocate registers", allocate-registers, interp-pseudo-x86-3)
    ; ("assign homes", assign-homes, interp-x86-3)
    ; ("patch instructions", patch-instructions, interp-x86-3)
    ; ("prelude and conclusion", prelude-and-conclusion, interp-x86-3)
     ))



; (define file "tests/fun_test_7.rkt")
; (define ast (read-program file))

; (debug-level 1)
; (AST-output-syntax 'concrete-syntax)

; (define (opt passes ast)
;   (pretty-print ast)
;   (match passes
;     ['() ast]
;     [(list (list name fun interp type-check) more ...)
;      (println (string-append "Applying " name))
;      (opt more (type-check (fun ast)))]
;     [(list (list name fun interp) more ...)
;      (println (string-append "Applying " name))
;      (opt more (fun ast))]
;     [(list (list name fun) more ...)
;      (println (string-append "Applying " name))
;      (opt more (fun ast))]))

; (define final (opt compiler-passes ast))

