(define (add [x : Integer] [y : Integer]) : Integer
    (+ x y))
(define (sub-1 [x : Integer]) : Integer
    (- x 1))
(define (summation [x : Integer]) : Integer
    (add x (summation (sub-1 x)))
)
(summation 5)