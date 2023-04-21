(define (add [x : Integer] [y : Integer]) : Integer
    (+ x y))

(let ([vec (vector 1 2 3)]) (add (vector-ref vec 1) (vector-length vec))) ; 5