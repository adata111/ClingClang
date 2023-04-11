(define (add [x : Integer] [y : Integer]) : Integer
    (+ x y))
(define (sub [add : Integer] [y : Integer]) : Integer
    (- add y))
(define (myfun [a : Integer] [b : Integer] [c : Boolean]) : Integer
    (if c (add a b) (sub a b)))
(myfun 4 38 #t) 