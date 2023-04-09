(define (add [x : Integer] [y : Integer]) : Integer
    (+ x y))
(define (sub [add : Integer] [y : Integer]) : Integer
    (- add y))
(define (choose-add-sub [c : Boolean]) : (Integer Integer -> Integer)
    (if c add sub))
((choose-add-sub #t) 5 4)