(define (add [x : Integer] [y : Integer]) : Integer
    (+ x y))
(define (sub [add : Integer] [y : Integer]) : Integer
    (- add y))
(define (chooseaddsub [c : Boolean]) : (Integer Integer -> Integer)
    (if c add sub))
((chooseaddsub #t) 5 37)