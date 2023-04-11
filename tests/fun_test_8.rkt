(define (func [x : Integer] [y : Integer] [z : Integer] [a : Integer] [b : Integer] [c : Integer]) : Integer
    (+ c (+ b (+ a (- (+ x y) z))))) ;c + b + a + ((x+y)-z))
(func 40 2 40 10 20 10)