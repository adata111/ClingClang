(define (makevector [x : Integer] [y : Integer] [z : Integer]) : (Vector Integer Integer Integer)
    (let ([v (vector x y z)])
      v))
(vector-ref (makevector 1 2 3) 1)
