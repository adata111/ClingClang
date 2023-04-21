(define (get1 [x : (Vector Integer (Vector Integer))]) : Integer
    (vector-ref (vector-ref x 1) 0))
(if #t (get1 (vector 1 (vector 42))) 0)
