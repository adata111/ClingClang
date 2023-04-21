(define (retVec [x : Boolean] [y : Boolean]) : (Vector Boolean Boolean)
    (vector x y))

(if (vector-ref (retVec #t #f) 1) 0 42)