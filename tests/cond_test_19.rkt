(let ([x 4])
    (+ (if (let ([x (and (eq? (read) x) (> 5 3))])
            (and (not x) #t))
        (+ 3 5)
        (- 24))
        (if (or (< 5 7) (>= 4 4))
            (let ([y (read)]) (- y))
            7))
)