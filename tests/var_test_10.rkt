(let ([x (let([x 5]) (+ 5 x))]) (let ([z 10]) (+ x ( let([x 7]) (+ (+ x z) 1)))))
