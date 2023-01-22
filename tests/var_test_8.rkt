(let ([x
        (let ([x 20])
            (+ x ( let([x 22]) x )))
        ])
    x
)