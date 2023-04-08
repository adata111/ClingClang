#lang racket

(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "priority_queue.rkt")
(require "interp.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")
(require "utilities.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))

(define (allocate-registers p)

  (define (get-lowest-available-color used-colors)          ; finds the lowest available color after getting the colors of all neighboring colored nodes
    (for/first ([i (in-naturals)]                           ; start searching from color 0
                  #:when (not (set-member? used-colors i))) ; stop the for/first loop when a natural number is found that is not a used color
                  i))                                       ; return this color

  (define (propagate-color-to-neighbors vertex new-color neighbors old-adjacent-colors)   ; when a vertex is colored, update the adjacent-colors of all its neighbours
    (for/fold ([adjacent-colors old-adjacent-colors])
              ([neighbor neighbors])
              (dict-set adjacent-colors neighbor
                        (set-union (dict-ref adjacent-colors neighbor) (set new-color)))) ; get the current set of adjacent colors of the neighbour and add the color of the current vertex
  )

  (define (update-pq priority-q vertex neighbors handle-map colors)   ; update the saturation of the vertices in the priority queue
    (for ([neighbor neighbors])
          (if (not (dict-has-key? colors neighbor))                               ; colored neighbors would not be in the priority queue
                (pqueue-decrease-key! priority-q (dict-ref handle-map neighbor))  ; decrease the priority of the neighbour
                neighbor))                                                        ; dummy else condition for the if block
  )

  (define (get-colors-of-neighbors vertex old-graph colors) ; return a set containing the colours of the neighbors of vertex
    (for/fold ([adj-colors (set)])
              ([neighbor (get-neighbors old-graph vertex)])   ; go through each neighbor of the vertex
              (if (dict-has-key? colors neighbor)             ; if the neighbor has a color, add it to the adjacent map of this vertex
                          (set-union adj-colors (set (dict-ref colors neighbor)))
                  adj-colors)))

  (define (initialize-adjacent old-graph vertices self-colors)  ; will return a dictionary where each vertex has the colors of it's neighbors
    (for/fold ([adjacent-map '()])
              ([vertex vertices])    ; go through each vertex to initialize its adjacent map
              (dict-set adjacent-map vertex (get-colors-of-neighbors vertex old-graph self-colors))
    )
  )

  (define (add-to-pq-and-handle-map priority-q handle-map vertex num-adjacent colors)   ; add vertex to the pq, map the handle in the pq to the vertex
    (if (dict-has-key? colors vertex) (values priority-q handle-map)                    ; if this vertex is colored already, do not add anything to the priority-q. Its mostly just going to be the registers that do not get allocated (rax, rsp, etc)
      (let* ([new-handle (pqueue-push! priority-q num-adjacent)]                        ; push this vertex into the priority-q and get the handle
            [new-handle-map (dict-set (dict-set handle-map                              ; set the dict[handle]=vertex and dict[vertex]=handle
                                      new-handle
                                      vertex) vertex new-handle)]
                                      )
            (values priority-q new-handle-map)) ; return values to be unpacked by a let*-values in allocate-registers-blocks where this is called
    )
  )                                  

  (define (initialize-pq vertices adjacent-map colors)
    (for/fold ([priority-q (make-pqueue >)] [handle-map '()])                       ; initialize a priority queue and an empty handle-map
              ([vertex vertices])
              (add-to-pq-and-handle-map priority-q handle-map vertex
                                        (set-count (dict-ref adjacent-map vertex)) colors)) ; calculate the number of colored neighbors to use as the value for the priority queue
  )

  (define (color-graph self-colors old-graph adjacent-colors priority-q handle-map )
    (if (equal? 0 (pqueue-count priority-q)) self-colors                              ; if there are no vertices left in the priority-q, return the color-map as it is
    (let*-values (
            [(num-neighbors vertex-handle) (pqueue-pop-node! priority-q)]                     ; get the handle of most saturated vertex from the priority queue
            [(cur-vertex) (dict-ref handle-map vertex-handle)]                                ; use the handle of the priority queue to find the actual vertex in the handle-map
            [(new-color) (get-lowest-available-color (dict-ref adjacent-colors cur-vertex))]  ; assign the lowest possible color to this variable
            [(new-color-map) (dict-set self-colors cur-vertex new-color)]                     ; make a new color map with the newly assigned color of this variable
            [(new-adjacent-colors) (propagate-color-to-neighbors cur-vertex                   ; rebuild the adjacent-colors map by propagating the color of this node to all of its neighbors
                                                                new-color
                                                                (get-neighbors old-graph cur-vertex) 
                                                                adjacent-colors)]
            [(_) (update-pq priority-q cur-vertex (get-neighbors old-graph cur-vertex) handle-map new-color-map)]  ; update the priority queue to take the new saturation values into account
            )
            (color-graph new-color-map old-graph  ; remove the newly colored vertex from the graph and call color-graph recursively
                          new-adjacent-colors priority-q handle-map))
  ))

  (define (get-used-callee all-callee color-map)                                  ; get all the used callee-saved registers
    (for/fold ([used-callees '()])
              ([(var var-color) (in-dict color-map)])                             ; go through all the entries in color-map, each entry is the var/reg and its color
              (if (and (dict-has-key? all-callee var-color) (> var-color -1) (not (Reg? var)))  ; if this color corresponds to a callee-saved, and the color corresponds to a Reg that can be allocated, and the entry is not the register itself
                  (append used-callees (list (dict-ref all-callee var-color)))                  ; then this is a used callee-saved register
                  used-callees
              )))

  (define (allocate-registers-blocks info old-graph) ; performs the first call to color-graph by initializing the required values
    (let*-values (
            [(callee-saved) (list (cons -5 (Reg 'r15)) (cons -3 (Reg 'rbp)) (cons -2 (Reg 'rsp))
                                    (cons 7 (Reg 'rbx)) (cons 8 (Reg 'r12))
                                    (cons 9 (Reg 'r13)) (cons 10 (Reg 'r14)))]
            [(caller-saved) (list (cons -4 (Reg 'r11)) (cons -1 (Reg 'rax))
                                    (cons 0 (Reg 'rcx)) (cons 1 (Reg 'rdx)) (cons 2 (Reg 'rsi))
                                    (cons 3 (Reg 'rdi)) (cons 4 (Reg 'r8)) (cons 5 (Reg 'r9))
                                    (cons 6 (Reg 'r10)))]
            [(self-colors) (list  (cons (Reg 'al) -6) (cons (Reg 'r15) -5) (cons (Reg 'r11) -4)
                                    (cons (Reg 'rbp) -3) (cons (Reg 'rsp) -2) (cons (Reg 'rax) -1)
                                    (cons (Reg 'rcx) 0) (cons (Reg 'rdx) 1) (cons (Reg 'rsi) 2)
                                    (cons (Reg 'rdi) 3) (cons (Reg 'r8) 4) (cons (Reg 'r9) 5)
                                    (cons (Reg 'r10) 6) (cons (Reg 'rbx) 7) (cons (Reg 'r12) 8)
                                    (cons (Reg 'r13) 9) (cons (Reg 'r14) 10))]                          ; currently these registers are mapped to colors
            [(adjacent-map) (initialize-adjacent old-graph (get-vertices old-graph) self-colors)]       ; initialize the interfering colors for other variables due to the above registers
            [(priority-q handle-map) (initialize-pq (get-vertices old-graph) adjacent-map self-colors)] ; initialize the priority queue to check the most saturated variables so far
            [(info-colormap) (dict-set info 'color-map (color-graph self-colors
                                                  old-graph
                                                  adjacent-map priority-q handle-map))]
            [(info-callee) (dict-set info-colormap 'used-callee (set->list (list->set (get-used-callee callee-saved (dict-ref info-colormap 'color-map) ))))] ; get the used callee-saved registers and deduplicate the list by converting to a set
          ) info-callee)
  )

  (match p
    [(X86Program info body) (X86Program (allocate-registers-blocks info (dict-ref info 'conflicts)) body)]
  )
)