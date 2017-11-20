#lang s-exp "../stlc.rkt"

(define (negate [x Int] -> Int)
  (- 0 x))

(define (+ [x Int] [y Int] -> Int)
  (- x (negate y)))

(define (swap! [v (Vec Int)] [i Int] [j Int] -> Unit)
  (let ([old-v-i (vec-ref v i)])
    (vec-set! v i (vec-ref v j))
    (vec-set! v j old-v-i)))

(define (< [n Int] [m Int] -> Bool)
  (positive? (- m n)))

(define (sort! [v (Vec Int)] -> Unit)
  (letrec ([find-min-index
            (-> Int Int Int)
            (λ ([best Int] [i Int])
              (if (< i (vec-len v))
                  (if (< (vec-ref v i) (vec-ref v best))
                      (find-min-index i (+ i 1))
                      (find-min-index best (+ i 1)))
                  best))]
           [main-loop
            (-> Int Unit)
            (λ ([i Int])
              (if (< i (vec-len v))
                  (let ([j (find-min-index i (+ i 1))])
                    (swap! v i j)
                    (main-loop (+ i 1)))
                  (void)))])
    (main-loop 0)))

(define v (vec 3 2 1))
(sort! v)