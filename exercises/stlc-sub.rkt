#lang s-exp nu-type-systems/turnstile/stlc-sub

(define (+/Num [n Num] [m Num] -> Num)
  (-/Num n (-/Num 0 m)))

(define (+/Float [n Float] [m Float] -> Float)
  (-/Float n (-/Float 0.0 m)))

(define (+/Int [n Int] [m Int] -> Int)
  (-/Int n (-/Int 0 m)))

(define (</Int [n Int] [m Int] -> Bool)
  (positive? (-/Int m n)))

(define (swap! [v (Vec Int)] [i Int] [j Int] -> Unit)
  (let ([old-v-i (vec-ref v i)])
    (vec-set! v i (vec-ref v j))
    (vec-set! v j old-v-i)))

(define (sort! [v (Vec Int)] -> Unit)
  (letrec ([find-min-index
            (-> Int Int Int)
            (λ ([best Int] [i Int])
              (if (</Int i (vec-len v))
                  (if (</Int (vec-ref v i) (vec-ref v best))
                      (find-min-index i (+/Int i 1))
                      (find-min-index best (+/Int i 1)))
                  best))]
           [main-loop
            (-> Int Unit)
            (λ ([i Int])
              (if (</Int i (vec-len v))
                  (let ([j (find-min-index i (+/Int i 1))])
                    (swap! v i j)
                    (main-loop (+/Int i 1)))
                  (void)))])
    (main-loop 0)))

(define v (vec 4 3 1 2))
(sort! v)
v