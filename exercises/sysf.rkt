#lang s-exp nu-type-systems/turnstile/sysf

(define (negate [x Int] -> Int)
  (- 0 x))

(define (+ [x Int] [y Int] -> Int)
  (- x (negate y)))

(define (< [n Int] [m Int] -> Bool)
  (positive? (- m n)))

(define (= [n Int] [m Int] -> Bool)
  (zero? (- m n)))

;;;; Sorting

(define swap!
  (tyλ (A)
    (λ ([v (Vec A)] [i Int] [j Int])
      (let ([old-v-i ((vec-ref A) v i)])
        ((vec-set! A) v i ((vec-ref A) v j))
        ((vec-set! A) v j old-v-i)))))

(define sort!
  (All (A) (-> (Vec A) (-> A A Bool) Unit))
  (tyλ (A)
    (λ (v lt?)
      (letrec ([find-min-index
                (-> Int Int Int)
                (λ ([best Int] [i Int])
                  (if (< i ((vec-len A) v))
                      (if (lt? ((vec-ref A) v i) ((vec-ref A) v best))
                          (find-min-index i (+ i 1))
                          (find-min-index best (+ i 1)))
                      best))]
               [main-loop
                (-> Int Unit)
                (λ ([i Int])
                  (if (< i ((vec-len A) v))
                      (let ([j (find-min-index i (+ i 1))])
                        ((swap! A) v i j)
                        (main-loop (+ i 1)))
                      (void)))])
        (main-loop 0)))))

(define-type-alias Time (Record [hour Int] [minute Int]))
(define mk-time
  (λ ([h Int] [m Int])
    (record [hour h] [minute m])))

(define (lex< [p1 Time] [p2 Time] -> Bool)
  (if (< (project p1 hour) (project p2 hour))
      #true
      (if (= (project p1 hour) (project p2 hour))
          (< (project p1 minute) (project p2 minute))
          #false)))

(define v (vec (mk-time 3 30)
               (mk-time 3 00)
               (mk-time 2 00)))
((sort! Time) v lex<)


;;;; Church encodings

;; The unit type!

(define-type-alias CUnit (All (A) (-> A A)))
(define cUnit CUnit
  (tyλ (A)
    (λ (x) x)))

;; Naturals

(define-type-alias CNat (All (A) (-> (-> A A) A A)))
(define c0 CNat
  (tyλ (A)
    (λ ([s (-> A A)] [z A]) z)))
(define c1 CNat
  (tyλ (A)
    (λ ([s (-> A A)] [z A]) (s z))))

;; Booleans

(define-type-alias CBool (All (A) (-> A A A)))
(define cTrue CBool
  (tyλ (A)
    (λ ([t A] [f A]) t)))
(define cFalse CBool
  (tyλ (A)
    (λ ([t A] [f A]) f)))

(define (bool->cbool [b Bool] -> CBool)
  (if b cTrue cFalse))
(define (cbool->bool [b CBool] -> Bool)
  ((b Bool) #t #f))

