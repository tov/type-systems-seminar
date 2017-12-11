#lang s-exp "../stlc.rkt"

;;;; Some examples

(define (negate [x Int] -> Int)
  (- 0 x))

(define (+ [x Int] [y Int] -> Int)
  (- x (negate y)))

(define (< [n Int] [m Int] -> Bool)
  (positive? (- m n)))

(define (= [n Int] [m Int] -> Bool)
  (zero? (- m n)))

;;;; Sorting

(define (swap! [v (Vec Int)] [i Int] [j Int] -> Unit)
  (let ([old-v-i (vec-ref v i)])
    (vec-set! v i (vec-ref v j))
    (vec-set! v j old-v-i)))

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

;;;; Weighted, path-compressing union-find

(define-type-alias UF (Record [id (Vec Int)] [sz (Vec Int)]))

(define (uf:create [size Int] -> UF)
  (record [id (build-vec size (λ ([i Int]) i))]
          [sz (build-vec size (λ ([i Int]) 1))]))

(define (uf:find [uf UF] [obj Int] -> Int)
  (let ([id (project uf id)])
    (if (= obj (vec-ref id obj))
        obj
        (begin
          (vec-set! id obj (vec-ref id (vec-ref id obj)))
          (uf:find uf (vec-ref id obj))))))

(define (uf:union! [uf UF] [obj1 Int] [obj2 Int] -> Unit)
  (let ([id (project uf id)]
        [sz (project uf sz)]
        [root1 (uf:find uf obj1)]
        [root2 (uf:find uf obj2)])
    (if (= root1 root2)
        (void)
        (if (< (vec-ref sz root1) (vec-ref sz root2))
            (begin
              (vec-set! id root1 root2)
              (vec-set! sz root2 (+ (vec-ref sz root1) (vec-ref sz root2))))
            (begin
              (vec-set! id root2 root1)
              (vec-set! sz root1 (+ (vec-ref sz root1) (vec-ref sz root2))))))))
            
(define (uf:same-set? [uf UF] [obj1 Int] [obj2 Int] -> Bool)
  (= (uf:find uf obj1) (uf:find uf obj2)))
