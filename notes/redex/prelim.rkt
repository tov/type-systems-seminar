#lang racket/base
(require "util.rkt"
         redex/reduction-semantics
         racket/match)
(provide prelim perfect complete)

(define-language prelim
  (bt ::=
      leaf
      (node z bt bt))
  (C ::=
     hole
     (node z bt C)
     (node z C bt))
  (E ::=
     hole
     (node z l-bt E)
     (node z E bt))
  (l-bt ::= leaf (node z leaf l-bt))
  (z ::= integer)
  (n ::= natural)
  (ℕ ::= 0 (succ ℕ)))

(define-lifted-metafunction prelim
  meta-add1 : z -> z
  add1)

(define-lifted-metafunction prelim
  meta-add2 : z -> z
  (λ (x) (+ x 2)))

(define-lifted-metafunction prelim
  meta-sub1 : z -> z
  sub1)

(define-lifted-metafunction prelim
  meta-sub2 : z -> z
  (λ (x) (- x 2)))

(define-judgment-form prelim
  #:mode (perfect I O)
  [----- "leaf"
   (perfect leaf 0)]

  [(perfect bt_1 n) (perfect bt_2 n)
   ----- "node"
   (perfect (node z bt_1 bt_2) (meta-add1 n))])

(module+ test
  (test-judgment-holds (perfect leaf 0))
  (test-judgment-holds (perfect (node 0 leaf leaf) 1))
  (test-judgment-holds (perfect (node 1 (node 0 leaf leaf) (node 2 leaf leaf)) 2))
  (test-judgment-holds (perfect (node 3
                                      (node 1 (node 0 leaf leaf) (node 2 leaf leaf))
                                      (node 1 (node 0 leaf leaf) (node 2 leaf leaf)))
                                3)))

(define-judgment-form prelim
  #:mode (offbyone I O)
  [-----
   (offbyone n ,(add1 (term n)))])

;; it would be nice to replace uses of `(complete-add1 bt n)` with
;; `(complete bt (meta-add1 n))` but redex doesn't support that, alas
(define-judgment-form prelim
  #:mode (complete-add1 I O)
  [(complete bt n)
   ----
   (complete-add1 bt (meta-sub1 n))])

(define-judgment-form prelim
  #:mode (complete I O)
  [----- "leaf"
   (complete leaf 0)]

  [(complete-add1 bt_1 n) (perfect bt_2 n)
   ----- "left"
   (complete (node z bt_1 bt_2) (meta-add2 n))]

  [(perfect bt_1 n) (complete bt_2 n)
   ----- "right"
   (complete (node z bt_1 bt_2) (meta-add1 n))])

(module+ test
  (test-judgment-holds (complete leaf 0))
  (test-judgment-holds (complete (node 0 leaf leaf) 1))
  (test-judgment-holds (complete (node 0 (node 1 leaf leaf) leaf) 2))
  (test-judgment-holds (complete (node 1 (node 0 leaf leaf) (node 2 leaf leaf)) 2))
  (test-judgment-holds (complete (node 2
                                       (node 1 (node 0 leaf leaf) leaf)
                                       (node 3 leaf leaf))
                                 3))
  (test-judgment-holds (complete (node 3
                                       (node 1 (node 0 leaf leaf) (node 2 leaf leaf))
                                       (node 1 leaf leaf))
                                 3))
  (test-judgment-holds (complete (node 3
                                       (node 1 (node 0 leaf leaf) (node 2 leaf leaf))
                                       (node 1 (node 0 leaf leaf) leaf))
                                 3))
  (test-judgment-holds (complete (node 3
                                       (node 1 (node 0 leaf leaf) (node 2 leaf leaf))
                                       (node 1 (node 0 leaf leaf) (node 2 leaf leaf)))
                                 3))
  (test-judgment-holds (complete (node 3
                                       (node 1
                                             (node 0 (node 0 leaf leaf) leaf)
                                             (node 2 leaf leaf))
                                       (node 1
                                             (node 0 leaf leaf)
                                             (node 2 leaf leaf)))
                                 4))
  (test-judgment-holds
   (complete
    (node 3
          (node 1
                (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                (node 2 (node 0 leaf leaf) (node 0 leaf leaf)))
          (node 1
                (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                (node 2 (node 0 leaf leaf) leaf)))
    4)))

(define (complete-height bt)
  (define jh (judgment-holds (complete bt z) z))
  jh)

(define-lifted-metafunction prelim
  meta-+ : z_1 z_2 -> z
  +)

(define-metafunction prelim
  leaves : bt -> n
  [(leaves leaf) 1]
  [(leaves (node z bt_1 bt_2)) (meta-+ (leaves bt_1) (leaves bt_2))])

(define (leaves-of-complete-trees bt)
  (define sizes (judgment-holds (complete ,bt n) n))
  (cond
    [(pair? sizes)
     (define n (car sizes))
     (<= (expt 2 (- n 1))
         (term (leaves ,bt))
         (expt 2 n))]
    [else #t]))

(module+ test
  (test-equal (leaves-of-complete-trees (term leaf)) #t)
  (test-equal (leaves-of-complete-trees (term (node 0 leaf leaf))) #t)
  (test-equal (leaves-of-complete-trees (term (node 0 (node 0 leaf leaf) leaf))) #t)
  (test-equal (leaves-of-complete-trees (term (node 0 (node 0 leaf leaf) (node 0 leaf leaf))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0 (node 0 leaf leaf) leaf)
                      (node 0 leaf leaf))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                      (node 0 leaf leaf))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                      (node 0 (node 0 leaf leaf) leaf))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0 (node 0 (node 0 leaf leaf) leaf) (node 0 leaf leaf))
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                            (node 0 leaf leaf))
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                            (node 0 (node 0 leaf leaf) leaf))
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))))
              #t)

  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))
                      (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))))
              #t)

  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))
                      (node 0
                            (node 0 (node 0 leaf leaf) leaf)
                            (node 0 leaf leaf)))))
              #t)
  (test-equal (leaves-of-complete-trees
               (term
                (node 0
                      (node 0
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf)))
                      (node 0
                            (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                            (node 0 (node 0 leaf leaf) leaf)))))
              #t)

  (redex-check prelim bt #:ad-hoc
               (leaves-of-complete-trees
                (term bt))))
  

(define-judgment-form prelim
  #:mode (rotl I O)
  [----
   (rotl (in-hole C (node z_2 (node z_1 bt_1 bt_2) bt_3))
         (in-hole C (node z_1 bt_1 (node z_2 bt_2 bt_3))))])

(define-judgment-form prelim
  #:mode (rotl-std I O)
  [----
   (rotl-std (in-hole E (node z_2 (node z_1 bt_1 bt_2) l-bt_3))
             (in-hole E (node z_1 bt_1 (node z_2 bt_2 l-bt_3))))])

(module+ test
  (test-->> rotl
            (term (node 4
                        (node 2
                              (node 1 leaf leaf)
                              (node 3 leaf leaf))
                        (node 6
                              (node 5 leaf leaf)
                              (node 7 leaf leaf))))
            (term (node
                   1 leaf
                   (node
                    2 leaf
                    (node
                     3 leaf
                     (node
                      4 leaf
                      (node
                       5 leaf
                       (node
                        6 leaf
                        (node 7 leaf leaf)))))))))

  (test--> rotl
           (term (node 4
                       (node 2
                             (node 1 leaf leaf)
                             (node 3 leaf leaf))
                       (node 6
                             (node 5 leaf leaf)
                             (node 7 leaf leaf))))
           (term (node 4
                       (node
                        1 leaf
                        (node
                         2 leaf
                         (node 3 leaf leaf)))
                       (node 6
                             (node 5 leaf leaf)
                             (node 7 leaf leaf))))
           (term (node 2
                       (node 1 leaf leaf)
                       (node 4
                             (node 3 leaf leaf)
                             (node 6
                                   (node 5 leaf leaf)
                                   (node 7 leaf leaf)))))
           (term
            (node
             4
             (node 2 (node 1 leaf leaf) (node 3 leaf leaf))
             (node 5 leaf (node 6 leaf (node 7 leaf leaf))))))

  (test-->> rotl-std
            (term (node 4
                        (node 2
                              (node 1 leaf leaf)
                              (node 3 leaf leaf))
                        (node 6
                              (node 5 leaf leaf)
                              (node 7 leaf leaf))))
            (term (node
                   1 leaf
                   (node
                    2 leaf
                    (node
                     3 leaf
                     (node
                      4 leaf
                      (node
                       5 leaf
                       (node
                        6 leaf
                        (node 7 leaf leaf)))))))))

  (test--> rotl-std
           (term (node 4
                       (node 2
                             (node 1 leaf leaf)
                             (node 3 leaf leaf))
                       (node 6
                             (node 5 leaf leaf)
                             (node 7 leaf leaf))))
           (term (node 4
                       (node
                        1 leaf
                        (node
                         2 leaf
                         (node 3 leaf leaf)))
                       (node 6
                             (node 5 leaf leaf)
                             (node 7 leaf leaf))))))
