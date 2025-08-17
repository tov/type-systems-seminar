#lang racket/base
(require "util.rkt" redex/reduction-semantics)
(provide prelim bounded-bst wrong-bst in-bst in-bt)

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
  meta-sub1 : z -> z
  sub1)

(define-judgment-form prelim
  #:mode (perfect I I)
  [-----
   (perfect leaf 0)]

  [(perfect bt_1 (meta-sub1 n))
   (perfect bt_2 (meta-sub1 n))
   -----
   (perfect (node z bt_1 bt_2) n)])

(module+ test
  (test-judgment-holds (perfect leaf 0))
  (test-judgment-holds (perfect (node 0 leaf leaf) 1))
  (test-judgment-holds (perfect (node 1 (node 0 leaf leaf) (node 2 leaf leaf)) 2))
  (test-judgment-holds (perfect (node 3
                                      (node 1 (node 0 leaf leaf) (node 2 leaf leaf))
                                      (node 1 (node 0 leaf leaf) (node 2 leaf leaf)))
                                3)))

(define-judgment-form prelim
  #:mode (complete I I)
  [-----
   (complete leaf 0)]

  [(complete bt_1 (meta-sub1 n))
   (perfect bt_2 (meta-sub1 (meta-sub1 n)))
   -----
   (complete (node z bt_1 bt_2) n)]

  [(perfect bt_1 (meta-sub1 n))
   (complete bt_2 (meta-sub1 n))
   -----
   (complete (node z bt_1 bt_2) n)])

(module+ test
  (test-judgment-holds (complete leaf 0))
  (test-judgment-holds (complete (node 0 leaf leaf) 1))
  (test-judgment-holds (complete (node 0 (node 1 leaf leaf) leaf) 2))
  (test-judgment-holds (complete (node 1 (node 0 leaf leaf) (node 2 leaf leaf)) 2))
  (test-judgment-holds (complete (node 3
                                       (node 1 (node 0 leaf leaf) leaf)
                                       (node 1 leaf leaf))
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
  (test-judgment-holds (complete (node 3
                                       (node 1
                                             (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                                             (node 2 (node 0 leaf leaf) (node 0 leaf leaf)))
                                       (node 1
                                             (node 0 (node 0 leaf leaf) (node 0 leaf leaf))
                                             (node 2 (node 0 leaf leaf) leaf)))
                                 4)))


(define-lifted-metafunction prelim
  meta-≤ : z_1 z_2 -> boolean
  <=)

(define-lifted-metafunction prelim
  meta-< : z_1 z_2 -> boolean
  <)

(define-lifted-metafunction prelim
  meta-min : z_1 z_2 -> z
  min)

(define-lifted-metafunction prelim
  meta-max : z_1 z_2 -> z
  max)

(define-judgment-form prelim
  #:mode (jf-≤ I I)

  [(where #t (meta-≤ z_1 z_2))
   -----
   (jf-≤ z_1 z_2)])

(define-judgment-form prelim
  #:mode (jf-< I I)

  [(where #t (meta-< z_1 z_2))
   -----
   (jf-< z_1 z_2)])

(define-judgment-form prelim
  #:mode (bounded-bst I I I)

  [(jf-≤ z_1 z_2)
   -------------------- "leaf"
   (bounded-bst leaf z_1 z_2)]

  [(bounded-bst bt_1 z_1 z_2) (bounded-bst bt_2 z_2 z_3)
   -------------------- "node"
   (bounded-bst (node z_2 bt_1 bt_2) z_1 z_3)])

(define-judgment-form prelim
  #:mode (wrong-bst I I I)

  [-------------------- "leaf"
   (wrong-bst leaf z_1 z_2)]

  [(wrong-bst bt_1 z_1 z_2) (wrong-bst bt_2 z_2 z_3)
   -------------------- "node"
   (wrong-bst (node z_2 bt_1 bt_2) z_1 z_3)])

(module+ test
  (test-judgment-holds (bounded-bst leaf 0 100))
  (test-judgment-holds (bounded-bst (node 50 leaf leaf) 0 100))
  (test-judgment-holds (bounded-bst (node 50
                                          (node 10 leaf leaf)
                                          (node 60 leaf leaf))
                                    0 100))
  (test-equal (judgment-holds (bounded-bst (node 50
                                                 (node 60 leaf leaf)
                                                 (node 60 leaf leaf))
                                           0 100))
              #f)

  (test-equal (judgment-holds (bounded-bst (node 0
                                                 (node -1 leaf leaf)
                                                 (node 1 leaf leaf))
                                           0 0))
              #f)
  (test-judgment-holds (wrong-bst (node 0
                                        (node -1 leaf leaf)
                                        (node 1 leaf leaf))
                                  0 0)))

(define-judgment-form prelim
  #:mode (in-bst I I)
  
  [--------------------------------- "here_bst"
   (in-bst z_1 (node z_1 bt_1 bt_2))]

  [(in-bst z_2 bt_1) (jf-< z_2 z_1)
   --------------------------------- "left_bst"
   (in-bst z_2 (node z_1 bt_1 bt_2))]

  [(in-bst z_2 bt_2) (jf-< z_1 z_2)
   ---------------------------------- "right_bst"
   (in-bst z_2 (node z_1 bt_1 bt_2))])

(module+ test
  (test-judgment-holds
   (in-bst 0 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
  (test-judgment-holds
   (in-bst 1 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
  (test-judgment-holds
   (in-bst 2 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
  (test-equal
   (judgment-holds
    (in-bst 3 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
   #f))

(define-judgment-form prelim
  #:mode (in-bt I I)
  
  [--------------------------------- "here_bt"
   (in-bt z_1 (node z_1 bt_1 bt_2))]

  [(in-bt z_2 bt_1)
   --------------------------------- "left_bt"
   (in-bt z_2 (node z_1 bt_1 bt_2))]

  [(in-bt z_2 bt_2)
   ---------------------------------- "right_bt"
   (in-bt z_2 (node z_1 bt_1 bt_2))])

(module+ test
  (test-judgment-holds
   (in-bt 0 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
  (test-judgment-holds
   (in-bt 1 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
  (test-judgment-holds
   (in-bt 2 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
  (test-equal
   (judgment-holds
    (in-bt 3 (node 1 (node 0 leaf leaf) (node 2 leaf leaf))))
   #f))

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

