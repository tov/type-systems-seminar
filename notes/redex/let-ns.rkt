#lang racket/base

(require redex)

(define-language let-ns
  (e ::=
     n
     s
     (+ e e)
     (* e e)
     (length e)
     (append e e)
     x
     (let x e e))
  (n ::= integer)
  (s ::= string)
  (x y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (let x e_1 e_2 #:refers-to x))

(define-extended-language let-ns/eval let-ns
  (v ::=
     n
     s)
  (E ::=
     hole
     (+ E e)
     (+ v E)
     (* E e)
     (* v E)
     (length E)
     (append E e)
     (append v E)
     (let x E e)))

(define ->val
  (reduction-relation
   let-ns/eval
   #:domain e
   (--> (in-hole E (+ n_1 n_2))
        (in-hole E ,(+ (term n_1) (term n_2)))
        plus)
   (--> (in-hole E (* n_1 n_2))
        (in-hole E ,(* (term n_1) (term n_2)))
        times)
   (--> (in-hole E (length s))
        (in-hole E ,(string-length (term s)))
        length)
   (--> (in-hole E (append s_1 s_2))
        (in-hole E ,(string-append (term s_1) (term s_2)))
        append)
   (--> (in-hole E (let x v e))
        (in-hole E (substitute e x v))
        let)))

(default-language let-ns/eval)

(test-->> ->val
          (term 4)
          (term 4))

(test-->> ->val
          (term (+ 4 5))
          (term 9))

(test-->> ->val
          (term (length "hello"))
          (term 5))

(test-->> ->val
          (term (+ 2 (+ 3 4)))
          (term 9))

(test-->> ->val
          (term (+ (+ 2 3) 4))
          (term 9))

(test-->> ->val
          (term (+ (+ 2 3) (+ 4 5)))
          (term 14))

(test-->> ->val
          (term (* 4 (+ 3 (length "hi"))))
          (term 20))

(test-->> ->val
          (term (let x 5 (+ x x)))
          (term 10))

; stuck
(test-->> ->val
          (term (+ 4 "hello"))
          (term (+ 4 "hello")))

; stuck, and demonstrates alpha equivalence
(test-->> ->val
          (term (let x (+ 4 "hello") (+ x 1)))
          (term (let y (+ 4 "hello") (+ y 1))))
