#lang racket/base

(provide let-ns let-ns/eval ->val)
         
(require redex
         "util.rkt")

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
        (in-hole E (meta-+ n_1 n_2))
        plus)
   (--> (in-hole E (* n_1 n_2))
        (in-hole E (meta-* n_1 n_2))
        times)
   (--> (in-hole E (length s))
        (in-hole E (meta-length s))
        length)
   (--> (in-hole E (append s_1 s_2))
        (in-hole E (meta-append s_1 s_2))
        append)
   (--> (in-hole E (let x v e))
        (in-hole E (substitute e x v))
        let)))

(define-lifted-metafunction let-ns/eval
  meta-+ : n_1 n_2 -> n
  +)

(define-lifted-metafunction let-ns/eval
  meta-* : n_1 n_2 -> n
  *)

(define-lifted-metafunction let-ns/eval
  meta-length : s -> n
  string-length)

(define-lifted-metafunction let-ns/eval
  meta-append : s_1 s_2 -> s
  string-append)

;;
;; Big-step evaluator
;;

(define-extended-language let-ns/env let-ns/eval
  (ρ ::= ([x v] ...)))

(define-metafunction let-ns/env
  extend : ρ x v -> ρ
  [(extend ([x_i v_i] ... [x v_old] [x_j v_j] ...) x v)
   ([x_i v_i] ... [x v] [x_j v_j] ...)]
  [(extend ([x_i v_i] ...) x v)
   ([x v] [x_i v_i] ...)
   (side-condition (not (member (term x) (term (x_i ...)))))])

(define-metafunction let-ns/env
  lookup : ρ x -> v
  [(lookup ([x_i v_i] ... [x v] [x_j v_j] ...) x)
   v])

(define-metafunction let-ns/env
  eval : ρ e -> v
  [(eval ρ n)                  n]
  [(eval ρ s)                  s]
  [(eval ρ (+ e_1 e_2))        (meta-+ n_1 n_2)
                               (where n_1 (eval ρ e_1))
                               (where n_2 (eval ρ e_2))]
  [(eval ρ (* e_1 e_2))        (meta-* n_1 n_2)
                               (where n_1 (eval ρ e_1))
                               (where n_2 (eval ρ e_2))]
  [(eval ρ (length e))         (meta-length s)
                               (where s (eval ρ e))]
  [(eval ρ (append e_1 e_2))   (meta-append s_1 s_2)
                               (where s_1 (eval ρ e_1))
                               (where s_2 (eval ρ e_2))]
  [(eval ρ x)                  (lookup ρ x)]
  [(eval ρ (let x e_1 e_2))    (eval (extend ρ x v_1) e_2)
                               (where v_1 (eval ρ e_1))])

;;
;; Tests
;;

(default-language let-ns/env)

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

(test-equal (term (eval () 5))
            (term 5))

(test-equal (term (eval () (+ 3 4)))
            (term 7))

(test-equal (term (eval ([x 4]) (let y (length "hello") (* x y))))
            (term 20))