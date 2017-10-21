#lang racket/base

(provide let-nl let-nl/eval ->val size)

(require redex
         "util.rkt")

(define-language let-nl
  (e ::=
     n
     nil
     (cons e e)
     (+ e e)
     (* e e)
     (car e)
     (cdr e)
     x
     (let x e e))
  (n ::= integer)
  (x y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (let x e_1 e_2 #:refers-to x))

(define-extended-language let-nl/eval let-nl
  (v ::=
     n
     nil
     (cons v v))
  (E ::=
     hole
     (cons E e)
     (cons v E)
     (+ E e)
     (+ v E)
     (* E e)
     (* v E)
     (car E)
     (cdr E)
     (let x E e))
  (C ::=
     e
     WRONG))

(define ->val
  (reduction-relation
   let-nl/eval
   #:domain C
   (--> (in-hole E (+ n_1 n_2))
        (in-hole E (meta-+ n_1 n_2))
        plus)
   (--> (in-hole E (* n_1 n_2))
        (in-hole E (meta-* n_1 n_2))
        times)
   (--> (in-hole E (car (cons v_1 v_2)))
        (in-hole E v_1)
        car)
   (--> (in-hole E (cdr (cons v_1 v_2)))
        (in-hole E v_2)
        cdr)
   (--> (in-hole E (car nil))
        WRONG
        car-nil)
   (--> (in-hole E (cdr nil))
        WRONG
        cdr-nil)
   (--> (in-hole E (let x v e))
        (in-hole E (substitute e x v))
        let)))

(define-lifted-metafunction let-nl/eval
  meta-+ : n_1 n_2 -> n
  +)

(define-lifted-metafunction let-nl/eval
  meta-* : n_1 n_2 -> n
  *)

(define-metafunction let-nl
  size : e -> n
  [(size n) 0]
  [(size nil) 0]
  [(size (cons e_1 e_2))
   (meta-+ (size e_1) (size e_2))]
  [(size (+ e_1 e_2))
   (meta-+ 1 (meta-+ (size e_1) (size e_2)))]
  [(size (* e_1 e_2))
   (meta-+ 1 (meta-+ (size e_1) (size e_2)))]
  [(size (car e_1))
   (meta-+ 1 (size e_1))]
  [(size (cdr e_1))
   (meta-+ 1 (size e_1))]
  [(size x) 0]
  [(size (let x e_1 e_2))
   (meta-+ 1 (meta-+ (size e_1) (size e_2)))])

;;
;; Big-step evaluator
;;

(define-extended-language let-nl/env let-nl/eval
  (ρ ::=
     •
     (extend ρ x v)))

(define-metafunction let-nl/env
  lookup : ρ x -> v
  [(lookup (extend ρ x v) x)
   v]
  [(lookup (extend ρ y v) x)
   (lookup ρ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-metafunction let-nl/env
  eval : ρ e -> v
  [(eval ρ n)                      n]
  [(eval ρ nil)                    nil]
  [(eval ρ (cons e_1 e_2))         (cons v_1 v_2)
                                   (where v_1 (eval ρ e_1))
                                   (where v_2 (eval ρ e_2))]
  [(eval ρ (+ e_1 e_2))            (meta-+ n_1 n_2)
                                   (where n_1 (eval ρ e_1))
                                   (where n_2 (eval ρ e_2))]
  [(eval ρ (* e_1 e_2))            (meta-* n_1 n_2)
                                   (where n_1 (eval ρ e_1))
                                   (where n_2 (eval ρ e_2))]
  [(eval ρ (car e))                v_1
                                   (where (cons v_1 v_2) (eval ρ e))]
  [(eval ρ (cdr e))                v_2
                                   (where (cons v_1 v_2) (eval ρ e))]
  [(eval ρ (car e))                WRONG ; this violates eval's contract
                                   (where nil (eval ρ e))]
  [(eval ρ (cdr e))                WRONG ; this violates eval's contract
                                   (where nil (eval ρ e))]
  [(eval ρ (car nil))              0]
  [(eval ρ (cdr nil))              nil]
  [(eval ρ x)                      (lookup ρ x)]
  [(eval ρ (let x e_1 e_2))        (eval (extend ρ x v_1) e_2)
                                   (where v_1 (eval ρ e_1))])


;; Tests
;;

(module+ test
  (default-language let-nl/eval)

  (test-->> ->val
            (term 4)
            (term 4))

  (test-->> ->val
            (term (+ 4 5))
            (term 9))

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
            (term (let x 5 (+ x x)))
            (term 10))

  (test-->> ->val
            (term (car nil))
            (term WRONG))

  (test-->> ->val
            (term (car (cons (+ 3 4) nil)))
            (term 7))

  ; it's untyped:
  (test-->> ->val
            (term (let x (cons (cons 4 nil) 7)
                    (* (car (car x)) (cdr x))))
            (term 28)))

; fully-reduce : e -> (or/c v #false)
; Uses the reduction relation to evaluate `e`, returning #false if reduction
; gets stuck or is non-deterministics.
(define (fully-reduce e)
  (define reduced (apply-reduction-relation* ->val e))
  (and (= 1 (length reduced))
       ((term-match/single let-nl/eval
          [v (term v)]
          [_ #false])
        (car reduced))))
     
; fully-evaluate : e -> (or/c v #false)
; Uses the big-step evaluation metafunction to evaluate `e`, returning
; #false if the metafunction doesn't apply.
(define (fully-evaluate e)
  (with-handlers ([exn:fail? (λ (exn) #false)])
    (term (eval • ,e))))

(define (dynamics-agree? e)
  (equal? (fully-reduce e) (fully-evaluate e)))

(module+ test
  (redex-check let-nl/eval e (dynamics-agree? (term e)) #:source ->val)
  #;(redex-check let-nl/eval e (dynamics-agree? (term e)) #:source eval))
