#lang racket/base

(provide let-zl let-zl/eval ->val size)

(require redex/reduction-semantics
         "util.rkt")

(define-language let-zl
  (e ::=
     z
     nil
     (cons e e)
     (+ e e)
     (* e e)
     (car e)
     (cdr e)
     x
     (let x e e))
  (z ::= integer)
  (x y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (let x e_1 e_2 #:refers-to x))

(define-extended-language let-zl/eval let-zl
  (v ::=
     z
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
   let-zl/eval
   #:domain C
   (--> (in-hole E (+ z_1 z_2))
        (in-hole E (meta-+ z_1 z_2))
        plus)
   (--> (in-hole E (* z_1 z_2))
        (in-hole E (meta-* z_1 z_2))
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

(define-lifted-metafunction let-zl/eval
  meta-+ : z_1 z_2 -> z
  +)

(define-lifted-metafunction let-zl/eval
  meta-* : z_1 z_2 -> z
  *)

(define-metafunction let-zl
  size : e -> z
  [(size z) 0]
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

(define-extended-language let-zl/env let-zl/eval
  (ρ ::=
     •
     (extend ρ x v)))

(define-metafunction let-zl/env
  lookup : ρ x -> v
  [(lookup (extend ρ x v) x)
   v]
  [(lookup (extend ρ y v) x)
   (lookup ρ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-metafunction let-zl/env
  eval : ρ e -> v
  [(eval ρ z)                      z]
  [(eval ρ nil)                    nil]
  [(eval ρ (cons e_1 e_2))         (cons v_1 v_2)
                                   (where v_1 (eval ρ e_1))
                                   (where v_2 (eval ρ e_2))]
  [(eval ρ (+ e_1 e_2))            (meta-+ z_1 z_2)
                                   (where z_1 (eval ρ e_1))
                                   (where z_2 (eval ρ e_2))]
  [(eval ρ (* e_1 e_2))            (meta-* z_1 z_2)
                                   (where z_1 (eval ρ e_1))
                                   (where z_2 (eval ρ e_2))]
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
  (default-language let-zl/eval)

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
       ((term-match/single let-zl/eval
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
  (redex-check let-zl/eval e (dynamics-agree? (term e)) #:source ->val)
  (redex-check let-zl/env (ρ e) (dynamics-agree? (term e)) #:source eval))
