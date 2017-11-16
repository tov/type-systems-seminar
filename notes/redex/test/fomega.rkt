#lang racket/base

(require "../fomega.rkt"
         redex/reduction-semantics
         rackunit)

(default-language fomega)

(define (unique-car lst)
  (cond
    [(null? lst) #false]
    [(null? (cdr lst)) (car lst)]
    [else (error "non-unique result")]))

(define (check-types/proc? e t-expected)
  (define t-actual (unique-car (judgment-holds (types • ,e t) t)))
  (test-equal t-actual t-expected))

(define-syntax-rule (check-types? e t)
  (check-types/proc? (term e) (term t)))

(define (check-does-not-type/proc? e)
  (check-false (unique-car (judgment-holds (types • ,e t) t))))

(define-syntax-rule (check-does-not-type? e)
  (check-does-not-type/proc? (term e)))

(check-types? (Λ a * (λ x a x))
              (all a * (-> a a)))

(check-types? (Λ a * (Λ b * (λ x a x)))
              (all a * (all b * (-> a a))))

(check-types? (Λ a * (Λ b * (λ x b x)))
              (all a * (all b * (-> b b))))

(check-types? (Λ a * (Λ b (=> * *) (λ x a x)))
              (all a * (all b (=> * *) (-> a a))))

(check-does-not-type? (Λ a * (Λ b (=> * *) (λ x b x))))

(check-types? (Λ a * (Λ b (=> * *) (λ x (ap b a) x)))
              (all a * (all b (=> * *) (-> (ap b a) (ap b a)))))

(check-types? (Λ a * (λ x a (λ y (-> a a) (ap y x))))
              (all a * (-> a (-> (-> a a) a))))

(check-types? (Λ a *
                 (λ x (ap (λ b * (-> b b)) a)
                   x))
              (all a * (-> (ap (λ b * (-> b b)) a)
                           (ap (λ b * (-> b b)) a))))

(check-types? (Λ a *
                 (λ x (ap (λ b * (-> b b)) a)
                   (λ y a (ap x y))))
              (all a * (-> (ap (λ b * (-> b b)) a)
                           (-> a a))))

(check-types? (Ap (Λ a *
                     (λ x a
                       (λ y (-> a a)
                         (ap y x))))
                  (all b * (-> b b)))
              (-> (all b * (-> b b))
                  (-> (-> (all b * (-> b b))
                          (all b * (-> b b)))
                      (all b * (-> b b)))))