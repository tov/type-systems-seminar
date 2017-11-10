#lang racket/base

(require "../ml.rkt")
(require racket/match
         racket/set
         rackunit
         redex/reduction-semantics)

; t t -> S or #false
(define (unify-types t_1 t_2)
  (define results (judgment-holds (unify ,t_1 ,t_2 S) S))
  (cond
    [(null? results) #false]
    [(null? (cdr results)) (car results)]
    [(fail-check "Unifies non-uniquely")]))
  
(define-check (check-unifies/fun? t_1 t_2)
  (unless (unify-types t_1 t_2)
    (fail-check "Could not unify")))

(define-syntax-rule (check-unifies? t_1 t_2)
  (check-unifies/fun? (term t_1) (term t_2)))

(define-check (check-does-not-unify/fun? t_1 t_2)
  (when (unify-types t_1 t_2)
    (fail-check "Unified")))
   
(define-syntax-rule (check-does-not-unify? t_1 t_2)
  (check-does-not-unify/fun? (term t_1) (term t_2)))

(define-check (check-unifies-with/fun? t_1 t_2 S)
  (define (subst->list S)
    (match S
      [`•                            `()]
      [`(extend-subst ,S_1 ,a ,t)    `((,a ,t) ,@(subst->list S_1))]))
  (define S-actual (subst->list (or (unify-types t_1 t_2)
                                    (fail-check "Could not unify"))))
  (unless (set=? S S-actual)
    (fail-check (format "Unifies with ~s" S-actual))))
    
(define-syntax-rule (check-unifies-with? t_1 t_2 S)
  (check-unifies-with/fun? (term t_1) (term t_2) `S))

(check-unifies? a a)
(check-unifies? a b)
(check-unifies? a bool)
(check-unifies? bool a)
(check-unifies? a (-> b b))
(check-unifies? (-> bool b) a)

(check-does-not-unify? bool (-> bool bool))
(check-does-not-unify? a (-> a bool))
(check-does-not-unify? (-> a b) (-> b (-> a a)))

(check-unifies-with? a a ())
(check-unifies-with? a b ((a b)))
(check-unifies-with? a bool ((a bool)))
(check-unifies-with? bool a ((a bool)))
(check-unifies-with? a (-> b b) ((a (-> b b))))
(check-unifies-with? a (-> a b) ())