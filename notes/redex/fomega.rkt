#lang racket/base

(require redex/reduction-semantics
         "util.rkt")

(define-language fomega
  (k ::=
     *
     (=> * *))
  (t ::=
     a
     (-> t t)
     (all a k t)
     (λ a k t)
     (ap t t))
  (e ::=
     x
     (λ x t e)
     (ap e e)
     (Λ a k e)
     (Ap e t))
  (Γ ::=
     •
     (extend Γ x t)
     (extend Γ a k))
  (TE ::=
     hole
     (ap TE t))
  (v ::=
     (λ x t e)
     (Λ a k e))
  (E ::=
     hole
     (ap E e)
     (ap v E)
     (Ap E t)))

(define-metafunction fomega
  lookup : Γ any -> t or k
  [(lookup (extend Γ x t) x)
   t]
  [(lookup (extend Γ a k) a)
   k]
  [(lookup (extend Γ y t) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))]
  [(lookup (extend Γ b k) a)
   (lookup Γ a)
   (side-condition (not (equal? (term a) (term b))))])

(define ->type
  (reduction-relation
   fomega #:domain t
   (--> (in-hole TE (ap (λ a k t_1) t_2))
        (in-hole TE (substitute t_1 a t_2))
        β-type)))

(define-judgment-form fomega
  #:mode (≡ I I)
  #:contract (≡ t t)
  [(where t_1* ,(apply-reduction-relation* ->type (term t_1)))
   (where t_2* ,(apply-reduction-relation* ->type (term t_2)))
   (side-condition ,(equal? (term t_1*) (term t_2*)))
   ---- equiv
   (≡ t_1 t_2)])

(define ->val
  (reduction-relation
   fomega
   #:domain e
   (--> (in-hole E (ap (λ x t e) v))
        (in-hole E (substitute e x v))
        β-val)
   (--> (in-hole E (Ap (Λ a k e) t))
        (in-hole E (substitute e a t))
        inst)))

(define-judgment-form fomega
  #:mode (kinds I I O)
  #:contract (kinds Γ t k)
  
  [---- var
   (kinds Γ a (lookup Γ a))]

  [(kinds Γ t_1 *)
   (kinds Γ t_2 *)
   ---- arr
   (kinds Γ (-> t_1 t_2) *)]

  [(kinds (extend Γ a k) t *)
   ---- all
   (kinds Γ (all a k t) *)]

  [(kinds (extend Γ a k) t *)
   ---- abs
   (kinds Γ (λ a k t) (=> * *))]

  [(kinds Γ t_1 (=> k_2 k))
   (kinds Γ t_2 k_2)
   ---- app
   (kinds Γ (ap t_1 t_2) k)])