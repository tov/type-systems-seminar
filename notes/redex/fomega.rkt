#lang racket/base

(provide fomega ->type ->val kinds types)

(require redex/reduction-semantics
         "util.rkt")

(define-language fomega
  (k ::=
     *
     (=> k k))
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
     (-> TE t)
     (-> t TE)
     (all a k TE)
     (λ a k TE)
     (ap TE t)
     (ap t TE))
  (v ::=
     (λ x t e)
     (Λ a k e))
  (E ::=
     hole
     (ap E e)
     (ap v E)
     (Ap E t))
  (a b ::= variable-not-otherwise-mentioned)
  (x y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (all a k t #:refers-to a)
  (λ a k t #:refers-to a)
  (Λ a k e #:refers-to a)
  (λ x t e #:refers-to x))
  
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
  #:mode (≡ I O)
  #:contract (≡ t t)
  [(where t_2 ,(car (apply-reduction-relation* ->type (term t_1))))
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

  [(kinds (extend Γ a k_1) t k_2)
   ---- abs
   (kinds Γ (λ a k_1 t) (=> k_1 k_2))]

  [(kinds Γ t_1 (=> k_2 k))
   (kinds Γ t_2 k_2)
   ---- app
   (kinds Γ (ap t_1 t_2) k)])

(define-judgment-form fomega
  #:mode (types I I O)
  #:contract (types Γ e t)

  [---- var
   (types Γ x (lookup Γ x))]

  [(kinds Γ t_1 *)
   (types (extend Γ x t_1) e t_2)
   ---- abs
   (types Γ (λ x t_1 e) (-> t_1 t_2))]

  [(types Γ e_1 t_1)
   (types Γ e_2 t_2)
   (≡ t_1 (-> t_2* t))
   (≡ t_2 t_2*)
   ---- app
   (types Γ (ap e_1 e_2) t)]

  [(types (extend Γ a k) e t)
   ---- tabs
   (types Γ (Λ a k e) (all a k t))]

  [(kinds Γ t k)
   (types Γ e t_1)
   (≡ t_1 (all a k t_1*))
   ---- tapp
   (types Γ (Ap e t) (substitute t_1* a t))])
