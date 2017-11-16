#lang racket/base

(provide λ-2 ->val member kinds kinds/env types)

(require redex/reduction-semantics
         "util.rkt")

(define-language λ-2
  (t ::=
     a
     (all a t)
     (-> t t))
  (e ::=
     x
     (λ x t e)
     (ap e e)
     (Λ a e)
     (Ap e t))
  (Δ ::=
     •
     (extend Δ a))
  (Γ ::=
     •
     (extend Γ x t))
  (v ::=
     (λ x t e)
     (Λ a e))
  (E ::=
     hole
     (ap E e)
     (ap v E)
     (Ap E t))
  (γ ::=
     •
     (extend γ x v))
  (x y ::= variable-not-otherwise-mentioned)
  (a b ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ x t e #:refers-to x)
  (Λ a e #:refers-to a)
  (all a t #:refers-to a))

(define ->val
  (reduction-relation
   λ-2
   #:domain e
   (--> (in-hole E (ap (λ x t e) v))
        (in-hole E (substitute e x v))
        β-val)
   (--> (in-hole E (Ap (Λ a e) t))
        (in-hole E (substitute e a t))
        inst)))

(define-metafunction λ-2
  lookup : Γ x -> t
  [(lookup (extend Γ x t) x)
   t]
  [(lookup (extend Γ y t) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-judgment-form λ-2
  #:mode (member I I)
  #:contract (member a Δ)

  [---- found
   (member a (extend Δ a))]

  [(member a Δ)
   ---- next
   (member a (extend Δ b))])

(define-judgment-form λ-2
  #:mode (kinds I I)
  #:contract (kinds Δ t)

  [(member a Δ)
   ---- var
   (kinds Δ a)]

  [(kinds Δ t_1)
   (kinds Δ t_2)
   ---- arr
   (kinds Δ (-> t_1 t_2))]

  [(kinds (extend Δ a) t)
   ---- all
   (kinds Δ (all a t))])

(define-judgment-form λ-2
  #:mode (kinds/env I I)
  #:contract (kinds/env Δ Γ)

  [---- nil
   (kinds/env Δ •)]

  [(kinds Δ t)
   (kinds/env Δ Γ)
   ---- cons
   (kinds/env Δ (extend Γ x t))])

(define-judgment-form λ-2
  #:mode (types I I I O)
  #:contract (types Δ Γ e t)
  
  [(kinds/env Δ Γ)
   ---- var
   (types Δ Γ x (lookup Γ x))]
  
   [(kinds Δ t_1)
    (types Δ (extend Γ x t_1) e t_2)
   ---- abs
   (types Δ Γ (λ x t_1 e) (-> t_1 t_2))]
  
  [(types Δ Γ e_1 (-> t_2 t))
   (types Δ Γ e_2 t_2)
   ---- app
   (types Δ Γ (ap e_1 e_2) t)]

  [(types (extend Δ a) Γ e t)
   ---- t-abs
   (types Δ Γ (Λ a e) (all a t))]

  [(kinds Δ t)
   (types Δ Γ e (all a t_1))
   ---- t-app
   (types Δ Γ (Ap e t) (substitute t_1 a t))])
