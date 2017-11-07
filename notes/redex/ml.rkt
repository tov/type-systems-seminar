#lang racket/base

(require redex/reduction-semantics
         "util.rkt")

(define-language λ-hm
  (e ::=
     x
     (λ x e)
     (ap e e)
     (let x e e))
  (v ::=
     (λ x e))
  (E ::=
     hole
     (ap E e)
     (ap v E)
     (let x E e))
  (t ::=
     a
     (-> t t))
  (σ ::=
     t
     (all a σ))
  (Γ ::=
     •
     (extend Γ x σ))
  (S ::=
     •
     (extend S a t))
  (x y ::= variable-not-otherwise-mentioned)
  (a b ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ x e #:refers-to x)
  (let x e_1 e_2 #:refers-to x)
  (all a s #:refers-to a))

(define ->val
  (reduction-relation
   λ-hm
   #:domain e
   (--> (in-hole E (ap (λ x e) v))
        (in-hole E (substitute e x v))
        β-val)
   (--> (in-hole E (let x v e))
        (in-hole E (substitute e x v))
        let)))

(define-judgment-form λ-hm
  #:mode (lookup I I O)
  #:contract (lookup Γ x σ)
  
  [---- here
   (lookup (extend Γ x σ) x σ)]
  
  [(lookup Γ x σ)
   (side-condition (not (equal? (term x) (term y))))
   ---- next
   (lookup (extend Γ y σ_1) x σ)])

(define-judgment-form λ-hm
  #:mode (W I I O O)
  #:contract (W Γ e S t)

  [(lookup Γ x t)
   ---- var
   (W Γ x • (apply-substitution • t))])

#;
(define-judgment-form λ-hm
  #:mode (types I I I)
  #:contract (types Γ e t)

  [(
   ---- var
   (types Γ x t))])