#lang racket/base

(provide λ-ml ->val W inst gen unify)

(require redex/reduction-semantics
         racket/set
         "util.rkt")

(define-language λ-ml
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
  (C ::=
     true
     (and C C)
     (= t t)
     (ex a C))
  (x y ::= variable-not-otherwise-mentioned)
  (a b ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ x e #:refers-to x)
  (let x e_1 e_2 #:refers-to x)
  (all a s #:refers-to a)
  (ex a C #:refers-to a))

(define ->val
  (reduction-relation
   λ-ml
   #:domain e
   (--> (in-hole E (ap (λ x e) v))
        (in-hole E (substitute e x v))
        β-val)
   (--> (in-hole E (let x v e))
        (in-hole E (substitute e x v))
        let)))

(define-metafunction λ-ml
  lookup : Γ x -> σ
  [(lookup (extend Γ x σ) x)
   σ]
  [(lookup (extend Γ y σ) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-metafunction λ-ml
  \\ : (a ...) (a ...) -> (a ...)
  [(\\ (a ...) (b ...))
   ,(set-subtract (term (a ...)) (term (b ...)))])

(define-metafunction λ-ml
  ∪ : (a ...) ... -> (a ...)
  [(∪ (a ...) ...)
   ,(apply set-union (term ((a ...) ...)))])

(define-metafunction λ-ml
  ftv : σ -> (a ...)
  [(ftv a)
   (a)]
  [(ftv (all a σ))
   (\\ (ftv σ) (a))]
  [(ftv (-> t_1 t_2))
   (∪ (ftv t_1) (ftv t_2))])

(define-metafunction λ-ml
  ftv/Γ : Γ -> (a ...)
  [(ftv/Γ •)
   ()]
  [(ftv/Γ (extend Γ x σ))
   (∪ (ftv/Γ Γ) (ftv σ))])

(define-metafunction λ-ml
  ftv/S : S -> (a ...)
  [(ftv/S •)
   ()]
  [(ftv/S (extend S a t))
   (∪ (ftv/S S) (ftv t))])

(define-metafunction λ-ml
  apply-subst : S σ -> σ
  [(apply-subst • σ)
   σ]
  [(apply-subst (extend S a t) σ)
   (substitute (apply-subst S σ) a t)])

(define-metafunction λ-ml
  apply-subst/Γ : S Γ -> Γ
  [(apply-subst/Γ S •)
   •]
  [(apply-subst/Γ S (extend Γ x σ))
   (extend (apply-subst/Γ S Γ) x (apply-subst S σ))])

(define-metafunction λ-ml
  apply-subst/S : S S -> S
  [(apply-subst/S S •)
   •]
  [(apply-subst/S S (extend S_1 a t))
   (extend (apply-subst/S S S_1) a (apply-subst S t))])

(define-metafunction λ-ml
  concat-subst : S S -> S
  [(concat-subst S •)
   S]
  [(concat-subst S (extend S_1 a t))
   (extend (concat-subst S S_1) a t)])

(define-metafunction λ-ml
  compose-subst : S S -> S
  [(compose-subst S_1 S_2) (concat-subst S_1 (apply-subst/S S_1 S_2))])

(define-metafunction λ-ml
  fresh : a (a ...) -> a
  [(fresh a (b ...))
   ,(variable-not-in (term (b ...)) (term a))])

(define-judgment-form λ-ml
  #:mode (∈ I I)
  #:contract (∈ a (a ...))
  [---- in
   (∈ a (b_i ... a b_j ...))])

(define-judgment-form λ-ml
  #:mode (∉ I I)
  #:contract (∉ a (a ...))
  [(side-condition ,(not (member (term a) (term (b ...)))))
    ---- not-in
   (∉ a (b ...))])

(define-judgment-form λ-ml
  #:mode (unify I I O)
  #:contract (unify t t S)
  
  [---- var-same
   (unify a a •)]
  
  [(∉ a (ftv t))
   ---- var-left
   (unify a t (extend • a t))]
  
  [(unify a (-> t_1 t_2) S)
   ---- var-right
   (unify (-> t_1 t_2) a S)]
  
  [(unify t_11 t_21 S_1)
   (unify (apply-subst S_1 t_12) (apply-subst S_1 t_22) S_2)
   ---- arr
   (unify (-> t_11 t_12) (-> t_21 t_22) (compose-subst S_2 S_1))])

(define-judgment-form λ-ml
  #:mode (inst I I O)
  #:contract (inst (a ...) σ t)

  [---- mono
   (inst (a ...) t t)]

  [(where b_1 (fresh b (a ...)))
   (inst (a ... b_1) (substitute σ b b_1) t)
   ---- all
   (inst (a ...) (all b σ) t)])

(define-judgment-form λ-ml
  #:mode (gen I I O)
  #:contract (gen (a ...) t σ)
  
  [---- mono
   (gen () t t)]
  
  [(gen (a_i ...) t σ)
   ---- all
   (gen (a a_i ...) t (all a σ))])

(define-judgment-form λ-ml
  #:mode (W I I O O)
  #:contract (W Γ e S t)

  [(inst (ftv/Γ Γ) (lookup Γ x) t)
   ---- var
   (W Γ x • t)]

  [(W Γ e_1 S_1 t_1)
   (W (apply-subst/Γ S_1 Γ) e_2 S_2 t_2)
   (where a (fresh α (∪ (ftv/Γ Γ) (ftv/S S_1) (ftv/S S_2) (ftv t_1) (ftv t_2))))
   (unify (apply-subst S_2 t_1) (-> t_2 a) S_3)
   ---- app
   (W Γ (ap e_1 e_2) (compose-subst S_3 (compose-subst S_2 S_1)) (apply-subst S_3 a))]

  [(where a (fresh α (ftv/Γ Γ)))
   (W (extend Γ x a) e S t)
   ---- abs
   (W Γ (λ x e) S (-> (apply-subst S a) t))]

  [(W Γ e_1 S_1 t_1)
   (gen (\\ (ftv t_1) (ftv/Γ (apply-subst/Γ S_1 Γ))) t_1 σ)
   (W (extend (apply-subst/Γ S_1 Γ) x σ) e_2 S_2 t_2)
   ---- let
   (W Γ (let x e_1 e_2) (compose-subst S_2 S_1) t_2)])

(define-judgment-form λ-ml
  #:mode (generate I I I O)
  #:contract (generate Γ e t C)

  [---- var
   (generate Γ x t (= t (lookup Γ x)))]

  [(where a (fresh))
   (where b (fresh))
   (generate (extend Γ x a) e b C)
   ---- abs
   (generate Γ (λ x e) t (ex a (ex b (and (= t (-> a b)) C))))]

  [(where a (fresh))
   (generate Γ e_1 (-> a t) C_1)
   (generate Γ e_2 a C_2)
   ---- app
   (generate Γ (ap e_1 e_2) t (ex a (and C_1 C_2)))])


