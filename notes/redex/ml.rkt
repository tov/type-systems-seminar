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
     (extend-subst S a t))
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
  ftv : any -> (a ...)
  ; Type variables
  [(ftv a)                       (a)]
  ; Types
  [(ftv (-> t_1 t_2))            (∪ (ftv t_1) (ftv t_2))]
  ; Type schemes
  [(ftv (all a σ))               (\\ (ftv σ) (a))]
  ; Environments
  [(ftv •)                       ()]
  [(ftv (extend Γ x σ))          (∪ (ftv Γ) (ftv σ))]
  ; Substitutions
  [(ftv (extend-subst S a t))    (∪ (ftv S) (ftv t))]
  ; Constraints
  [(ftv true)                    ()]
  [(ftv (and C_1 C_2))           (∪ (ftv C_1) (ftv C_2))]
  [(ftv (= t_1 t_2))             (∪ (ftv t_1) (ftv t_2))]
  [(ftv (ex a C))                (\\ (ftv C) (a))])

(define-metafunction λ-ml
  apply-subst : S any -> any
  [(apply-subst • any)
   any]
  [(apply-subst (extend-subst S a t) any)
   (substitute (apply-subst S any) a t)])

(define-metafunction λ-ml
  concat-subst : S S -> S
  [(concat-subst S •)
   S]
  [(concat-subst S (extend-subst S_1 a t))
   (extend-subst (concat-subst S S_1) a t)])

(define-metafunction λ-ml
  compose-subst : S S -> S
  [(compose-subst S_1 S_2) (concat-subst S_1 (apply-subst S_1 S_2))])

(define-metafunction λ-ml
  fresh : a any -> a
  [(fresh a any)
   ,(variable-not-in (term any) (term a))])

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
   (unify a t (extend-subst • a t))]
  
  [(unify a (-> t_1 t_2) S)
   ---- var-right
   (unify (-> t_1 t_2) a S)]
  
  [(unify t_11 t_21 S_1)
   (unify (apply-subst S_1 t_12) (apply-subst S_1 t_22) S_2)
   ---- arr
   (unify (-> t_11 t_12) (-> t_21 t_22) (compose-subst S_2 S_1))])

(define-metafunction λ-ml
  inst : (a ...) σ -> t
  [(inst (a ...) t)
   t]
  [(inst (a ...) (all b σ))
   (inst (a ... b_1) (substitute σ b b_1))
   (where b_1 (fresh b (a ...)))])
  
(define-metafunction λ-ml
  gen : (a ...) t -> σ
  [(gen () t)
   t]
  [(gen (a a_i ...) t)
   (all a (gen (a_i ...) t))])

(define-judgment-form λ-ml
  #:mode (W I I O O)
  #:contract (W Γ e S t)

  [(where t (inst (ftv Γ) (lookup Γ x)))
   ---- var
   (W Γ x • t)]

  [(W Γ e_1 S_1 t_1)
   (W (apply-subst S_1 Γ) e_2 S_2 t_2)
   (where a (fresh β (Γ S_1 S_2 t_1 t_2)))
   (unify (apply-subst S_2 t_1) (-> t_2 a) S_3)
   ---- app
   (W Γ (ap e_1 e_2) (compose-subst S_3 (compose-subst S_2 S_1)) (apply-subst S_3 a))]

  [(where a (fresh α Γ))
   (W (extend Γ x a) e S t)
   ---- abs
   (W Γ (λ x e) S (-> (apply-subst S a) t))]

  [(W Γ e_1 S_1 t_1)
   (where σ (gen (\\ (ftv t_1) (ftv (apply-subst S_1 Γ))) t_1))
   (W (extend (apply-subst S_1 Γ) x σ) e_2 S_2 t_2)
   ---- let
   (W Γ (let x e_1 e_2) (compose-subst S_2 S_1) t_2)])

(define-judgment-form λ-ml
  #:mode (solve I O)
  #:contract (solve C S)

  [---- true
   (solve true •)]

  [(solve C_1 S_1)
   (solve C_2 S_2)
   ---- and
   (solve (and C_1 C_2) (compose-subst S_2 S_1))])

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


