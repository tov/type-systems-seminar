#lang racket/base

(provide λ-qual
         ->val δ
         type-of
         > qimplies qtypes
         unify inst qreduce W
         get-evidence app-evidence abs-evidence qtranslates)

(require redex/reduction-semantics
         racket/set
         (only-in racket/list remove-duplicates)
         "util.rkt")

(caching-enabled? #f)

(define-language λ-qual
  (e ::=
     x
     (λ x e)
     (ap e e)
     (let x e e)
     c
     (if0 e e e)
     (pair e e))
  (v ::=
     c
     (λ x e)
     (pair v v))
  (c ::=
     z
     fst
     snd
     -
     =
     <)
  (z ::= integer)
  (E ::=
     hole
     (ap E e)
     (ap v E)
     (pair E e)
     (pair v E)
     (if0 E e e)
     (let x E e))
  (t ::=
     a
     Int
     (Prod t t)
     (-> t t))
  (C ::=
     Eq
     Ord)
  (π ::=
     (C t))
  (P ::=
     [π ...])
  (ρ ::= (=> P t))
  (as ::=
      (a ...))
  (σ ::=
     (all as ρ))
  (Γ ::=
     •
     (extend Γ x σ))
  (Δ ::=
     [(x π) ...])
  (S ::=
     •
     (extend-subst S a t))
  (x y ::= variable-not-otherwise-mentioned)
  (a b ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ x e #:refers-to x)
  (let x e_1 e_2 #:refers-to x)
  (all (a ...) ρ #:refers-to (shadow a ...)))

(define-metafunction λ-qual
  meta-< : v v -> z
  [(meta-< z_1 z_2)
   ,(if (< (term z_1) (term z_2)) (term 0) (term 1))])

(define-metafunction λ-qual
  meta-= : v v -> z
  [(meta-= v_1 v_2)
   ,(if (equal? (term v_1) (term v_2)) (term 0) (term 1))])

(define-lifted-metafunction λ-qual
  meta-- : z_1 z_2 -> z
  -)

(define-metafunction λ-qual
  δ : c v -> v
  [(δ fst (pair v_1 v_1))    v_1]
  [(δ snd (pair v_1 v_2))    v_2]
  [(δ - (pair z_1 z_2))      (meta-- z_1 z_2)]
  [(δ = (pair v_1 v_2))      (meta-= v_1 v_2)]
  [(δ < (pair v_1 v_2))      (meta-< v_1 v_2)])

(define-metafunction λ-qual
  non-zero? : z -> boolean
  [(non-zero? z)     ,(not (zero? (term z)))])

(define ->val
  (reduction-relation
   λ-qual
   #:domain e
   (--> (in-hole E (ap (λ x e) v))
        (in-hole E (substitute e x v))
        β-val)
   (--> (in-hole E (let x v e))
        (in-hole E (substitute e x v))
        let)
   (--> (in-hole E (if0 0 e_1 e_2))
        (in-hole E e_1)
        if-true)
   (--> (in-hole E (if0 z e_1 e_2))
        (in-hole E e_2)
        (side-condition (term (non-zero? z)))
        if-false)
   (--> (in-hole E (ap c v))
        (in-hole E (δ c v))
        delta)))

(define-metafunction λ-qual
  type-of : c -> σ
  [(type-of z)     (all () (=> [] Int))]
  [(type-of fst)   (all (a b) (=> [] (-> (Prod a b) a)))]
  [(type-of snd)   (all (a b) (=> [] (-> (Prod a b) b)))]
  [(type-of -)     (all () (=> [] (-> (Prod Int Int) Int)))]
  [(type-of =)     (all (a) (=> [(Eq a)] (-> (Prod a a) Int)))]
  [(type-of <)     (all (a) (=> [(Ord a)] (-> (Prod a a) Int)))])

(define-metafunction λ-qual
  qjoin : P P -> P
  [(qjoin [π_1 ...] [π_2 ...]) [π_1 ... π_2 ...]])

(define-metafunction λ-qual
  lookup : Γ x -> σ
  [(lookup (extend Γ x σ) x)
   σ]
  [(lookup (extend Γ y σ) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-metafunction λ-qual
  \\ : as as -> as
  [(\\ (a ...) (b ...))
   ,(set-subtract (term (a ...)) (term (b ...)))])

(define-metafunction λ-qual
  ∪ : as ... -> as
  [(∪)
   ()]
  [(∪ (a ...) (b ...) ...)
   ,(apply set-union (term ((a ...) (b ...) ...)))])

(define-metafunction λ-qual
  parens : any -> any
  [(parens any) any])

(define-metafunction λ-qual
  ftv : any -> (a ...)
  ; Type variables
  [(ftv a)                       (a)]
  ; Types
  [(ftv (-> t_1 t_2))            (∪ (ftv t_1) (ftv t_2))]
  [(ftv (Prod t_1 t_2))          (∪ (ftv t_1) (ftv t_2))]
  [(ftv Int)                     ()]
  ; Constraints
  [(ftv (C t))                   (ftv t)]
  [(ftv [π ...])                 (∪ (ftv π) ...)]
  ; Qualified types
  [(ftv (=> P t))                (∪ (ftv P) (ftv t))]
  ; Type schemes
  [(ftv (all as ρ))              (\\ (ftv ρ) as)]
  ; Environments
  [(ftv •)                       ()]
  [(ftv (extend Γ x σ))          (∪ (ftv Γ) (ftv σ))]
  ; Substitutions
  [(ftv (extend-subst S a t))    (∪ (ftv S) (ftv t))])

(define-metafunction λ-qual
  apply-subst : S any -> any
  [(apply-subst • any)
   any]
  ; This case should not be necessary by my understanding, but it
  ; avoids a problem.
  [(apply-subst S (extend-subst S_rest a t))
   (extend-subst (apply-subst S S_rest) a (apply-subst S t))]
  [(apply-subst (extend-subst S a t) any)
   (apply-subst S (substitute any a t))])

(define-metafunction λ-qual
  concat-subst : S S -> S
  [(concat-subst S •)
   S]
  [(concat-subst S (extend-subst S_1 a t))
   (extend-subst (concat-subst S S_1) a t)])

(define-metafunction λ-qual
  compose-subst : S S -> S
  [(compose-subst S_1 S_2) (concat-subst S_1 (apply-subst S_1 S_2))])

(define-metafunction λ-qual
  fresh : a any -> a
  [(fresh a any)
   ,(variable-not-in (term any) (term a))])

(define-judgment-form λ-qual
  #:mode (∈ I I)
  #:contract (∈ a (a ...))
  [---- in
   (∈ a (b_i ... a b_j ...))])

(define-judgment-form λ-qual
  #:mode (∉ I I)
  #:contract (∉ a (a ...))
  [(side-condition ,(not (member (term a) (term (b ...)))))
    ---- not-in
   (∉ a (b ...))])

(define-judgment-form λ-qual
  #:mode (not-a-type-variable I)
  #:contract (not-a-type-variable t)
  [(side-condition ,(not (redex-match? λ-qual a (term t))))
    ---- only
   (not-a-type-variable t)])

(define-judgment-form λ-qual
  #:mode (unify I I O)
  #:contract (unify t t S)

  [---- var-same
   (unify a a •)]

  [(∉ a (ftv t))
   ---- var-left
   (unify a t (extend-subst • a t))]

  [(not-a-type-variable t)
   (unify a t S)
   ---- var-right
   (unify t a S)]

  [---- int
   (unify Int Int •)]

  [(unify t_11 t_21 S_1)
   (unify (apply-subst S_1 t_12) (apply-subst S_1 t_22) S_2)
   ---- prod
   (unify (Prod t_11 t_12) (Prod t_21 t_22) (compose-subst S_2 S_1))]

  [(unify t_11 t_21 S_1)
   (unify (apply-subst S_1 t_12) (apply-subst S_1 t_22) S_2)
   ---- arr
   (unify (-> t_11 t_12) (-> t_21 t_22) (compose-subst S_2 S_1))])

(define-metafunction λ-qual
  inst : (a ...) σ -> ρ
  [(inst (a ...) (all () ρ))
   ρ]
  [(inst (a ...) (all (b b_i ...) ρ))
   (inst (a ... b_1) (substitute (all (b_i ...) ρ) b b_1))
   (where b_1 (fresh b (b_i ... a ...)))])

(define-metafunction λ-qual
  qsimplify : P -> P
  [(qsimplify [])
   []]
  [(qsimplify [(Eq Int) π_i ...])
   (qsimplify [π_i ...])]
  [(qsimplify [(Eq (Prod t_1 t_2)) π_i ...])
   (qsimplify [(Eq t_1) (Eq t_2) π_i ...])]
  [(qsimplify [(Ord Int) π_i ...])
   (qsimplify [π_i ...])]
  [(qsimplify [(C a) π_i ...])
   (qjoin [(C a)] (qsimplify [π_i ...]))])

(define-metafunction λ-qual
  qreduce : P -> P
  [(qreduce P)
   ,(remove-duplicates (term (qsimplify P)))])

(define-judgment-form λ-qual
  #:mode (W I I O O O)
  #:contract (W Γ e S t P)

  [(where (=> P t) (inst (ftv Γ) (lookup Γ x)))
   ---- var
   (W Γ x • t P)]

  [(where (=> P t) (inst (ftv Γ) (type-of c)))
   ---- const
   (W Γ c • t P)]

  [(W Γ e_1 S_1 t_1 P_1)
   (W (apply-subst S_1 Γ) e_2 S_2 t_2 P_2)
   (where a (fresh β (Γ S_1 S_2 t_1 t_2 P_1 P_2)))
   (unify (apply-subst S_2 t_1) (-> t_2 a) S_3)
   ---- app
   (W Γ (ap e_1 e_2) (compose-subst S_3 (compose-subst S_2 S_1)) (apply-subst S_3 a) (apply-subst S_3 (parens (qjoin (apply-subst S_2 P_1) P_2))))]

  [(where a (fresh α Γ))
   (W (extend Γ x (all () (=> [] a))) e S t P)
   ---- abs
   (W Γ (λ x e) S (-> (apply-subst S a) t) P)]

  [(W Γ e_1 S_1 t_1 P_1)
   (W (apply-subst S_1 Γ) e_2 S_2 t_2 P_2)
   ---- pair
   (W Γ (pair e_1 e_2) (compose-subst S_2 S_1) (Prod (apply-subst S_2 t_1) t_2) (qjoin (apply-subst S_2 P_1) P_2))]

  [(W Γ e_1 S_1 t_1 P_1)
   (W (apply-subst S_1 Γ) e_2 S_2 t_2 P_2)
   (W (apply-subst S_2 (apply-subst S_1 Γ)) e_3 S_3 t_3 P_3)
   (unify (apply-subst S_3 (apply-subst S_2 t_1)) Int S_4)
   (unify (apply-subst S_4 (apply-subst S_3 t_2)) (apply-subst S_4 t_3) S_5)
   (where S (compose-subst S_5 (compose-subst S_4 (compose-subst S_3 (compose-subst S_2 S_1)))))
   ---- if0
   (W Γ (if e_1 e_2 e_3) S (apply-subst S_5 (apply-subst S_4 t_3)) (apply-subst S_5 (apply-subst S_4 (parens (qjoin (apply-subst S_3 (parens (qjoin (apply-subst S_2 P_1) P_2))) P_3)))))]

  [(W Γ e_1 S_1 t_1 P_1)
   (where P (qreduce P_1))
   (where σ (all (parens (\\ (parens (∪ (ftv P) (ftv t_1))) (ftv (apply-subst S_1 Γ)))) (=> P t_1)))
   (W (extend (apply-subst S_1 Γ) x σ) e_2 S_2 t_2 P_2)
   ---- let
   (W Γ (let x e_1 e_2) (compose-subst S_2 S_1) t_2 P_2)])

(define-judgment-form λ-qual
  #:mode (> I O)
  #:contract (> σ ρ)
  [---- mono
   (> (all () ρ) ρ)]
  [(where/hidden t guess-type)
   (> (substitute (all (a_i ...) ρ_0) a t) ρ)
   ---- all
   (> (all (a a_i ...) ρ_0) ρ)])

(define-judgment-form λ-qual
  #:mode (qimplies I I)
  #:contract (qimplies P P)

  [---- refl
   (qimplies P P)]

  [(where/hidden P_2 fake-P)
   (qimplies P_1 P_2) (qimplies P_2 P_3)
   ---- trans
   (qimplies P_1 P_3)]

  [---- dup
   (qimplies [π_i ... π π_j ... π_k ...] [π_i ... π π_j ... π π_k ...])]

  [---- eq-int
   (qimplies [π_i ... π_j ...] [π_i ... (Eq Int) π_j ...])]

  [--- eq-prod
   (qimplies [π_i ... (Eq t_1) (Eq t_2) π_j ...] [π_i ... (Eq (Prod t_1 t_2)) π_j ...])]

  [---- ord-int
   (qimplies [π_i ... π_j ...] [π_i ... (Ord Int) π_j ...])])

(define-judgment-form λ-qual
  #:mode (qtypes O I I O)
  #:contract (qtypes P Γ e t)

  [(> (lookup Γ x) (=> P t))
   ---- var-inst
   (qtypes P Γ x t)]

  [(> (type-of c) (=> P t))
   ---- const-inst
   (qtypes P Γ c t)]

  [(where/hidden t_1 guess-type)
   (qtypes P (extend Γ x t_1) e t_2)
   ---- abs
   (qtypes P Γ (λ x e) (-> t_1 t_2))]

  [(qtypes P_1 Γ e_1 (-> t_2 t))
   (qtypes P_2 Γ e_2 t_2)
   ---- app
   (qtypes [qjoin P_1 P_2] Γ (ap e_1 e_2) t)]

  [(qtypes P_1 Γ e_1 Int)
   (qtypes P_2 Γ e_2 t)
   (qtypes P_3 Γ e_3 t)
   --- if0
   (qtypes (qjoin P_1 (qjoin P_2 P_3)) Γ (if0 e_1 e_2 e_3) t)]

  [(qtypes P_1 Γ e_1 t_1)
   (qtypes P_2 Γ e_2 t_2)
   ---- pair
   (qtypes (qjoin P_1 P_2) Γ (pair e_1 e_2) (Prod t_1 t_2))]

  [(qtypes P_1 Γ e_1 t_1)
   (where/hidden P fake-P)
   (qimplies P P_1)
   (where σ (all (parens (\\ (parens (∪ (ftv P) (ftv t_1))) (ftv Γ))) (=> P t_1)))
   (qtypes P_2 (extend Γ x σ) e_2 t)
   ---- let-gen
   (qtypes P_2 Γ (let x e_1 e_2) t)])

(define-judgment-form λ-qual
  #:mode (get-evidence I O I)

  [(where/hidden =/int fake)
   ---- eq-int
   (get-evidence Δ =/int (Eq Int))]

  [(where/hidden </int fake)
   ---- ord-int
   (get-evidence Δ </int (Ord Int))]

  [(get-evidence Δ e_1 (Eq t_1))
   (get-evidence Δ e_2 (Eq t_2))
   (where e_out (λ p (if0 (ap e_1 (pair (ap fst (ap fst p)) (ap fst (ap snd p))))
                          (ap e_2 (pair (ap snd (ap fst p)) (ap snd (ap snd p))))
                          1)))
   ---- eq-prod
   (get-evidence Δ e_out (Eq (Prod t_1 t_2)))]

  [---- lookup
   (get-evidence [(x_i π_i) ... (x π) (x_j π_j) ...] x π)])

(define-judgment-form λ-qual
  #:mode (app-evidence I I I O)
  #:contract (app-evidence Δ P e e)

  [---- nil
   (app-evidence Δ [] e e)]

  [(get-evidence Δ e_ev π)
   (app-evidence Δ [π_i ...] (ap e e_ev) e_out)
   ---- cons
   (app-evidence Δ [π π_i ...] e e_out)])

(define-judgment-form λ-qual
  #:mode (abs-evidence I I O O)
  #:contract (abs-evidence Δ e P e)

  [---- nil
   (abs-evidence [] e [] e)]

  [(abs-evidence [(x_i π_i) ...] (λ x e) [π_out ...] e_out)
   ---- cons
   (abs-evidence [(x π) (x_i π_i) ...] e [π π_out ...] e_out)])

(define-judgment-form λ-qual
  #:mode (qtranslates I I I O O)
  #:contract (qtranslates Δ Γ e e t)

  [(> (lookup Γ x) (=> P t))
   (app-evidence Δ P x e)
   ---- var
   (qtranslates Δ Γ x e t)]

  [(> (type-of c) (=> P t))
   (app-evidence Δ P c e)
   ---- const
   (qtranslates Δ Γ c e t)]

  [(where/hidden t_1 guess-type)
   (qtranslates Δ (extend Γ x t_1) e e_^† t_2)
   ---- abs
   (qtranslates Δ Γ (λ x e) e_^† (-> t_1 t_2))]

  [(qtranslates Δ Γ e_1 e_1^† (-> t_2 t))
   (qtranslates Δ Γ e_2 e_2^† t_2)
   ---- app
   (qtranslates Δ Γ (ap e_1 e_2) (ap e_1^† e_2^†) t)]

  [(qtranslates Δ Γ e_1 e_1^† Int)
   (qtranslates Δ Γ e_2 e_2^† t)
   (qtranslates Δ Γ e_3 e_3^† t)
   --- if0
   (qtranslates Δ Γ (if0 e_1 e_2 e_3) (if0 e_1^† e_2^† e_3^†) t)]

  [(qtranslates Δ Γ e_1 e_1^† t_1)
   (qtranslates Δ Γ e_2 e_2^† t_2)
   ---- pair
   (qtranslates Δ Γ (pair e_1 e_2) (pair e_1^† e_2^†) (Prod t_1 t_2))]

  [(where/hidden Δ_1 fake-Δ)
   (qtranslates Δ_1 Γ e_1 e_1^† t_1)
   (abs-evidence Δ_1 e_1^† P e_1^‡)
   (where σ (all (parens (\\ (parens (∪ (ftv P) (ftv t_1))) (ftv Γ))) (=> P t_1)))
   (qtranslates Δ_2 (extend Γ x σ) e_2 e_2^† t)
   ---- let
   (qtranslates Δ_2 Γ (let x e_1 e_2) (let x e_1^‡ e_2^†) t)])


