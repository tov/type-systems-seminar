#lang racket/base
(require redex/reduction-semantics)
(provide λcube types types/alt env-ok)

(define-language λcube
  (a A b B c C F e τ ::=
     x
     (λ (x : e) e)
     (ap e e)
     s
     (x : e → e))
  (x y α β ::= variable-not-otherwise-mentioned)
  (s ::= * □)
  (Γ ::= • (extend Γ x A))

  #:binding-forms
  (λ (x : e_1) e_2 #:refers-to x)
  (x : e_1 → e_2 #:refers-to x))

(module+ test (default-language λcube))

(define red
  (reduction-relation
   λcube
   #:domain e
   (--> (ap (λ (x : A) B) C)
        (substitute B x C))))

(define-judgment-form λcube
  #:contract (types Γ A B)
  #:mode     (types I I O)

  [-------------- "axiom"
   (types Γ * □)]

  [(env-ok Γ)
   ------------------------ "variable"
   (types Γ x (lookup Γ x))]

  [(types Γ F (x : A → B)) (types Γ a A)
   ------------------------------------- "application"
   (types Γ (ap F a) (substitute B x a))]

  ;; the application rule is the only place where we
  ;; have two subderivations that produce terms that
  ;; have to be the same, so we bake conversion in
  [(types Γ F (x : A_1 → B)) (types Γ a A_2) (≡ A_1 A_2)
   ----------------------------------------------------- "application + conversion"
   (types Γ (ap F a) (substitute B x a))]

  [(types (extend Γ x A) b B) (types Γ (x : A → B) s)
   ---------------------------------------------------- "abstraction"
   (types Γ (λ (x : A) b) (x : A → B))]

  [(types Γ A s_1) (types (extend Γ x A) B s_2)
   -------------------------------------------- "λC"
   (types Γ (x : A → B) s_2)])

(define-judgment-form λcube
  #:mode (env-ok I)
  #:contract (env-ok Γ)

  [---------- "nil"
   (env-ok •)]

  [(types Γ A s)
   ----------------------- "cons"
   (env-ok (extend Γ x A))])

;; this rule is an infinite loop in Redex, so
;; separate it out into its own judgment form
;; (so we can typeset it without running it)
(define-judgment-form λcube
  #:contract (types/alt Γ A B)
  #:mode     (types/alt I I O)

  [(types/alt Γ A B_1) (≡/alt B_1 B_2) (types/alt Γ B_2 s)
   ------------------------------------------------------- "conversion"
   (types/alt Γ A B_2)])

(define-metafunction λcube
  lookup : Γ x -> e
  [(lookup (extend Γ x e) x)
   e]
  [(lookup (extend Γ y e) x)
   (lookup Γ x)])

(define-judgment-form λcube
  #:mode (≡ I I)
  #:contract (≡ e e)

  [------- "refl"
   (≡ A A)]

  [(≡ (substitute B x C) e)
    ------------------------- "β"
   (≡ (ap (λ (x : A) B) C) e)]

  [(≡ A_1 A_2) (≡ B_1 B_2)
   ----------------------------- "ap"
   (≡ (ap A_1 B_1) (ap A_2 B_2))])

(define-judgment-form λcube
  #:mode (≡/alt I O)
  #:contract (≡/alt e e)

  [----------- "refl"
   (≡/alt A A)])


(module+ test

  (test-judgment-holds
   (≡ (ap (λ (x : □) x) *) *))

  (test-judgment-holds
   (≡ (ap (λ (x : □) (ap (λ (y : □) x) *)) *) *)))


;; Examples 5.1.15
(module+ test

  ;; 1.

  (test-judgment-holds
   (types (extend • A *) (x : A → A) *))

  (test-judgment-holds
   (types (extend • A *) (λ (a : A) a) (x : A → A)))

  (test-judgment-holds
   (types (extend (extend (extend • A *) B *) b B)
          (λ (a : A) b)
          (a : A → B)))

  (test-judgment-holds
   (types (extend • α *) (λ (a : α) a) (x : α → α)))

  (test-judgment-holds
   (types (extend (extend (extend (extend • A *) B *) c A) b B)
          (ap (λ (a : A) b) c)
          B))

  (test-judgment-holds
   (types (extend (extend • A *) B *)
          (λ (a : A) (λ (b : B) a))
          (a : A → (b : B → A)))))

;; 2.

(module+ test
  (test-judgment-holds
   (types (extend • α *) (λ (a : α) a) (a : α → α)))

  (test-judgment-holds
   (types •
          (λ (α : *) (λ (a : α) a))
          (α : * → (a : α → α))))

  (test-judgment-holds
   (types (extend • A *)
          (ap (λ (α : *) (λ (a : α) a)) A)
          (a : A → A)))

  (test-judgment-holds
   (types (extend (extend • A *) b A)
          (ap (ap (λ (α : *) (λ (a : α) a)) A) b)
          A))

  (test-judgment-holds
   (types •
          (λ (β : *) (λ (a : (α : * → α)) (ap (ap a (i : (α : * → α) → β)) a)))
          (β : * → (x : (α : * → α) → β)))))


(module+ test
  (test-equal
   (judgment-holds
    (types •
           (λ (x : *) (λ (x : (x : * → x)) x))
           any)
    any)
   (list (term (x : * → (x : (x : * → x) → (x : * → x)))))))
