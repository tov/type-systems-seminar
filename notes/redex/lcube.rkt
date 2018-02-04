#lang racket/base
(require redex/reduction-semantics)
(provide λcube types types/alt env-ok)

(define-language λcube
  (a A b B c C F e τ ::=
     x
     (λ (x : e) e)
     (ap e e)
     (Π (x : e) e)
     s)
  (x y α β ::= variable-not-otherwise-mentioned)
  (s ::= * □)
  (Γ ::= • (extend Γ x A))

  #:binding-forms
  (λ (x : e_1) e_2 #:refers-to x)
  (Π (x : e_1) e_2 #:refers-to x))

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

  [(types Γ F (Π (x : A_1) B)) (types Γ a A_1)
   ------------------------------------------- "application"
   (types Γ (ap F a) (substitute B x a))]

  ;; the application rule is the only place where we
  ;; have two subderivations that produce terms that
  ;; have to be the same, so we bake conversion in
  [(types Γ F (Π (x : A_1) B)) (types Γ a A_2) (≡ A_1 A_2)
   ------------------------------------------------------- "application + conversion"
   (types Γ (ap F a) (substitute B x a))]

  [(types (extend Γ x A) b B) (types Γ (Π (x : A) B) s)
   ---------------------------------------------------- "abstraction"
   (types Γ (λ (x : A) b) (Π (x : A) B))]

  [(types Γ A s_1) (types (extend Γ x A) B s_2)
   -------------------------------------------- "λC"
   (types Γ (Π (x : A) B) s_2)])

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

(define-metafunction λcube
  [(→ A B)
   (Π (x : A) B)])

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
   (types (extend • A *) (Π (x : A) A) *))

  (test-judgment-holds
   (types (extend • A *) (λ (a : A) a) (Π (x : A) A)))

  (test-judgment-holds
   (types (extend (extend (extend • A *) B *) b B)
          (λ (a : A) b)
          (Π (a : A) B)))

  (test-judgment-holds
   (types (extend • α *) (λ (a : α) a) (Π (x : α) α)))

  (test-judgment-holds
   (types (extend (extend (extend (extend • A *) B *) c A) b B)
          (ap (λ (a : A) b) c)
          B))

  (test-judgment-holds
   (types (extend (extend • A *) B *)
          (λ (a : A) (λ (b : B) a))
          (Π (a : A) (Π (b : B) A)))))

;; 2.

(module+ test
  (test-judgment-holds
   (types (extend • α *) (λ (a : α) a) (Π (a : α) α)))

  (test-judgment-holds
   (types •
          (λ (α : *) (λ (a : α) a))
          (Π (α : *) (Π (a : α) α))))

  (test-judgment-holds
   (types (extend • A *)
          (ap (λ (α : *) (λ (a : α) a)) A)
          (Π (a : A) A)))

  (test-judgment-holds
   (types (extend (extend • A *) b A)
          (ap (ap (λ (α : *) (λ (a : α) a)) A) b)
          A))

  (test-judgment-holds
   (types •
          (λ (β : *) (λ (a : (Π (α : *) α)) (ap (ap a (→ (Π (α : *) α) β)) a)))
          (Π (β : *) (Π (x : (Π (α : *) α)) β)))))


(module+ test
  (test-equal
   (judgment-holds
    (types •
           (λ (x : *) (λ (x : (Π (x : *) x)) x))
           any)
    any)
   (list (term (Π (x : *) (Π (x : (Π (x : *) x)) (Π (x : *) x)))))))
