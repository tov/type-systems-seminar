#lang racket/base
(require redex/reduction-semantics)

(define-language λcube
  (a A b B c C F T ::=
     V
     K
     (T T)
     (λ (V : T) T)
     (Π (V : T) T))
  (x V ::= variable-not-otherwise-mentioned)
  (s S ::= * □)
  (K ::= S)
  (Γ ::= <> (Γ x A))

  #:binding-forms
  (λ (x : T) T #:refers-to x)
  (Π (x : T) T #:refers-to x))

(define red
  (reduction-relation
   λcube
   #:domain T
   (--> ((λ (x : A) B) C)
        (substitute B x C))))

(define-judgment-form λcube
  #:contract (types Γ A B)
  #:mode     (types I I O)

  [-------------- "axiom"
   (types <> * □)]

  [(types Γ A s)
   ------------------- "start"
   (types (Γ x A) x A)]

  [(types Γ A B)
   (types Γ C s)
   ------------------- "weakening"
   (types (Γ x C) A B)]

  [(types Γ F (Π (x : A_1) B))
   (types Γ a A_1)
   ---------------------------------- "application"
   (types Γ (F a) (substitute B x a))]

  ;; the application rule is the only place where we
  ;; have two subderivations that produce terms that
  ;; have to be the same, so we bake conversion in
  [(types Γ F (Π (x : A_1) B))
   (types Γ a A_2)
   (equiv A_1 A_2)
   ---------------------------------- "application + conversion"
   (types Γ (F a) (substitute B x a))]

  [(types (Γ x A) b B)
   (types Γ (Π (x : A) B) s)
   ------------------------------------- "abstraction"
   (types Γ (λ (x : A) b) (Π (x : A) B))]

  [(types Γ A s_1)
   (types (Γ x A) B s_2)
   --------------------------- "λC rule"
   (types Γ (Π (x : A) B) s_2)])

;; this rule is an infinite loop in Redex, so
;; separate it out into its own judgment form
;; (so we can typeset it without running it)
(define-judgment-form λcube
  #:contract (types-C Γ A B)
  #:mode     (types-C I I O)

  [(types-C Γ A B_1)
   (equiv B_1 B_2)
   (types-C Γ B_2 s)
   ----------------- "conversion"
   (types-C Γ A B_2)])

(define-metafunction λcube
  [(→ A B)
   (Π (x : A) B)])

(define-judgment-form λcube
  #:mode (equiv I O)
  #:contract (equiv T T)

  [-------------------------- "subst"
   (equiv ((λ (x : A) B) C)
          (substitute B x C))]

  [-------------------------- "same"
   (equiv A A)])


;; Examples 5.1.15
(module+ test

  ;; 1.

  (test-judgment-holds
   (types (<> A *) (Π (x : A) A) *))

  (test-judgment-holds
   (types (<> A *) (λ (a : A) a) (Π (x : A) A)))

  (test-judgment-holds
   (types (((<> A *) B *) b B)
          (λ (a : A) b)
          (Π (a : A) B)))

  (test-judgment-holds
   (types (<> α *) (λ (a : α) a) (Π (x : α) α)))

  (test-judgment-holds
   (types ((((<> A *) B *) c A) b B)
          ((λ (a : A) b) c)
          B))

  (test-judgment-holds
   (types ((<> A *) B *)
          (λ (a : A) (λ (b : B) a))
          (Π (a : A) (Π (b : B) A)))))

;; 2.

(module+ test
  (test-judgment-holds
   (types (<> α *) (λ (a : α) a) (Π (a : α) α)))

  (test-judgment-holds
   (types <>
          (λ (α : *) (λ (a : α) a))
          (Π (α : *) (Π (a : α) α))))

  (test-judgment-holds
   (types (<> A *)
          ((λ (α : *) (λ (a : α) a)) A)
          (Π (a : A) A)))

  (test-judgment-holds
   (types ((<> A *) b A)
          (((λ (α : *) (λ (a : α) a)) A) b)
          A))

  (test-judgment-holds
   (types <>
          (λ (β : *) (λ (a : (Π (α : *) α)) ((a (→ (Π (α : *) α) β)) a)))
          (Π (β : *) (Π (x : (Π (α : *) α)) β)))))
