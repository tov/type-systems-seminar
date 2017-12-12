#lang racket/base

(provide λ-P)

(require redex/reduction-semantics
         "util.rkt")

(define-language λ-P
  (M N A B s ::=
     x
     c
     (ap M M)
     (λ x M M)
     (Pi x M M))
  (c ::=
     *
     ☐)
  (Γ ::=
     •
     (extend Γ x M))
  (E ::=
     hole
     (ap E M)
     (ap M E)
     (λ x E M)
     (λ x M E)
     (Pi x E M)
     (Pi x M E))
  (x y a b ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ x M N #:refers-to x)
  (Pi x M N #:refers-to x))

(define ->free
  (reduction-relation
   λ-P #:domain M
   (--> (ap (λ x A M) N)
        (substitute M x N)
        β)))

(define (-->* term)
  (apply-reduction-relation* ->free term))

(define-judgment-form λ-P
  #:mode (=β I I)
  #:contract (=β M M)
  [(where A ,(car (apply-reduction-relation* ->free (term M))))
   (where A ,(car (apply-reduction-relation* ->free (term N))))
   ---- converts-to
   (=β M N)])

(define-judgment-form λ-P
  #:mode (types I I O)
  #:contract (types Γ M M)

  [---- axiom
   (types • * ☐)]

  [---- start
   (types (extend Γ x A) x A)]

  [(types Γ M B)
   (types Γ A s)
   ---- weakening
   (types (extend Γ x A) M B)]

  [(types Γ A s_1)
   (=β s_1 *)
   (types (extend Γ x A) B s_2)
    ---- type/kind-formation
   (types Γ (Pi x A B) s_2)]

  [(types Γ M (Pi x A_M B))
   (types Γ N A_N)
   (=β A_M A_N)
   ---- application/conversion
   (types Γ (ap M N) (substitute B x N))]

  [(types (extend Γ x M) N A)
   (types Γ (Pi x M A) s)
   ---- abstraction
   (types Γ (λ x M N) (Pi x M A))])

(define-metafunction λ-P
  -> : A A -> A
  [(-> A B) (Pi X-dummy A B)])

