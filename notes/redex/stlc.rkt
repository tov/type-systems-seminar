#lang racket/base

(provide stlc ->val types satisfies SN
         stlc/rec stlc/fix ->val/rec ->val/fix
         types/alt)

(require redex/reduction-semantics
         "util.rkt")

(define-language stlc
  (t ::=
     nat
     (-> t t))
  (e ::=
     x
     z
     (s e)
     (λ x t e)
     (ap e e))
  (Γ ::=
     •
     (extend Γ x t))    
  (v ::=
     z
     (s v)
     (λ x t e))
  (E ::=
     hole
     (s E)
     (ap E e)
     (ap v E))
  (γ ::=
     •
     (extend-subst γ x v))
  (x y ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ x t e #:refers-to x))

(define ->val
  (reduction-relation
   stlc
   #:domain e
   (--> (in-hole E (ap (λ x t e) v))
        (in-hole E (substitute e x v))
        β-val)))

(define-metafunction stlc
  lookup : Γ x -> t
  [(lookup (extend Γ x t) x)
   t]
  [(lookup (extend Γ y t) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-judgment-form stlc
  #:mode (types I I O)
  #:contract (types Γ e t)
  
  [---- var
   (types Γ x (lookup Γ x))]
  
  [---- zero
   (types Γ z nat)]
  
  [(types Γ e nat)
   ---- succ
   (types Γ (s e) nat)]
  
  [(types (extend Γ x t_1) e t_2)
   ---- abs
   (types Γ (λ x t_1 e) (-> t_1 t_2))]
  
  [(types Γ e_1 (-> t_2 t))
   (types Γ e_2 t_2)
   ---- app
   (types Γ (ap e_1 e_2) t)])

(define-judgment-form stlc
  #:mode (SN I I)
  #:contract (SN t e)
  [---- not-right
   (SN nat e)])

(define-judgment-form stlc
  #:mode (satisfies I I)
  #:contract (satisfies γ Γ)

  [---- nil
   (satisfies • •)]

  [(SN t v)
   (satisfies γ Γ)
   ---- cons
   (satisfies (extend-subst γ x v) (extend Γ x t))])

; This is based on Gödel’s T via Harper in Practical Foundations:
(define-extended-language stlc/rec stlc
  [e ::= ....
     (rec e [e_z] [x_pre y_rec e_s])]
  [E ::= ....
     (rec E [e_z] [x_pre y_rec e_s])])

; This is actually call-by-name, because call-by-value requires a dirty hack
; or extra syntax, so far as I can tell.
(define ->val/rec
  (extend-reduction-relation ->val stlc/rec
   [--> (in-hole E (rec z [e_z] [x_pre y_rec e_s]))
        (in-hole E e_z)
        rec-zero]
   [--> (in-hole E (rec (s v) [e_z] [x_pre y_rec e_s]))
        (in-hole E (substitute (substitute e_s x_pre v) y_rec (rec v [e_z] [x_pre y_rec e_s])))
        rec-succ]))

; This is PCF:
(define-extended-language stlc/fix stlc/rec
  [e ::= ....
     (fix e)
     (if0 e e [x e])]
  [E ::= ....
     (fix E)
     (if0 E e [x e])])

(define ->val/fix
  (extend-reduction-relation ->val/rec stlc/fix
   [--> (in-hole E (fix (λ x t e)))
        (in-hole E (substitute e x (fix (λ x t e))))
        fix]
   [--> (in-hole E (if0 z e_z [x e_s]))
        (in-hole E e_z)
        if0-z]
   [--> (in-hole E (if0 (s v) e_z [x e_s]))
        (in-hole E (substitute e_s x v))
        if0-s]))

(define-extended-judgment-form stlc/fix types
  #:mode (types/alt I I O)
  #:contract (types/alt Γ e t)
  
  [(types/alt Γ e nat)
   (types/alt Γ e_z t)
   (types/alt (extend (extend Γ x_pre nat) y_rec t) e_s t)
   ---- rec
   (types/alt Γ (rec e [e_z] [x_pre y_rec e_s]) t)]

  [(types/alt Γ e (-> t t))
   ---- fix
   (types/alt Γ (fix e) t)]

  [(types/alt Γ e nat)
   (types/alt Γ e_z t)
   (types/alt (extend Γ x nat) e_s t)
   ---- if0
   (types/alt Γ (if0 e e_z [x e_s]) t)])
