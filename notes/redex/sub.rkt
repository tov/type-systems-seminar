#lang racket/base

(provide λsub ->val <: types)

(require redex/reduction-semantics
         (prefix-in stlc: "stlc.rkt")
         "util.rkt")

(define-extended-language λsub stlc:stlc
  (t ::=
     ....
     (Record [f t] ...))
  (e ::=
     ....
     (record [f e] ...)
     (project e f))
  (v ::=
     ....
     (record [f v] ...))
  (E ::=
     ....
     (record [f v] ... [f E] [f e] ...))
  (f g ::= variable-not-otherwise-mentioned))

(define ->val
  (extend-reduction-relation
   stlc:->val
   λsub
   #:domain e
   (--> (in-hole E (project (record [f_i v_i] ... [f v] [f_j v_j] ...) f))
        (in-hole E v)
        prj)))

(define-metafunction λsub
  lookup : Γ x -> t
  [(lookup (extend Γ x t) x)
   t]
  [(lookup (extend Γ y t) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-judgment-form λsub
  #:mode (<: I I)
  #:contract (<: t t)

  [---- nat
   (<: nat nat)]

  [(<: t_21 t_11)
   (<: t_12 t_22)
   ---- arr
   (<: (-> t_11 t_12) (-> t_21 t_22))]

  [---- rec-nil
   (<: (Record [f t] ...) (Record))]

  [(<: t^l t^r)
   (<: (Record [g_j t_j] ... [g_k t_k] ...) (Record [g_i t_i] ...))
   ---- rec-cons
   (<: (Record [g_j t_j] ... [f t^l] [g_k t_k] ...) (Record [f t^r] [g_i t_i] ...))])

(define-extended-judgment-form λsub stlc:types
  #:mode (types I I O)
  #:contract (types Γ e t)

  [(types Γ e_i t_i)
   ...
   ---- record
   (types Γ (record [f_i e_i] ...) (Record [f_i t_i] ...))]

  [(types Γ e (Record [f_i t_i] ... [f t] [f_j t_j] ...))
   ---- project
   (types Γ (project e f) t)]
  
  [(types Γ e_1 (-> t_1 t))
   (types Γ e_2 t_2)
   (<: t_2 t_1)
   ---- app
   (types Γ (ap e_1 e_2) t)])