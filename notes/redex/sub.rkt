#lang racket/base

(provide λsub ->val <: types <:~> types~>)

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

  [(<: t_l t_r)
   (<: (Record [g_j t_j] ... [g_k t_k] ...) (Record [g_i t_i] ...))
   ---- rec-cons
   (<: (Record [g_j t_j] ... [f t_l] [g_k t_k] ...) (Record [f t_r] [g_i t_i] ...))])

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

(define-judgment-form λsub
  #:mode (<:~> I I O)
  #:contract (<:~> t t e)

  [---- nat
   (<:~> nat nat (λ n nat n))]

  [(<:~> t_21 t_11 e_1)
   (<:~> t_12 t_22 e_2)
   ---- arr
   (<:~> (-> t_11 t_12) (-> t_21 t_22) (λ h (-> t_11 t_12) (λ n t_21 (ap e_2 (ap h (ap e_1 n))))))]

  [---- rec-nil
   (<:~> (Record [f t] ...) (Record) (λ r (Record [f t] ...) (record)))]

  [(<:~> t_l t_r e_1)
   (<:~> (Record [g_j t_j] ... [g_k t_k] ...) (Record [g_i t_i] ...) e_2)
   ---- rec-cons
   (<:~> (Record [g_j t_j] ... [f t_l] [g_k t_k] ...) (Record [f t_r] [g_i t_i] ...) (λ r (Record [g_j t_j] ... [f t_l] [g_k t_k] ...)
                                                                                       (ap (λ s (Record [g_i t_i] ...)
                                                                                             (record [f (e_1 (project r f))]
                                                                                                     [g_i (project s g_i)] ...))
                                                                                           (e_2 (record [g_j (project r g_j)] ...
                                                                                                        [g_k (project r g_k)] ...)))))])

(define-judgment-form λsub
  #:mode (types~> I I O O)
  #:contract (types~> Γ e t e)

  [---- var
   (types~> Γ x (lookup Γ x) x)]

  [---- zero
   (types~> Γ z nat z)]

  [(types~> Γ e nat e_1)
   ---- succ
   (types~> Γ (s e) nat (s e_1))]

  [(types~> Γ e t e_1) ...
   ---- record
   (types~> Γ (record [f e] ...) (Record [f t] ...) (record [f e_1] ...))]

  [(types~> Γ e (Record [f_i t_i] ... [f t] [f_j t_j] ...) e_1)
   ---- project
   (types~> Γ (project e f) t (project e_1 f))]
  
  [(types~> (extend Γ x t_1) e t_2 e_1)
   ---- abs
   (types~> Γ (λ x t_1 e) (-> t_1 t_2) (λ x t_1 e_1))]

  [(types~> Γ e_1 (-> t_1 t) e_11)
   (types~> Γ e_2 t_2 e_21)
   (<:~> t_2 t_1 e_c)
   ---- app
   (types~> Γ (ap e_1 e_2) t (ap e_11 (ap e_c e_21)))])