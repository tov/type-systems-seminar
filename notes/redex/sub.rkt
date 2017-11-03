#lang racket/base

(provide λsub ->val <: types <:~> types~>)

(require redex/reduction-semantics
         (prefix-in stlc: "stlc.rkt")
         "util.rkt")

(define-extended-language λsub stlc:stlc
  (t ::=
     ....
     (Record [l t] ...))
  (e ::=
     ....
     (record [l e] ...)
     (project e l))
  (v ::=
     ....
     (record [l v] ...))
  (E ::=
     ....
     (record [l v] ... [l E] [l e] ...))
  (l m ::= variable-not-otherwise-mentioned))

(define ->val
  (extend-reduction-relation
   stlc:->val
   λsub
   #:domain e
   (--> (in-hole E (project (record [l_i v_i] ... [l v] [l_j v_j] ...) l))
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
   (<: (Record [l t] ...) (Record))]

  [(<: t_l t_r)
   (<: (Record [m_j t_j] ... [m_k t_k] ...) (Record [m_i t_i] ...))
   ---- rec-cons
   (<: (Record [m_j t_j] ... [l t_l] [m_k t_k] ...) (Record [l t_r] [m_i t_i] ...))])

(define-extended-judgment-form λsub stlc:types
  #:mode (types I I O)
  #:contract (types Γ e t)

  [(types Γ e_i t_i) ...
   ---- record
   (types Γ (record [l_i e_i] ...) (Record [l_i t_i] ...))]

  [(types Γ e (Record [l_i t_i] ... [l t] [l_j t_j] ...))
   ---- project
   (types Γ (project e l) t)]
  
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
   (<:~> (Record [l t] ...) (Record) (λ r (Record [l t] ...) (record)))]

  [(<:~> t_l t_r e_1)
   (<:~> (Record [m_j t_j] ... [m_k t_k] ...) (Record [m_i t_i] ...) e_2)
   ---- rec-cons
   (<:~> (Record [m_j t_j] ... [l t_l] [m_k t_k] ...) (Record [l t_r] [m_i t_i] ...) (λ r (Record [m_j t_j] ... [l t_l] [m_k t_k] ...)
                                                                                       (ap (λ s (Record [m_i t_i] ...)
                                                                                             (record [l (e_1 (project r l))]
                                                                                                     [m_i (project s m_i)] ...))
                                                                                           (e_2 (record [m_j (project r m_j)] ...
                                                                                                        [m_k (project r m_k)] ...)))))])

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
   (types~> Γ (record [l e] ...) (Record [l t] ...) (record [l e_1] ...))]

  [(types~> Γ e (Record [l_i t_i] ... [l t] [l_j t_j] ...) e_1)
   ---- project
   (types~> Γ (project e l) t (project e_1 l))]
  
  [(types~> (extend Γ x t_1) e t_2 e_1)
   ---- abs
   (types~> Γ (λ x t_1 e) (-> t_1 t_2) (λ x t_1 e_1))]

  [(types~> Γ e_1 (-> t_1 t) e_11)
   (types~> Γ e_2 t_2 e_21)
   (<:~> t_2 t_1 e_c)
   ---- app
   (types~> Γ (ap e_1 e_2) t (ap e_11 (ap e_c e_21)))])