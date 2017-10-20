#lang racket/base

(require redex
         "let-nl.rkt")

(provide let-nl/t)

(define-extended-language let-nl/t let-nl/eval
  (t ::=
     int
     str)
  (Γ ::= ([x t] ...)))

(define-metafunction let-nl/t
  extend : Γ x v -> Γ
  [(extend ([x_i t_i] ...) x t)
   ([x t] [x_i t_i] ...)])

(define-metafunction let-nl/t
  lookup : Γ x -> t
  [(lookup ([x_i v_i] ... [x v] [x_j v_j] ...) x)
   v
   (side-condition (not (member (term x) (term (x_i ...)))))])

(define-judgment-form let-nl/t
  #:mode (types I I O)
  #:contract (types Γ e t)
  [---- "nat"
   (types Γ n int)]
  [---- "nil"
   (types Γ nil list)]
  [(types Γ e_1 int)
   (types Γ e_2 list)
   ---- "cons"
   (types Γ (cons e_1 e_2) list)]
  [(types Γ e_1 int)
   (types Γ e_2 int)
   ---- "plus"
   (types Γ (+ e_1 e_2) int)]
  [(types Γ e_1 int)
   (types Γ e_2 int)
   ---- "times"
   (types Γ (* e_1 e_2) int)]
  [(types Γ e list)
   ---- "car"
   (types Γ (car e) int)]
  [(types Γ e list)
   ---- "cdr"
   (types Γ (cdr e) list)]
  [---- "var"
   (types Γ x (lookup Γ x))]
  [(types Γ e_1 t_1)
   (types (extend Γ x t_1) e_2 t_2)
   ---- "let"
   (types Γ (let x e_1 e_2) t_2)])



; type-check : Γ e -> t
(define (type-check Γ e)
  ((term-match/single
    let-nl/t
    [n               (term int)]
    [nil             (term list)]
    [(cons e_1 e_2)  (let ([t_1 (type-check Γ (term e_1))]
                           [t_2 (type-check Γ (term e_2))])
                       
    [(+ e_1 e_2)     (let ([t_1 (type-check Γ (term e_1))]
                           [t_2 (type-check Γ (term e_2))])
                       (unless (equal? t_1 (term int))
                         (error "+: wanted an int, got " t_1))
                       (unless (equal? t_2 (term int))
                         (error "+: wanted an int, got " t_2))
                       (term int))]
    [(* e_1 e_2)     (let ([t_1 (type-check Γ (term e_1))]
                           [t_2 (type-check Γ (term e_2))])
                       (unless (equal? t_1 (term int))
                         (error "*: wanted an int, got " t_1))
                       (unless (equal? t_2 (term int))
                         (error "*: wanted an int, got " t_2))
                       (term int))])
   e))
