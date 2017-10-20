#lang racket/base

(require redex
         "let-nl.rkt")

(provide let-nl/t)

(define-extended-language let-nl/t let-nl/eval
  (t ::=
     int
     list)
  (Γ ::= ([x t] ...)))

(default-language let-nl/t)

(define-metafunction let-nl/t
  extend : Γ x t -> Γ
  [(extend ([x_i t_i] ...) x t)
   ([x t] [x_i t_i] ...)])

(define-metafunction let-nl/t
  lookup : Γ x -> t
  [(lookup ([x_i t_i] ... [x t] [x_j t_j] ...) x)
   t
   (side-condition (not (member (term x) (term (x_i ...)))))])

(define-judgment-form let-nl/t
  #:mode (types I I O)
  #:contract (types Γ e t)
  [---- nat
   (types Γ n int)]
  [---- nil
   (types Γ nil list)]
  [(types Γ e_1 int)
   (types Γ e_2 list)
   ---- cons
   (types Γ (cons e_1 e_2) list)]
  [(types Γ e_1 int)
   (types Γ e_2 int)
   ---- plus
   (types Γ (+ e_1 e_2) int)]
  [(types Γ e_1 int)
   (types Γ e_2 int)
   ---- times
   (types Γ (* e_1 e_2) int)]
  [(types Γ e list)
   ---- car
   (types Γ (car e) int)]
  [(types Γ e list)
   ---- cdr
   (types Γ (cdr e) list)]
  [---- var
   (types Γ x (lookup Γ x))]
  [(types Γ e_1 t_1)
   (types (extend Γ x t_1) e_2 t_2)
   ---- let
   (types Γ (let x e_1 e_2) t_2)])

(define-syntax-rule (let-nl-match scrutinee [patt expr ...] ...)
  ((term-match/single let-nl/t
    [patt (begin expr ...)]
    ...)
   scrutinee))

(define-syntax-rule (assert-type who patt expr then ...)
  (let-nl-match expr
    [patt   (void) then ...]
    [t      (error 'who ": wanted " 'patt ", got " (term t))]))
    
; type-check : Γ e -> t
(define (type-check Γ e)
  (let-nl-match e
    [n               (term int)]
    [nil             (term list)]
    [(cons e_1 e_2)  (assert-type cons int (type-check Γ (term e_1)))
                     (assert-type cons list (type-check Γ (term e_2)))
                     (term list)]
    [(+ e_1 e_2)     (assert-type + int (type-check Γ (term e_1)))
                     (assert-type + int (type-check Γ (term e_2)))
                     (term int)]
    [(* e_1 e_2)     (assert-type * int (type-check Γ (term e_1)))
                     (assert-type * int (type-check Γ (term e_2)))
                     (term int)]
    [(car e_1)       (assert-type car list (type-check Γ (term e_1)))
                     (term int)]
    [(cdr e_1)       (assert-type cdr list (type-check Γ (term e_1)))
                     (term list)]
    [x               (term (lookup ,Γ x))]
    [(let x e_1 e_2) (define-term t_1 ,(type-check Γ (term e_1)))
                     (type-check (term (extend ,Γ x t_1)) (term e_2))]))

(define-syntax-rule (test-type-check expr type)
  (test-equal (type-check (term ()) (term expr))
              (term type)))

(test-type-check 5 int)

(test-type-check (+ 5 6) int)

(test-type-check (car nil) int)
            
(test-type-check (let x (cons 4 nil) (cdr (cdr x)))
                 list)

