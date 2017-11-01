#lang racket/base

(require redex/reduction-semantics
         "let-zl.rkt")

(provide let-zl/t types types*)

(define-extended-language let-zl/t let-zl/eval
  (t ::=
     int
     list)
  (Γ ::=
     •
     (extend Γ x t)))

(default-language let-zl/t)

(define-metafunction let-zl/t
  lookup : Γ x -> t
  [(lookup (extend Γ x t) x)
   t]
  [(lookup (extend Γ y t) x)
   (lookup Γ x)
   (side-condition (not (equal? (term x) (term y))))])

(define-judgment-form let-zl/t
  #:mode (types I I O)
  #:contract (types Γ e t)
  [---- int
   (types Γ z int)]
  [---- nil
   (types Γ nil list)]
  [(types Γ e_1 int) (types Γ e_2 list)
   ---- cons
   (types Γ (cons e_1 e_2) list)]
  [(types Γ e_1 int) (types Γ e_2 int)
   ---- plus
   (types Γ (+ e_1 e_2) int)]
  [(types Γ e_1 int) (types Γ e_2 int)
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

; This is a broken version of `types` that doesn't use an environment:
(define-judgment-form let-zl/t
  #:mode (types* I O)
  #:contract (types* e t)
  [---- int
   (types* z int)]
  [---- nil
   (types* nil list)]
  [(types* e_1 int) (types* e_2 list)
   ---- cons
   (types* (cons e_1 e_2) list)]
  [(types* e_1 int) (types* e_2 int)
   ---- plus
   (types* (+ e_1 e_2) int)]
  [(types* e_1 int) (types* e_2 int)
   ---- times
   (types* (* e_1 e_2) int)]
  [(types* e list)
   ---- car
   (types* (car e) int)]
  [(types* e list)
   ---- cdr
   (types* (cdr e) list)])

(define-syntax-rule (let-zl-match scrutinee [patt expr ...] ...)
  ((term-match/single let-zl/t
    [patt (begin expr ...)]
    ...)
   scrutinee))

(define-syntax-rule (assert-type who patt expr then ...)
  (let-zl-match expr
    [patt   (void) then ...]
    [t      (error 'who ": wanted " 'patt ", got " (term t))]))
    
; type-check : Γ e -> t
(define (type-check Γ e)
  (let-zl-match e
    [z               (term int)]
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
  (test-equal (type-check (term •) (term expr))
              (term type)))

(test-type-check 5 int)

(test-type-check (+ 5 6) int)

(test-type-check (car nil) int)
            
(test-type-check (let x (cons 4 nil) (cdr (cdr x)))
                 list)

