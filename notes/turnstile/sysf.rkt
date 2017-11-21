#lang turnstile/lang

(extends "stlc.rkt")
(provide all tyλ inst)

(define-binding-type all)

(define-typed-syntax tyλ
  [(_ (tv:id ...) e) ⇐ (~all (tv_in:id ...) τ_in) ≫
   #:fail-unless (stx-length=? #'(tv ...) #'(tv_in ...))
                 (format "Expected ~a bound type variables but got ~a"
                         (stx-length #'(tv_in ...))
                         (stx-length #'(tv ...)))
   #:with τ_renamed (substs #'(tv ...) #'(tv_in ...) #'τ_in)
   [[tv ≫ tv- :: #%type] ... ⊢ e ≫ e- ⇐ τ_renamed]
   ----
   [⊢ (λ- () e-)]]
  [(_ (tv:id ...) e) ≫
   [[tv ≫ tv- :: #%type] ... ⊢ e ≫ e- ⇒ τ]
   ----
   [⊢ (λ- () e-) ⇒ (all (tv- ...) τ)]])

(define-typed-syntax inst
  [(_ e τi:type ...) ≫
   [⊢ e ≫ e- ⇒ (~all (tv:id ...) τ_body)]
   #:with τ (substs #'(τi.norm ...) #'(tv ...) #'τ_body)
   ----
   [⊢ (e-) ⇒ τ]])