#lang turnstile/lang

(extends "stlc.rkt"
         #:except vec-ref vec-set! build-vec vec-len)
(provide all tyλ inst
         vec-ref vec-set! build-vec vec-len)

(define-binding-type all)

(define-simple-macro (define-poly-primop name:id defn:expr τ:type)
  (begin
    (define (internal) defn)
    (define-primop name internal τ)))

(define-poly-primop vec-ref vector-ref (all (X) (-> (Vec X) Int X)))
(define-poly-primop vec-set! vector-set! (all (X) (-> (Vec X) Int X Unit)))
(define-poly-primop build-vec build-vector (all (X) (-> Int (-> Int X) (Vec X))))
(define-poly-primop vec-len vector-length (all (X) (-> (Vec X) Int)))

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