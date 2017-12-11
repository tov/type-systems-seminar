#lang turnstile/lang

(extends "stlc.rkt"
         #:except #%app vec-ref vec-set! build-vec vec-len)
(provide All tyλ inst
         vec-ref vec-set! build-vec vec-len
         (rename-out [app #%app])
         error!)

(define-binding-type All)

(define-simple-macro (define-poly-primop name:id defn:expr τ:type)
  (begin
    (define (internal) defn)
    (define-primop name internal τ)))

(define-poly-primop vec-ref vector-ref (All (X) (-> (Vec X) Int X)))
(define-poly-primop vec-set! vector-set! (All (X) (-> (Vec X) Int X Unit)))
(define-poly-primop build-vec build-vector (All (X) (-> Int (-> Int X) (Vec X))))
(define-poly-primop vec-len vector-length (All (X) (-> (Vec X) Int)))

(define-poly-primop error! error (All (X) (-> String X)))

(define-typed-syntax tyλ
  [(_ (tv:id ...) e) ⇐ (~All (tv_in:id ...) τ_in) ≫
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
   [⊢ (λ- () e-) ⇒ (All (tv- ...) τ)]])

(define-typed-syntax inst
  [(_ e τi:type ...) ≫
   [⊢ e ≫ e- ⇒ (~All (tv:id ...) τ_body)]
   #:fail-unless (stx-length=? #'(τi ...) #'(tv ...))
                 (format "Got ~a where ~a type parameter(s) expected"
                         (map type->str (syntax->list #'(τi ...)))
                         (stx-length #'(tv ...)))
   #:with τ (substs #'(τi.norm ...) #'(tv ...) #'τ_body)
   ----
   [⊢ (e-) ⇒ τ]])

(require (prefix-in stlc: (only-in "stlc.rkt")))

(define-typed-syntax app
  [(_ e τi-raw ...) ≫
   [⊢ e ≫ e- ⇒ (~All (tv:id ...) τ_body)]
   #:with (τi:type ...) #'(τi-raw ...)
   #:fail-unless (stx-length=? #'(τi ...) #'(tv ...))
                 (format "Got ~a where ~a type parameter(s) expected"
                         (map type->str (syntax->list #'(τi ...)))
                         (stx-length #'(tv ...)))
   #:with τ (substs #'(τi.norm ...) #'(tv ...) #'τ_body)
   ----
   [⊢ (e-) ⇒ τ]]
  [(_ . stx) ≫
   ----
   [≻ (stlc:#%app . stx)]])
