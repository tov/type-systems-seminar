#lang turnstile/lang

(extends "stlc.rkt" #:except #%datum record project - zero?)
(provide (type-out Top)
         ; (type-out Bot)
         zero?
         (type-out Num) -/Num
         -/Int
         (type-out Float) -/Float
         record project
         (rename-out [datum #%datum])
         (for-syntax current-sub? subs?))

(require (prefix-in stlc: "stlc.rkt"))

(define-base-type Top)
(define-base-type Bot)
(define-base-type Num)
(define-base-type Float)

(define-primop zero? (-> Num Bool))
(define-primop -/Num -- (-> Num Num Num))
(define-primop -/Int -- (-> Int Int Int))
(define-primop -/Float -- (-> Float Float Float))

(define-typed-syntax datum
  [(_ . z:integer) ≫
   #:when (exact-integer? (syntax-e #'z))
   ----
   [⊢ (#%datum- . z) ⇒ Int]]
  [(_ . f:number) ≫
   #:when (flonum? (syntax-e #'f))
   ----
   [⊢ (#%datum- . f) ⇒ Float]]
  [(_ . n:number) ≫
   ----
   [⊢ (#%datum- . n) ⇒ Num]]
  [(_ . otherwise) ≫
   ----
   (≻ (stlc:#%datum . otherwise))])

(begin-for-syntax
  (define (sub? t1 t2)
    (define τ1 ((current-type-eval) t1))
    (define τ2 ((current-type-eval) t2))
    (or ((current-type=?) τ1 τ2)
        (Bot? τ1)
        (Top? τ2)
        (syntax-parse (list τ1 τ2)
          [(~Int ~Num) #t]
          [(~Float ~Num) #t]
          [((~-> τi1 ... τo1) (~-> τi2 ... τo2))
           (and (subs? #'(τi2 ...) #'(τi1 ...))
                ((current-sub?) #'τo1 #'τo2))]
          [_ #f])))
  (define current-sub? (make-parameter sub?))
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))

  (define (meet t1 t2)
    (let ([τ1 ((current-type-eval) t1)]
          [τ2 ((current-type-eval) t2)])
      (cond
        [((current-sub?) τ1 τ2) τ1]
        [((current-sub?) τ2 τ1) τ2]
        [else
         (syntax-parse (list τ1 τ2)
           [((~-> τi1 ... τo1) (~-> τi2 ... τo2))
            #:when (stx-length=? #'(τi1 ...) #'(τi2 ...))
            #:with (τi3 ...) #'((⊔ τi1 τi2) ...)
            #:with τo3 #'(⊓ τo1 τo2)
            #'(-> τi3 ... τo3)]
           [else #'Bot])])))

  (define (join t1 t2)
    (define τ1 ((current-type-eval) t1))
    (define τ2 ((current-type-eval) t2))
    (cond
      [((current-sub?) τ1 τ2) τ2]
      [((current-sub?) τ2 τ1) τ1]
      [else
       (syntax-parse (list τ1 τ2)
         [(~Int ~Float) #'Num]
         [(~Float ~Int) #'Num]
         [((~-> τi1 ... τo1) (~-> τi2 ... τo2))
          #:when (stx-length=? #'(τi1 ...) #'(τi2 ...))
          #:with (τi3 ...) #'((⊓ τi1 τi2) ...)
          #:when (stx-andmap (λ (τ) (not (Bot? τ))) #'(τi3 ...))
          #:with τo3 #'(⊔ τo1 τo2)
          #'(-> τi3 ... τo3)]
         [else #'Top])]))
  (current-join join))

(define-syntax ⊓
  (syntax-parser
    [(_ τ1 τ2 ...)
     (for/fold ([τ1 ((current-type-eval) #'τ1)])
               ([τ2 (in-list (stx-map (current-type-eval) #'[τ2 ...]))])
       (meet τ1 τ2))]))

(define-typed-syntax record
  [(_ [label:id ei:expr] ...) ≫
   [⊢ ei ≫ ei- ⇒ τi] ...
   ----
   [⊢ (list (cons 'label ei-) ...) ⇒ (Record [label τi] ...)]])

(begin-for-syntax
  (define (record-lookup label a-list)
    (cond
      [(assoc label
              (map syntax->list (syntax->list a-list))
              free-identifier=?)
       => cadr]
      [else
       (type-error #:src a-list
                   #:msg "Expected record with field ~a" label)])))

(define-typed-syntax project
  [(_ e:expr label:id) ≫
   [⊢ e ≫ e- ⇒ (~Record [label_i:id τi:type] ...)]
   #:with τ (record-lookup #'label #'([label_i τi] ...))
   ----
   [⊢ (cdr (assq 'label e-)) ⇒ τ]])