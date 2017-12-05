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
         (for-syntax current-sub? subs? join-rows meet-rows))

(require "stx-utils.rkt"
         (prefix-in stlc: "stlc.rkt")
         racket/set)

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
  (define (not-bot? τ)
    (not (Bot? ((current-type-eval) τ))))
  
  (define (sub-row? row1* row2*)
    (define row1 (map syntax->list (syntax->list row1*)))
    (define row2 (map syntax->list (syntax->list row2*)))
    (for/and [(binding2 (in-list row2))]
      (define label2 (car binding2))
      (define τ2 (cadr binding2))
      (cond
        [(assoc label2 row1 free-identifier=?)
         =>
         (λ (binding1) ((current-sub?) (cadr binding1) τ2))]
        [else
         #false])))
    
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
          [((~Record [l1 τ1] ...) (~Record [l2 τ2] ...))
           (sub-row? #'([l1 τ1] ...) #'([l2 τ2] ...))]
          [_ #f])))
  
  (define current-sub? (make-parameter sub?))
  
  (current-typecheck-relation sub?)
  
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))

  (define (meet-rows row1* row2*)
    (define row1 (map syntax->list (syntax->list row1*)))
    (define row2 (map syntax->list (syntax->list row2*)))
    (define ids1 (map car row1))
    (define ids2 (map car row2))
    (append
     (for/list ([id (free-id-set-intersect ids1 ids2)])
       (define τ1 (cadr (assoc id row1 free-identifier=?)))
       (define τ2 (cadr (assoc id row2 free-identifier=?)))
       (define τ-meet ((current-meet) τ1 τ2))
       (list id τ-meet))
     (for/list ([id (free-id-set-difference ids1 ids2)])
       (assoc id row1 free-identifier=?))
     (for/list ([id (free-id-set-difference ids2 ids1)])
       (assoc id row2 free-identifier=?))))
 
  (define (join-rows row1* row2*)
    (define row1 (map syntax->list (syntax->list row1*)))
    (define row2 (map syntax->list (syntax->list row2*)))
    (define ids1 (map car row1))
    (define ids2 (map car row2))
    (for/list ([id (free-id-set-intersect ids1 ids2)])
      (define τ1 (cadr (assoc id row1 free-identifier=?)))
      (define τ2 (cadr (assoc id row2 free-identifier=?)))
      (define τ-join ((current-join) τ1 τ2))
      (list id τ-join)))

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
            #:when (not-bot? #'τo3)
            #'(-> τi3 ... τo3)]
           [((~Record [l1 τ1] ...) (~Record [l2 τ2] ...))
            #:with ([l3 τ3] ...) (meet-rows #'([l1 τ1] ...) #'([l2 τ2] ...))
            #:when (stx-andmap not-bot? #'(τ3 ...))
            #'(Record [l3 τ3] ...)]
           [else #'Bot])])))
  (current-meet meet)

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
          #:when (stx-andmap not-bot? #'(τi3 ...))
          #:with τo3 #'(⊔ τo1 τo2)
          #'(-> τi3 ... τo3)]
         [((~Record [l1 τ1] ...) (~Record [l2 τ2] ...))
          #:with ([l3 τ3] ...) (join-rows #'([l1 τ1] ...) #'([l2 τ2] ...))
          #'(Record [l3 τ3] ...)]
         [else #'Top])]))
  (current-join join))

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