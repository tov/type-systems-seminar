#lang typed/racket

(require/typed
 racket/base
 [(<= racket/base:<=l) (All (α) (-> (U (Pairof Val Val) Boolean) Val α))]
 [(<= racket/base:<=r) (All (α) (-> Val (U (Pairof Val Val) Boolean) α))]
 [(+ racket/base:+l) (All (α) (-> Val (U (Pairof Val Val) Boolean) α))]
 [(+ racket/base:+r) (All (α) (-> (U (Pairof Val Val) Boolean) Val α))]
 [(car racket/base:car) (All (α) (-> (U Real Boolean) α))]
 [(cdr racket/base:cdr) (All (α) (-> (U Real Boolean) α))]
 [exn:fail:contract:variable-id (-> exn:fail:contract:variable Symbol)])

(define-type Expr (U Real Boolean sum less bind ifte String
                     (Pairof Expr Expr) hd tl))
(define-type Val (U Real Boolean (Pairof Val Val)))
(struct sum ([lhs : Expr] [rhs : Expr]) #:transparent)
(struct less ([lhs : Expr] [rhs : Expr]) #:transparent)
(struct bind ([var : String] [thn : Expr] [els : Expr]) #:transparent)
(struct ifte ([tst : Expr] [thn : Expr] [els : Expr]) #:transparent)
(struct hd ([pr : Expr]) #:transparent)
(struct tl ([pr : Expr]) #:transparent)

(: letzl-eval (-> Expr Val))
(define (letzl-eval e)
  (match e
    [(? real?) e]
    [(? boolean?) e]
    [(? string?) (error 'eval "free variable: ~a" e)]
    [(sum lhs rhs)
     (define lhs-v (letzl-eval lhs))
     (define rhs-v (letzl-eval rhs))
     (cond
       [(and (real? lhs-v) (real? rhs-v))
        (+ lhs-v rhs-v)]
       [else
        (if (real? lhs-v)
            (racket/base:+l lhs-v rhs-v)
            (racket/base:+r lhs-v rhs-v))])]
    [(less lhs rhs)
     (define lhs-v (letzl-eval lhs))
     (define rhs-v (letzl-eval rhs))
     (cond
       [(and (real? lhs-v) (real? rhs-v))
        (<= lhs-v rhs-v)]
       [else
        (if (real? lhs-v)
            (racket/base:<=r lhs-v rhs-v)
            (racket/base:<=l lhs-v rhs-v))])]
    [(bind var rhs body)
     (letzl-eval (subst var (letzl-eval rhs) body))]
    [(ifte tst thn els)
     (define tst-v (letzl-eval tst))
     (cond
       [(boolean? tst-v)
        (if tst-v
            (letzl-eval thn)
            (letzl-eval els))]
       [else (error 'eval "if got a non-boolean in the test position")])]
    [(cons hd tl) (cons (letzl-eval hd) (letzl-eval tl))]
    [(hd pr)
     (define v (letzl-eval pr))
     (if (pair? v)
         (car v)
         (racket/base:car v))]
    [(tl pr)
     (define v (letzl-eval pr))
     (if (pair? v)
         (cdr v)
         (racket/base:cdr v))]))

(: subst (-> String Val Expr Expr))
(define (subst x v e)
  (match e
    [(? real?) e]
    [(? boolean?) e]
    [(? string?) (if (equal? x e) v e)]
    [(sum lhs rhs) (sum (subst x v lhs) (subst x v rhs))]
    [(less lhs rhs) (less (subst x v lhs) (subst x v rhs))]
    [(bind y rhs body)
     (if (equal? x y)
         (bind y (subst x v rhs) body)
         (bind y (subst x v rhs) (subst x v body)))]
    [(ifte tst thn els)
     (ifte (subst x v tst)
           (subst x v thn)
           (subst x v els))]
    [(cons hd tl)
     (cons (subst x v hd)
           (subst x v tl))]
    [(hd e) (hd (subst x v e))]
    [(tl e) (tl (subst x v e))]))

(: letzl-safe-eval (-> Expr (U Val String)))
(define (letzl-safe-eval expr)
  (with-handlers ([exn:fail? exn-message])
    (letzl-eval expr)))

(define ns (make-base-namespace))

(: racket-safe-eval (-> Expr (U Val String)))
(define (racket-safe-eval expr)
  (parameterize ([current-namespace ns])
    (with-handlers ([exn:fail:contract:variable?
                     (λ ([exn : exn:fail:contract:variable])
                       (define str
                         (~a (exn:fail:contract:variable-id
                              exn)))
                       (format "eval: free variable: ~a"
                               (regexp-replace #rx"^x" str "")))]
                    [exn:fail? exn-message])
      (call-with-values (λ () (eval (to-racket expr)))
                        (λ x
                          (unless (pair? x) (error 'impossible))
                          (cast (car x) Val))))))

(: to-racket (-> Expr Any))
(define (to-racket e)
  (match e
    [(? real?) e]
    [(? boolean?) e]
    [(? string?) (string->symbol (~a "x" e))]
    [(sum lhs rhs) `(+ ,(to-racket lhs) ,(to-racket rhs))]
    [(less lhs rhs) `(<= ,(to-racket lhs) ,(to-racket rhs))]
    [(bind y rhs body)
     `(let ([,(string->symbol (~a "x" y)) ,(to-racket rhs)])
        ,(to-racket body))]
    [(ifte tst thn els)
     `(let ([t ,(to-racket tst)])
        (unless (boolean? t)
          (error 'eval "if got a non-boolean in the test position"))
        (if t
            ,(to-racket thn)
            ,(to-racket els)))]
    [(cons e1 e2) `(cons ,(to-racket e1) ,(to-racket e2))]
    [(hd e) `(car ,(to-racket e))]
    [(tl e) `(cdr ,(to-racket e))]))

(define-syntax-rule
  (random-case e ...)
  ((random-item (list (λ () e) ...))))

(: random-item (All (a) (-> (Listof a) a)))
(define (random-item choices)
  (list-ref choices (random (length choices))))

(: random-bool (-> Boolean))
(define (random-bool) (random-item (list #f #t)))

(: random-var (-> (Setof String) String))
(define (random-var vars)
  (if (or (set-empty? vars)
          (zero? (random 10)))
      (random-string)
      (random-item (set->list vars))))

(: random-string (-> String))
(define (random-string) (apply string (random-list-of-chars)))

(: random-list-of-chars (-> (Listof Char)))
(define (random-list-of-chars)
  (if (zero? (random 3))
      (list (random-char))
      (cons (random-char) (random-list-of-chars))))

(: random-char (-> Char))
(define (random-char) (random-item (list #\a #\b #\c #\τ)))

(: random-real (-> Real))
(define (random-real) (random-item (list -1 1.0 -0.0 5 3/2)))

(: random-expr (-> Natural (Setof String) Expr))
(define (random-expr depth vars)
  (cond
    [(zero? depth)
     (random-case
      (random-real)
      (random-bool)
      (random-var vars))]
    [else
     (random-case
      (random-real)
      (random-bool)
      (random-var vars)
      (sum (random-expr (- depth 1) vars)
           (random-expr (- depth 1) vars))
      (less (random-expr (- depth 1) vars)
            (random-expr (- depth 1) vars))
      (let ([x (random-string)])
        (bind x
              (random-expr (- depth 1) vars)
              (random-expr (- depth 1) (set-add vars x))))
      (ifte (random-expr (- depth 1) vars)
            (random-expr (- depth 1) vars)
            (random-expr (- depth 1) vars))
      (cons (random-expr (- depth 1) vars)
            (random-expr (- depth 1) vars))
      (hd (random-expr (- depth 1) vars))
      (tl (random-expr (- depth 1) vars)))]))

(: check-evals (-> Expr Void))
(define (check-evals expr)
  (define vr (racket-safe-eval expr))
  (define vl (letzl-safe-eval expr))
  (unless (equal? vr vl)
    (error 'different!
           "\n  ~a\n  produced different results (racket first, letzl second)\n   ~a\n   ~a"
           (regexp-replace #rx"\n" (pretty-format expr) "\n  ")
           (pretty-format vr)
           (pretty-format vl))))

(for ([x (in-range 100)])
  (check-evals (random-expr 4 (set))))
