#lang turnstile/lang

(provide ->
         Unit void ignore begin
         Bool not if
         Int - zero? positive? negative? random
         Vec vec vec-ref vec-set! build-vec vec-len
         ann
         let let* letrec
         λ (rename-out [λ lam])
         define-type-alias define
         (rename-out [datum #%datum]
                     [app #%app]))

; Functions can have 0 or more arguments:
(define-type-constructor -> #:arity >= 1)

(define-base-type Unit)
(define-primop void (-> Unit))

(define-base-type Bool)
(define-primop not (-> Bool Bool))

(define-base-type Int)
(define-primop - (-> Int Int Int))
(define-primop zero? (-> Int Bool))
(define-primop positive? (-> Int Bool))
(define-primop negative? (-> Int Bool))
(define-primop random (-> Int Int))

(define-type-constructor Vec #:arity = 1)

(define-typed-syntax λ
  [(_ ([x:id τ_in:type] ...) e:expr) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   ----
   [⊢ (λ- (x- ...) e-) ⇒ (-> τ_in.norm ... τ_out)]]
  [(λ (x:id ...) e:expr) ⇐ (~-> τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ----
   [⊢ (λ- (x- ...) e-)]])

(define-typed-syntax (app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~-> τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (format "arity mismatch, expected ~a args, given ~a"
                        (stx-length #'[τ_in ...]) #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  ----
  [⊢ (#%app- e_fn- e_arg- ...) ⇒ τ_out])
  
(define-typed-syntax (ann e:expr τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  ----
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax datum
  [(_ . i:integer) ≫
   ----
   [⊢ (#%datum- . i) ⇒ Int]]
  [(_ . b:boolean) ≫
   ----
   [⊢ (#%datum- . b) ⇒ Bool]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x
                        #:msg "Unsupported literal: ~v" #'x)]])

(define-typed-syntax vec
  [(_ e1 ei ...) ≫
   [⊢ e1 ≫ e1- ⇒ τ]
   [⊢ ei ≫ ei- ⇐ τ] ...
   ----
   [⊢ (vector- e1- ei- ...) ⇒ (Vec τ)]]
  [(_ ei ...) ⇐ (~Vec τ) ≫
   [⊢ ei ≫ ei- ⇐ τ] ...
   ----
   [⊢ (vector- ei- ...)]])

(define-typed-syntax vec-ref
  [(_ e_vec e_ix) ≫
   [⊢ e_vec ≫ e_vec- ⇒ (~Vec τ)]
   [⊢ e_ix ≫ e_ix- ⇐ Int]
   ----
   [⊢ (vector-ref- e_vec- e_ix-) ⇒ τ]])

(define-typed-syntax vec-set!
  [(_ e_vec e_ix e_val) ≫
   [⊢ e_vec ≫ e_vec- ⇒ (~Vec τ)]
   [⊢ e_ix ≫ e_ix- ⇐ Int]
   [⊢ e_val ≫ e_val- ⇐ τ]
   ----
   [⊢ (vector-set! e_vec- e_ix- e_val-) ⇒ Unit]])

(define-typed-syntax build-vec
  [(_ e_size e_fn) ≫
   [⊢ e_size ≫ e_size- ⇐ Int]
   [⊢ e_fn ≫ e_fn- ⇒ (~-> ~Int τ)]
   ----
   [⊢ (build-vector- e_size e_fn) ⇒ (Vec τ)]])

(define-typed-syntax vec-len
  [(_ e_vec) ≫
   [⊢ e_vec ≫ e_vec- ⇒ (~Vec τ)]
   ----
   [⊢ (vector-length- e_vec-) ⇒ Int]])

(define-typed-syntax ignore
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ]
   ----
   [⊢ (begin- e- (void)) ⇒ Unit]])

(define-typed-syntax begin
  [(_ e_i ... e_n) ≫
   [⊢ e_i ≫ e_i- ⇐ Unit] ...
   [⊢ e_n ≫ e_n- ⇒ τ]
   ----
   [⊢ (begin- e_i- ... e_n-) ⇒ τ]]
  [(_ e_i ... e_n) ⇐ τ ≫
   [⊢ e_i ≫ e_i- ⇐ Unit] ...
   [⊢ e_n ≫ e_n- ⇐ τ]
   ----
   [⊢ (begin- e_i- ... e_n-)]])

(define-typed-syntax if
  [(_ e1 e2 e3) ≫
   [⊢ e1 ≫ e1- ⇐ Bool]
   [⊢ e2 ≫ e2- ⇒ τ]
   [⊢ e3 ≫ e3- ⇐ τ]
   ----
   [⊢ (if- e1- e2- e3-) ⇒ τ]])

(define-typed-syntax let
  [(_ ([x:id rhs:expr] ...) body:expr ...+) ≫
   [⊢ rhs ≫ rhs- ⇒ τ_rhs] ...
   [[x ≫ x- : τ_rhs] ... ⊢ (begin body ...) ≫ body- ⇒ τ_body]
   ----
   [⊢ (let- ([x- rhs-] ...) body-) ⇒ τ_body]]
  [(_ ([x:id rhs:expr] ...) body:expr ...+) ⇐ τ ≫
   [⊢ rhs ≫ rhs- ⇒ τ_rhs] ...
   [[x ≫ x- : τ_rhs] ... ⊢ (begin body ...) ≫ body- ⇐ τ]
   ----
   [⊢ (let- ([x- rhs-] ...) body-)]])

(define-typed-syntax let*
  [(_ () body:expr ...+) ≫
   ----
   [≻ (begin body ...)]]
  [(_ ([x:id rhs:expr] [x_i:id rhs_i:expr] ...) body ...+) ≫
   ----
   [≻ (let ([x rhs]) (let* ([x_i rhs_i] ...) body ...))]])

(define-typed-syntax letrec
  [(_ ([x:id τ:type rhs:expr] ...) body ...+) ≫
   [[x ≫ x- : τ.norm] ... ⊢ [rhs ≫ rhs- ⇐ τ] ...
                             [(begin body ...) ≫ body- ⇒ τ_body]]
   ----
   [⊢ (letrec- ([x- rhs-] ...) body-) ⇒ τ_body]]
  [(_ ([x:id τ:type rhs:expr] ...) body ...+) ⇐ τ_body ≫
   [[x ≫ x- : τ.norm] ... ⊢ [rhs ≫ rhs- ⇐ τ] ...
                             [(begin body ...) ≫ body- ⇐ τ_body]]
   ----
   [⊢ (letrec- ([x- rhs-] ...) body-)]])

(define-syntax define-type-alias
  (syntax-parser
    [(_ alias:id τ:any-type)
     #'(define-syntax- alias
         (make-variable-like-transformer #'τ))]
    [(_ (f:id x:id ...) ty)
     #'(define-syntax- (f stx)
         (syntax-parse stx
           [(_ x ...)
            #:with τ:any-type #'ty
            #'τ.norm]))]))

(define-typed-syntax define
  [(_ x:id τ:type e:expr) ≫
   #:with y (generate-temporary #'x)
   ----
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
        (define- y (ann e τ.norm)))]]
  [(_ x:id e:expr) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- (assign-type #'y #'τ))
   ----
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  [(_ (f [x ty] ... (~datum ->) ty_out) e ...+) ≫
   #:with f- (add-orig (generate-temporary #'f) #'f)
   ----
   [≻ (begin-
        (define-syntax- f
          (make-rename-transformer (⊢ f- : (-> ty ... ty_out))))
        (define- f-
          (λ ([x ty] ...)
            (ann (begin e ...) ty_out))))]])