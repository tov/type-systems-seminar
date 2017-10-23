#lang racket/base

(provide define-lifted-metafunction)

(require redex/reduction-semantics
         (for-syntax racket/base
                     syntax/parse))

(define-syntax (define-lifted-metafunction stx)
  (syntax-parse stx #:datum-literals (-> :)
    [(_ lang:expr meta-fun:id : dom:id ...+ -> cod:id racket-fun:expr)
     #'(define-metafunction lang
         meta-fun : dom ... -> cod
         [(meta-fun dom ...) ,(racket-fun (term dom) ...)])]))
