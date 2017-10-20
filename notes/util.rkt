#lang racket/base

(provide term langname rulename
         render-reduction-rules)

(require redex/pict
         scribble/base
         (only-in redex default-language))

(define-syntax-rule (term e)
  (render-term (default-language) e))

(define-syntax-rule (rulename n)
  (symbol->string 'n))

(define-syntax-rule (langname n)
  (symbol->string 'n))

(define-syntax-rule (render-reduction-rules rel rule ...)
  (parameterize ([render-reduction-relation-rules '(rule ...)])
   (centered (render-reduction-relation rel #:style 'horizontal))))