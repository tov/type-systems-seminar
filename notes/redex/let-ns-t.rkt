#lang racket

(require redex
         "let-ns.rkt")

(provide let-ns/t)

(define-extended-language let-ns/t let-ns/eval
  (t ::=
     int
     str))

