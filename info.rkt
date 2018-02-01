#lang setup/infotab
(define name "northwestern type systems seminar")
(define collection "nu-type-systems")
(define categories '(educational))
(define can-be-loaded-with 'all)
(define required-core-version "6.11")
(define version "0.0.1")
(define deps '("base"
               "draw-lib"
               "rackunit-lib"
               "redex-lib"
               "redex-pict-lib"
               "scribble-lib"
               "turnstile"))
(define test-omit-paths '("."))
