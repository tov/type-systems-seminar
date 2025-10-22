#lang racket
(require "../stlc.rkt" redex/reduction-semantics)

(test-->> ->val/rec
          (term (ap (λ x nat x) (s z)))
          (term (s z)))

(test-->> ->val/rec
          (term (rec z (z) (xpre yrec (s z))))
          (term z))
(test-->> ->val/rec
          (term (rec (s z) (z) (xpre yrec (s z))))
          (term (s z)))
(test-->> ->val/rec
          (term (rec (s (s z)) (z) (xpre yrec xpre)))
          (term (s z)))
(test-->> ->val/rec
          (term (rec (s (s z)) (z) (xpre yrec yrec)))
          (term z))

(define add
  (term (λ n nat (λ m nat (rec n [m] [xpre yrec (s yrec)])))))
(define (to-n n)
  (cond
    [(zero? n) (term z)]
    [else (term (s ,(to-n (- n 1))))]))
(test-->> ->val/rec
          (term (ap (ap ,add z) z))
          (term z))
(test-->> ->val/rec
          (term (ap (ap ,add z) (s z)))
          (term (s z)))
(test-->> ->val/rec
          (term (ap (ap ,add (s z)) z))
          (term (s z)))
(test-->> ->val/rec
          (term (ap (ap ,add ,(to-n 3)) ,(to-n 4)))
          (to-n 7))

(define mult
  (term (λ n nat (λ m nat (rec n [z] [xpre yrec (ap (ap ,add m) yrec)])))))
(test-->> ->val/rec
          (term (ap (ap ,mult z) z))
          (term z))
(test-->> ->val/rec
          (term (ap (ap ,mult z) (s z)))
          (term z))
(test-->> ->val/rec
          (term (ap (ap ,mult (s z)) z))
          (term z))
(test-->> ->val/rec
          (term (ap (ap ,mult ,(to-n 3)) ,(to-n 4)))
          (to-n 12))

(define fact
  (term (λ n nat (rec n [(s z)] [xpre yrec (ap (ap ,mult (s xpre)) yrec)]))))

(test-->> ->val/rec
          (term (ap ,fact z))
          (term (s z)))
(test-->> ->val/rec
          (term (ap ,fact (s z)))
          (term (s z)))
(test-->> ->val/rec
          (term (ap ,fact (s (s z))))
          (term (s (s z))))
(test-->> ->val/rec
          (term (ap ,fact (s (s (s z)))))
          (to-n 6))
(test-->> ->val/rec
          (term (ap ,fact (s (s (s (s z))))))
          (to-n 24))

(define swap
  (term (λ n nat (rec n [(s z)] [xpre yrec z]))))

(test-->> ->val/rec
          (term (ap ,swap z))
          (term (s z)))
(test-->> ->val/rec
          (term (ap ,swap (s z)))
          (term z))

(define parity
  (term (λ n nat (rec n [z] [xpre yrec (ap ,swap yrec)]))))

(test-->> ->val/rec
          (term (ap ,parity z))
          (term z))
(test-->> ->val/rec
          (term (ap ,parity (s z)))
          (term (s z)))
(test-->> ->val/rec
          (term (ap ,parity (s (s z))))
          (term z))
(test-->> ->val/rec
          (term (ap ,parity (s (s (s z)))))
          (term (s z)))

(define halve
  (term (λ n nat (rec n [z] [xpre yrec (ap (ap ,add (ap ,parity xpre)) yrec)]))))

(test-->> ->val/rec
          (term (ap ,halve z))
          (term z))
(test-->> ->val/rec
          (term (ap ,halve (s z)))
          (term z))
(test-->> ->val/rec
          (term (ap ,halve (s (s z))))
          (term (s z)))
(test-->> ->val/rec
          (term (ap ,halve (s (s (s z)))))
          (term (s z)))
(test-->> ->val/rec
          (term (ap ,halve (s (s (s (s z))))))
          (term (s (s z))))
(test-->> ->val/rec
          (term (ap ,halve ,(to-n 9)))
          (to-n 4))
(test-->> ->val/rec
          (term (ap ,halve ,(to-n 10)))
          (to-n 5))
(test-->> ->val/rec
          (term (ap ,halve ,(to-n 11)))
          (to-n 5))
