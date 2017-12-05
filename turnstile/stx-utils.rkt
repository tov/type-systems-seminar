#lang turnstile

(provide (for-syntax free-id-set-intersect
                     free-id-set-union
                     free-id-set-difference))

(begin-for-syntax
  (define (free-id-set-intersect set1 set2)
    (cond
      [(null? set1)
       '()]
      [(member (car set1) set2 free-identifier=?)
       (cons (car set1) (free-id-set-intersect (cdr set1) set2))]
      [else
       (free-id-set-intersect (cdr set1) set2)]))

  (define (free-id-set-union set1 set2)
    (cond
      [(null? set1)
       set2]
      [(member (car set1) set2 free-identifier=?)
       (free-id-set-union (cdr set1) set2)]
      [else
       (cons (car set1) (free-id-set-union (cdr set1) set2))]))

  (define (free-id-set-difference set1 set2)
    (cond
      [(null? set1)
       '()]
      [(member (car set1) set2 free-identifier=?)
       (free-id-set-difference (cdr set1) set2)]
      [else
       (cons (car set1) (free-id-set-difference (cdr set1) set2))])))
     
      