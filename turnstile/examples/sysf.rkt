#lang s-exp nu-type-systems/turnstile/sysf


(define (negate [x Int] -> Int)
  (- 0 x))

(define (+ [x Int] [y Int] -> Int)
  (- x (negate y)))

(define (< [n Int] [m Int] -> Bool)
  (positive? (- m n)))

(define (= [n Int] [m Int] -> Bool)
  (zero? (- m n)))

;;;; Sorting

(define swap!
  (tyλ (A)
    (λ ([v (Vec A)] [i Int] [j Int])
      (let ([old-v-i ((vec-ref A) v i)])
        ((vec-set! A) v i ((vec-ref A) v j))
        ((vec-set! A) v j old-v-i)))))

(define sort!
  (All (A) (-> (Vec A) (-> A A Bool) Unit))
  (tyλ (A)
    (λ (v lt?)
      (letrec ([find-min-index
                (-> Int Int Int)
                (λ ([best Int] [i Int])
                  (if (< i ((vec-len A) v))
                      (if (lt? ((vec-ref A) v i) ((vec-ref A) v best))
                          (find-min-index i (+ i 1))
                          (find-min-index best (+ i 1)))
                      best))]
               [main-loop
                (-> Int Unit)
                (λ ([i Int])
                  (if (< i ((vec-len A) v))
                      (let ([j (find-min-index i (+ i 1))])
                        ((swap! A) v i j)
                        (main-loop (+ i 1)))
                      (void)))])
        (main-loop 0)))))

(define-type-alias Time (Record [hour Int] [minute Int]))
(define mk-time
  (λ ([h Int] [m Int])
    (record [hour h] [minute m])))

(define (lex< [p1 Time] [p2 Time] -> Bool)
  (if (< (project p1 hour) (project p2 hour))
      #true
      (if (= (project p1 hour) (project p2 hour))
          (< (project p1 minute) (project p2 minute))
          #false)))

(define v (vec (mk-time 3 30)
               (mk-time 3 00)
               (mk-time 2 00)))
((sort! Time) v lex<)


;;;; Church encodings

;; The unit type!

(define-type-alias CUnit (All (A) (-> A A)))
(define cUnit CUnit
  (tyλ (A)
    (λ (x) x)))

;; Booleans

(define-type-alias CBool (All (A) (-> A A A)))
(define cTrue CBool
  (tyλ (A)
    (λ ([t A] [f A]) t)))
(define cFalse CBool
  (tyλ (A)
    (λ ([t A] [f A]) f)))

(define (bool->cbool [b Bool] -> CBool)
  (if b cTrue cFalse))
(define (cbool->bool [b CBool] -> Bool)
  ((b Bool) #t #f))

(define (cnot [b CBool] -> CBool)
  ((b CBool) cFalse cTrue))
(define (cand [b1 CBool] [b2 CBool] -> CBool)
  ((b1 CBool) b2 cFalse))
(define (cor [b1 CBool] [b2 CBool] -> CBool)
  ((b1 CBool) cTrue b2))

(define cif (All (A) (-> CBool (-> CUnit A) (-> CUnit A) A))
  (tyλ (A)
    (λ (condition t-thunk f-thunk)
      (((condition (-> CUnit A)) t-thunk f-thunk)
       cUnit))))

;; Naturals

(define-type-alias CNat (All (A) (-> (-> A A) A A)))
(define c0 CNat
  (tyλ (A)
    (λ ([s (-> A A)] [z A]) z)))
(define c1 CNat
  (tyλ (A)
    (λ ([s (-> A A)] [z A]) (s z))))
(define (csucc [n CNat] -> CNat)
  (tyλ (A)
    (λ ([s (-> A A)] [z A])
      (s ((n A) s z)))))

(define (cnat->int [n CNat] -> Int)
  ((n Int) (λ (x) (+ x 1)) 0))
(define (int->cnat [n Int] -> CNat)
  (if (< n 1)
      c0
      (csucc (int->cnat (- n 1)))))

(define (czero? [n CNat] -> CBool)
  ((n CBool) (λ (_) cFalse) cTrue))

(define (c+ [n CNat] [m CNat] -> CNat)
  ((n CNat) csucc m))
(define (c* [n CNat] [m CNat] -> CNat)
  ((n CNat) (λ (x) (c+ x m)) c0))

(define c2 (c+ c1 c1))
(define c4 (c+ c2 c2))
(define c6 (c+ c4 c2))
(define c24 (c* c4 c6))

;; Pairs

(define-type-alias (CProd A B) (All (R) (-> (-> A B R) R)))
(define cPair (All (A B) (-> A B (CProd A B)))
  (tyλ (A B)
    (λ (fst snd)
      (tyλ (R)
        (λ (k)
          (k fst snd))))))
(define cfst (All (A B) (-> (CProd A B) A))
  (tyλ (A B)
    (λ (pair)
      ((pair A) (λ (fst snd) fst)))))
(define csnd (All (A B) (-> (CProd A B) B))
  (tyλ (A B)
    (λ (pair)
      ((pair B) (λ (fst snd) snd)))))

(define cpair->rec (All (A B) (-> (CProd A B) (Record [fst A] [snd B])))
  (tyλ (A B)
    (λ (pair)
      (record [fst ((cfst A B) pair)] [snd ((csnd A B) pair)]))))
(define rec->cpair (All (A B) (-> (Record [fst A] [snd B]) (CProd A B)))
  (tyλ (A B)
    (λ (rec)
      ((cPair A B) (project rec fst) (project rec snd)))))

;; More arithmetic

(define (cpred [n CNat] -> CNat)
  ((cfst CNat CNat)
   ((n (CProd CNat CNat))
    (λ (pair)
      ((cPair CNat CNat)
       ((csnd CNat CNat) pair)
       (csucc ((csnd CNat CNat) pair))))
    ((cPair CNat CNat) c0 c0))))

(define (c- [n CNat] [m CNat] -> CNat)
  ((m CNat) cpred n))

(define (c<= [n CNat] [m CNat] -> CBool)
  (czero? (c- n m)))
(define (c>= [n CNat] [m CNat] -> CBool)
  (c<= m n))
(define (c< [n CNat] [m CNat] -> CBool)
  (cnot (c>= n m)))
(define (c> [n CNat] [m CNat] -> CBool)
  (c< m n))
(define (c= [n CNat] [m CNat] -> CBool)
  (cand (c<= n m) (c<= m n)))

(define (cfact [n CNat] -> CNat)
  ((cif CNat)
   (c= n c0)
   (λ (_) c1)
   (λ (_) (c* n (cfact (c- n c1))))))

;; Sums

(define-type-alias (CSum A B) (All (R) (-> (-> A R) (-> B R) R)))
(define cInl (All (A B) (-> A (CSum A B)))
  (tyλ (A B)
    (λ (vl)
      (tyλ (R)
        (λ (kl kr) (kl vl))))))
(define cInr (All (A B) (-> B (CSum A B)))
  (tyλ (A B)
    (λ (vr)
      (tyλ (R)
        (λ (kl kr) (kr vr))))))

(define cinl? (All (A B) (-> (CSum A B) CBool))
  (tyλ (A B)
    (λ (sum)
      ((sum CBool) (λ (_) cTrue) (λ (_) cFalse)))))
(define cinr? (All (A B) (-> (CSum A B) CBool))
  (tyλ (A B)
    (λ (sum)
      (cnot ((cinl? A B) sum)))))

(define cprjl! (All (A B) (-> (CSum A B) A))
  (tyλ (A B)
    (λ (sum)
      ((sum A)
       (λ (va) va)
       (λ (_) ((error! A) "cprjl!: not a cInl"))))))
(define cprjr! (All (A B) (-> (CSum A B) B))
  (tyλ (A B)
    (λ (sum)
      ((sum B)
       (λ (_) ((error! B) "cprjr!: not a cInr"))
       (λ (vb) vb)))))

;; Lists

(define-type-alias (CList A) (All (R) (-> (-> A R R) R R)))
(define cNil (All (A) (CList A))
  (tyλ (A)
    (tyλ (R)
      (λ (cons nil) nil))))
(define cCons (All (A) (-> A (CList A) (CList A)))
  (tyλ (A)
    (λ (car cdr)
      (tyλ (R)
        (λ (cons nil) (cons car ((cdr R) cons nil)))))))

(define cnil? (All (A) (-> (CList A) CBool))
  (tyλ (A)
    (λ (clist)
      ((clist CBool)
       (λ (car cdr) cTrue)
       cFalse))))
(define ccons? (All (A) (-> (CList A) CBool))
  (tyλ (A)
    (λ (clist)
      (cnot ((cnil? A) clist)))))

(define clength (All (A) (-> (CList A) CNat))
  (tyλ (A)
    (λ (clist)
      ((clist CNat)
       (λ (car cdr) (csucc cdr))
       c0))))

(define cmap (All (A B) (-> (-> A B) (CList A) (CList B)))
  (tyλ (A B)
    (λ (f lst)
      ((lst (CList B))
       (λ (car cdr) ((cCons B) (f car) cdr))
       (cNil B)))))

(define ccar! (All (A) (-> (CList A) A))
  (tyλ (A)
    (λ (clist)
      (((clist (-> CUnit A))
        (λ (car cdr) (λ (_) car))
        (λ (_) ((error! A) "ccar!: not a cCons")))
       cUnit))))

; my gosh, ccdr is linear time (just like cpred)!
(define ccdr (All (A) (-> (CList A) (CList A)))
  (tyλ (A)
    (λ (clist)
      ((cfst (CList A) (CList A))
       ((clist (CProd (CList A) (CList A)))
        (λ (car cdr)
          ((cPair (CList A) (CList A))
           ((csnd (CList A) (CList A)) cdr)
           ((cCons A) car ((csnd (CList A) (CList A)) cdr))))
        ((cPair (CList A) (CList A)) (cNil A) (cNil A)))))))

(define ccdr! (All (A) (-> (CList A) (CList A)))
  (tyλ (A)
    (λ (clist)
      ((cif (CList A))
       ((cnil? A) clist)
       (λ (_) ((error! (CList A)) "ccdr!: not a cCons"))
       (λ (_) ((ccdr A) clist))))))

;; Existentials

(define-type-alias (ex A t) (All (R) (-> (All (A) (-> t R)) R)))

(define-type-alias COUNTER (ex A (Record [start A]
                                         [next (-> A A)]
                                         [get (-> A Int)])))

(define Counter1 COUNTER
  (tyλ (R)
    (λ (k)
      ((k Int)
       (record [start 0]
               [next (λ (x) (+ x 1))]
               [get (λ (x) x)])))))
(define Counter2 COUNTER
  (tyλ (R)
    (λ (k)
      ((k CNat)
       (record [start c0]
               [next csucc]
               [get cnat->int])))))

(define (count-to-2 [Counter COUNTER] -> Int)
  ((Counter Int)
   (tyλ (counter-type)
     (λ (r)
       ((project r get)
        ((project r next)
         ((project r next)
          (project r start))))))))

(define counted-to-2 (count-to-2 Counter1))
(define counted-to-2* (count-to-2 Counter2))
