#lang s-exp "../sysf.rkt"


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
      (let ([old-v-i ((inst vec-ref A) v i)])
        ((inst vec-set! A) v i ((inst vec-ref A) v j))
        ((inst vec-set! A) v j old-v-i)))))

(define sort!
  (all (A) (-> (Vec A) (-> A A Bool) Unit))
  (tyλ (A)
    (λ (v lt?)
      (letrec ([find-min-index
                (-> Int Int Int)
                (λ ([best Int] [i Int])
                  (if (< i ((inst vec-len A) v))
                      (if (lt? ((inst vec-ref A) v i) ((inst vec-ref A) v best))
                          (find-min-index i (+ i 1))
                          (find-min-index best (+ i 1)))
                      best))]
               [main-loop
                (-> Int Unit)
                (λ ([i Int])
                  (if (< i ((inst vec-len A) v))
                      (let ([j (find-min-index i (+ i 1))])
                        ((inst swap! A) v i j)
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
((inst sort! Time) v lex<)


;;;; Church encodings

;; The unit type!

(define-type-alias CUnit (all (A) (-> A A)))
(define cUnit CUnit
  (tyλ (A)
    (λ (x) x)))

;; Booleans

(define-type-alias CBool (all (A) (-> A A A)))
(define cTrue CBool
  (tyλ (A)
    (λ ([t A] [f A]) t)))
(define cFalse CBool
  (tyλ (A)
    (λ ([t A] [f A]) f)))

(define (bool->cbool [b Bool] -> CBool)
  (if b cTrue cFalse))
(define (cbool->bool [b CBool] -> Bool)
  ((inst b Bool) #t #f))

(define (cnot [b CBool] -> CBool)
  ((inst b CBool) cFalse cTrue))
(define (cand [b1 CBool] [b2 CBool] -> CBool)
  ((inst b1 CBool) b2 cFalse))
(define (cor [b1 CBool] [b2 CBool] -> CBool)
  ((inst b1 CBool) cTrue b2))

(define cif (all (A) (-> CBool (-> CUnit A) (-> CUnit A) A))
  (tyλ (A)
    (λ (condition t-thunk f-thunk)
      (((inst condition (-> CUnit A)) t-thunk f-thunk)
       cUnit))))

;; Naturals

(define-type-alias CNat (all (A) (-> (-> A A) A A)))
(define c0 CNat
  (tyλ (A)
    (λ ([s (-> A A)] [z A]) z)))
(define c1 CNat
  (tyλ (A)
    (λ ([s (-> A A)] [z A]) (s z))))
(define (csucc [n CNat] -> CNat)
  (tyλ (A)
    (λ ([s (-> A A)] [z A])
      (s ((inst n A) s z)))))

(define (cnat->int [n CNat] -> Int)
  ((inst n Int) (λ (x) (+ x 1)) 0))
(define (int->cnat [n Int] -> CNat)
  (if (< n 1)
      c0
      (csucc (int->cnat (- n 1)))))

(define (czero? [n CNat] -> CBool)
  ((inst n CBool) (λ (_) cFalse) cTrue))

(define (c+ [n CNat] [m CNat] -> CNat)
  ((inst n CNat) csucc m))
(define (c* [n CNat] [m CNat] -> CNat)
  ((inst n CNat) (λ (x) (c+ x m)) c0))

(define c2 (c+ c1 c1))
(define c4 (c+ c2 c2))
(define c6 (c+ c4 c2))
(define c24 (c* c4 c6))

;; Pairs

(define-type-alias (CProd A B) (all (R) (-> (-> A B R) R)))
(define cPair (all (A B) (-> A B (CProd A B)))
  (tyλ (A B)
    (λ (fst snd)
      (tyλ (R)
        (λ (k)
          (k fst snd))))))
(define cfst (all (A B) (-> (CProd A B) A))
  (tyλ (A B)
    (λ (pair)
      ((inst pair A) (λ (fst snd) fst)))))
(define csnd (all (A B) (-> (CProd A B) B))
  (tyλ (A B)
    (λ (pair)
      ((inst pair B) (λ (fst snd) snd)))))

(define cpair->rec (all (A B) (-> (CProd A B) (Record [fst A] [snd B])))
  (tyλ (A B)
    (λ (pair)
      (record [fst ((inst cfst A B) pair)] [snd ((inst csnd A B) pair)]))))
(define rec->cpair (all (A B) (-> (Record [fst A] [snd B]) (CProd A B)))
  (tyλ (A B)
    (λ (rec)
      ((inst cPair A B) (project rec fst) (project rec snd)))))

;; More arithmetic

(define (cpred [n CNat] -> CNat)
  ((inst cfst CNat CNat)
   ((inst n (CProd CNat CNat))
    (λ (pair)
      ((inst cPair CNat CNat)
       ((inst csnd CNat CNat) pair)
       (csucc ((inst csnd CNat CNat) pair))))
    ((inst cPair CNat CNat) c0 c0))))

(define (c- [n CNat] [m CNat] -> CNat)
  ((inst m CNat) cpred n))

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
  ((inst cif CNat)
   (c= n c0)
   (λ (_) c1)
   (λ (_) (c* n (cfact (c- n c1))))))

;; Sums

(define-type-alias (CSum A B) (all (R) (-> (-> A R) (-> B R) R)))
(define cInl (all (A B) (-> A (CSum A B)))
  (tyλ (A B)
    (λ (vl)
      (tyλ (R)
        (λ (kl kr) (kl vl))))))
(define cInr (all (A B) (-> B (CSum A B)))
  (tyλ (A B)
    (λ (vr)
      (tyλ (R)
        (λ (kl kr) (kr vr))))))

(define cinl? (all (A B) (-> (CSum A B) CBool))
  (tyλ (A B)
    (λ (sum)
      ((inst sum CBool) (λ (_) cTrue) (λ (_) cFalse)))))
(define cinr? (all (A B) (-> (CSum A B) CBool))
  (tyλ (A B)
    (λ (sum)
      (cnot ((inst cinl? A B) sum)))))

(define cprjl! (all (A B) (-> (CSum A B) A))
  (tyλ (A B)
    (λ (sum)
      ((inst sum A)
       (λ (va) va)
       (λ (_) ((inst error! A) "cprjl!: not a cInl"))))))
(define cprjr! (all (A B) (-> (CSum A B) B))
  (tyλ (A B)
    (λ (sum)
      ((inst sum B)
       (λ (_) ((inst error! B) "cprjr!: not a cInr"))
       (λ (vb) vb)))))

;; Lists

(define-type-alias (CList A) (all (R) (-> (-> A R R) R R)))
(define cNil (all (A) (CList A))
  (tyλ (A)
    (tyλ (R)
      (λ (cons nil) nil))))
(define cCons (all (A) (-> A (CList A) (CList A)))
  (tyλ (A)
    (λ (car cdr)
      (tyλ (R)
        (λ (cons nil) (cons car ((inst cdr R) cons nil)))))))

(define cnil? (all (A) (-> (CList A) CBool))
  (tyλ (A)
    (λ (clist)
      ((inst clist CBool)
       (λ (car cdr) cTrue)
       cFalse))))
(define ccons? (all (A) (-> (CList A) CBool))
  (tyλ (A)
    (λ (clist)
      (cnot ((inst cnil? A) clist)))))

(define clength (all (A) (-> (CList A) CNat))
  (tyλ (A)
    (λ (clist)
      ((inst clist CNat)
       (λ (car cdr) (csucc cdr))
       c0))))

(define cmap (all (A B) (-> (-> A B) (CList A) (CList B)))
  (tyλ (A B)
    (λ (f lst)
      ((inst lst (CList B))
       (λ (car cdr) ((inst cCons B) (f car) cdr))
       (inst cNil B)))))

(define ccar! (all (A) (-> (CList A) A))
  (tyλ (A)
    (λ (clist)
      (((inst clist (-> CUnit A))
        (λ (car cdr) (λ (_) car))
        (λ (_) ((inst error! A) "ccar!: not a cCons")))
       cUnit))))

; my gosh, ccdr is linear time (just like cpred)!
(define ccdr (all (A) (-> (CList A) (CList A)))
  (tyλ (A)
    (λ (clist)
      ((inst cfst (CList A) (CList A))
       ((inst clist (CProd (CList A) (CList A)))
        (λ (car cdr)
          ((inst cPair (CList A) (CList A))
           ((inst csnd (CList A) (CList A)) cdr)
           ((inst cCons A) car ((inst csnd (CList A) (CList A)) cdr))))
        ((inst cPair (CList A) (CList A)) (inst cNil A) (inst cNil A)))))))

(define ccdr! (all (A) (-> (CList A) (CList A)))
  (tyλ (A)
    (λ (clist)
      ((inst cif (CList A))
       ((inst cnil? A) clist)
       (λ (_) ((inst error! (CList A)) "ccdr!: not a cCons"))
       (λ (_) ((inst ccdr A) clist))))))

