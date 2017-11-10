#lang racket/base

(require "../ml.rkt")
(require racket/match
         racket/set
         rackunit
         redex/reduction-semantics)

(default-language λ-ml)

;                                                         
;                                                         
;                                                         
;                                                         
;                             ;;          ;;;;            
;                             ;;         ;;;;;            
;                                        ;;               
;                                        ;;               
;   ;;     ;;  ;;  ;;;      ;;;;      ;;;;;;;;  ;;     ;; 
;   ;;     ;;  ;;;;;;;;       ;;      ;;;;;;;;   ;;   ;;  
;   ;;     ;;  ;;;   ;;;      ;;         ;;      ;;   ;;  
;   ;;     ;;  ;;     ;;      ;;         ;;      ;;;  ;;  
;   ;;     ;;  ;;     ;;      ;;         ;;       ;; ;;   
;   ;;     ;;  ;;     ;;      ;;         ;;       ;; ;;   
;   ;;     ;;  ;;     ;;      ;;         ;;        ;;;;   
;   ;;;   ;;;  ;;     ;;      ;;         ;;        ;;;    
;    ;;;;;;;;  ;;     ;;      ;;         ;;         ;;    
;     ;;;  ;;  ;;     ;;   ;;;;;;;;      ;;        ;;;    
;                                                  ;;     
;                                                  ;;     
;                                                ;;;;     
;                                                ;;;      
;                                                         

; [List-of A] -> A or #false
(define (unique-car lst)
  (cond
    [(null? lst) #false]
    [(null? (cdr lst)) (car lst)]
    [else (fail-check "non-unique result")]))

; t t -> S or #false
(define (unify-types t_1 t_2)
  (unique-car (judgment-holds (unify ,t_1 ,t_2 S) S)))
 
(define-check (check-unifies/fun? t_1 t_2 S)
  ; S -> [List-of [List a t]]
  (define (subst->list S)
    (match S
      [`•                            `()]
      [`(extend-subst ,S_1 ,a ,t)    `((,a ,t) ,@(subst->list S_1))]))
  (define S-actual (subst->list (or (unify-types t_1 t_2)
                                    (fail-check "Could not unify"))))
  (unless (set=? S S-actual)
    (fail-check (format "Unifies with ~s" S-actual))))
    
(define-syntax-rule (check-unifies? t_1 t_2 S)
  (check-unifies/fun? (term t_1) (term t_2) `S))

(define-check (check-does-not-unify/fun? t_1 t_2)
  (when (unify-types t_1 t_2)
    (fail-check "Unified")))
   
(define-syntax-rule (check-does-not-unify? t_1 t_2)
  (check-does-not-unify/fun? (term t_1) (term t_2)))

(check-unifies? a a ())
(check-unifies? a b ((a b)))
(check-unifies? a bool ((a bool)))
(check-unifies? bool a ((a bool)))
(check-unifies? a (-> b b) ((a (-> b b))))
(check-unifies? (-> a b) (-> (-> b b) (-> c c))
                ((a (-> (-> c c) (-> c c)))
                 (b (-> c c))))
(check-unifies? (-> a (-> c c)) (-> (-> b b) b)
                ((a (-> (-> c c) (-> c c)))
                 (b (-> c c))))

(check-does-not-unify? bool (-> bool bool))
(check-does-not-unify? a (-> a bool))
(check-does-not-unify? (-> a b) (-> b (-> a a)))

;                                                                    
;                                                                    
;                                                                    
;                                                                    
;               ;;;;                                      ;;       ;;
;                 ;;                                      ;;       ;;
;                 ;;                                      ;;       ;;
;                 ;;                                      ;;;     ;;;
;     ;;;;;       ;;        ;;;; ;;    ;;;;;               ;; ;;; ;; 
;    ;;;;;;;;     ;;       ;;;;;;;;   ;;;;;;;              ;; ;;; ;; 
;    ;     ;;     ;;      ;;;   ;;;  ;;;   ;;;             ;; ; ; ;; 
;     ;;;;;;;     ;;      ;;     ;;  ;;     ;;             ;; ; ; ;; 
;    ;;;;;;;;     ;;      ;;     ;;  ;;     ;;             ;; ; ; ;; 
;   ;;;    ;;     ;;      ;;     ;;  ;;     ;;             ;;;; ;;;; 
;   ;;     ;;     ;;      ;;     ;;  ;;     ;;             ;;;   ;;; 
;   ;;    ;;;     ;;      ;;;   ;;;  ;;;   ;;;              ;;   ;;  
;    ;;;;;;;;      ;;      ;;;;;;;;   ;;;;;;;               ;;   ;;  
;     ;;;  ;;       ;;;;    ;;;; ;;    ;;;;;                ;;   ;;  
;                                ;;                                  
;                          ;    ;;;                                  
;                          ;;;;;;;                                   
;                           ;;;;;                                    
;                                                                    

; e -> σ or #false
(define (type-check e)
  (define t (unique-car (judgment-holds (W • ,e S t) t)))
  (and t (term (gen (ftv ,t) ,t))))

(define-syntax-rule (check-types? e t)
  (test-equal (type-check (term e)) (term t)))

(define-syntax-rule (check-does-not-type? e)
  (check-false (type-check (term e))))

(check-types? true bool)
(check-types? (let x true x) bool)
(check-types? (λ x x) (all a (-> a a)))
; the order of binders produced by generalization is unpredictable!
(check-types? (λ x (λ y x)) (all a (all b (-> b (-> a b)))))
(check-types? (λ f (λ g (λ x (ap f (ap g x)))))
              (all a (all c (all b (-> (-> b c) (-> (-> a b) (-> a c)))))))
(check-types? (let f (λ x x) (ap f (λ x (λ y x))))
              (all a (all b (-> b (-> a b)))))
(check-types? (let f (λ x x)
                (if true
                    (ap f true)
                    (ap (ap f (λ y y)) false)))
              bool)

(check-types? (λ y
                (let f (λ x x)
                  (if y
                      (ap f true)
                      (ap (ap f (λ y y)) false))))
              (-> bool bool))
              
(check-does-not-type? (λ x (ap x x)))
(check-does-not-type? (ap true true))

(check-does-not-type? (λ y
                        (λ f
                          (if y
                              (ap f true)
                              (ap (ap f (λ y y)) false)))))

;                                                         
;                                                         
;                                                         
;                                                         
;                          ;;;;                           
;                            ;;                           
;                            ;;                           
;                            ;;                           
;     ;;;;;;     ;;;;;       ;;      ;;     ;;     ;;;;   
;   ;;;;;;;;;   ;;;;;;;      ;;       ;;   ;;    ;;   ;;  
;   ;;      ;  ;;;   ;;;     ;;       ;;   ;;    ;;    ;; 
;   ;;;;;      ;;     ;;     ;;       ;;   ;;   ;;      ; 
;    ;;;;;;;   ;;     ;;     ;;        ;; ;;    ;;;;;;;;; 
;       ;;;;;  ;;     ;;     ;;        ;; ;;    ;;        
;          ;;  ;;     ;;     ;;        ;; ;;    ;;        
;   ;     ;;;  ;;;   ;;;     ;;         ;;;      ;        
;   ;;;;;;;;;   ;;;;;;;       ;;        ;;;      ;;     ; 
;    ;;;;;;      ;;;;;         ;;;;     ;;;        ;;;;;; 
;                                                         
;                                                         
;                                                         
;                                                         
;                                                         

(define (type-check* e)
  (unique-car (judgment-holds (types* ,e σ) σ)))

(define-syntax-rule (check-types*? e t)
  (test-equal (type-check* (term e)) (term t)))

(define-syntax-rule (check-does-not-type*? e)
  (check-false (type-check* (term e))))

(check-types*? true bool)
(check-types*? (let x true x) bool)
(check-types*? (λ x x) (all a (-> a a)))
; the order of binders produced by generalization is unpredictable!
(check-types*? (λ x (λ y x)) (all a (all b (-> b (-> a b)))))
(check-types*? (λ f (λ g (λ x (ap f (ap g x)))))
               (all a (all c (all b (-> (-> b c) (-> (-> a b) (-> a c)))))))
(check-types*? (let f (λ x x) (ap f (λ x (λ y x))))
               (all a (all b (-> b (-> a b)))))
(check-types*? (let f (λ x x)
                 (if true
                     (ap f true)
                     (ap (ap f (λ y y)) false)))
               bool)

(check-types*? (λ y
                 (let f (λ x x)
                   (if y
                       (ap f true)
                       (ap (ap f (λ y y)) false))))
               (-> bool bool))
              
(check-does-not-type*? (λ x (ap x x)))
(check-does-not-type*? (ap true true))

(check-does-not-type*? (λ y
                         (λ f
                           (if y
                               (ap f true)
                               (ap (ap f (λ y y)) false)))))
