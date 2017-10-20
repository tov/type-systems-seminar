#lang racket/base

(provide with-rewriters
         term langname rulename
         render-reduction-rules
         render-judgment-rules types/r
         render-nonterminals)

(require racket/list
         redex/pict
         scribble/base
         (only-in racket/match match-define match-lambda)
         (only-in redex default-language))

#;
(define (with-rewriters/thunk thunk)
  (with-compound-rewriters
   (['lookup (match-lambda [`(,_ ,_ ,Γ ,x ,_) (list "" Γ "(" x ")")])]
    ['extend (match-lambda [(list _ _ Γ x t _) (list "" Γ ", " x ":" t)])]
    ['substitute
     (match-lambda [(list _ _ e x v _) (list "" e "[" x ":=" v "]")])]
    ['types* (match-lambda [(list _ _ e t _) (list "" e " : " t)])]
    ['types  (match-lambda [(list _ _ Γ e t _) (list "" Γ " ⊢ " e " : " t)])])
   (with-atomic-rewriter 't "τ" (thunk))))

#;
(define-syntax-rule (with-rewriters expr0 expr ...)
  (with-rewriters/thunk (λ () (expr0 expr ...))))

(define-syntax-rule (with-rewriters expr0 expr ...)
  (with-compound-rewriters
   (['-->    (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " → " e_2)])]
    ['lookup (match-lambda [(list _ _ Γ x _)     (list "" Γ "(" x ")")])]
    ['extend (match-lambda [(list _ _ Γ x t _)   (list "" Γ ", " x ":" t)])]
    ['substitute
     (match-lambda [(list _ _ e x v _)           (list "" e "[" x ":=" v "]")])]
    ['types* (match-lambda [(list _ _ e t _)     (list "" e " : " t)])]
    ['types  (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)])])
   (with-atomic-rewriter 't "τ" (begin expr0 expr ...))))

(define-syntax-rule (term e)
  (with-rewriters (render-term (default-language) e)))

(define-syntax-rule (types/r Γ e t)
  (term (types Γ e t)))

(define-syntax-rule (rulename n)
  (symbol->string 'n))

(define-syntax-rule (langname n)
  (symbol->string 'n))

(define-syntax-rule (render-reduction-rules rel rule ...)
  (parameterize ([render-reduction-relation-rules '(rule ...)])
    (with-rewriters (centered (render-reduction-relation
                               rel #:style 'horizontal)))))

(define-syntax-rule (render-judgment-rules rel rule ...)
  (parameterize ([judgment-form-cases '(rule ...)])
    (with-rewriters (centered (render-judgment-form rel)))))

(define-syntax-rule (render-nonterminals lang nt ...)
  (parameterize ([render-language-nts '(nt ...)])
    (with-rewriters (centered (render-language lang)))))

