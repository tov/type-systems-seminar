#lang racket/base

(provide with-rewriters
         term langname rulename
         theorem lemma exercise proof
         render-reduction-rules
         render-judgment-rules types/r
         render-nonterminals)

(require redex/pict
         scribble/base
         (only-in racket/match match-define match-lambda)
         (only-in redex/reduction-semantics default-language)
         (for-syntax racket/base syntax/parse))

#;
(define (with-rewriters/thunk thunk)
  (with-compound-rewriters
   (['->     (match-lambda [(list _ _ e_1 e_2 _) (list "(→ " e_1 " " e_2 ")")])]
    ['-->    (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " → " e_2)])]
    ['extend (match-lambda [(list _ _ Γ x t _)   (list "" Γ ", " x ":" t)])]
    ['lookup (match-lambda [(list _ _ Γ x _)     (list "" Γ "(" x ")")])]
    ['meta-+ (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " + " e_2)])]
    ['meta-* (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " × " e_2)])]
    ['satisfies
             (match-lambda [(list _ _ γ Γ _)     (list "" γ " ⊨ " Γ)])]
    ['size   (match-lambda [(list _ _ e _)       (list "|" e "|")])]
    ['substitute
             (match-lambda [(list _ _ e x v _)   (list "" e "[" x ":=" v "]")])]
    ['types  (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)])]
    ['types/rec
             (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)])]
    ['types* (match-lambda [(list _ _ e t _)     (list "" e " : " t)])])
   (with-atomic-rewriter 't "τ" (thunk))))

#;
(define-syntax-rule (with-rewriters expr0 expr ...)
  (with-rewriters/thunk (λ () (expr0 expr ...))))

(define-syntax-rule (with-rewriters expr0 expr ...)
  (with-compound-rewriters
   (['->     (match-lambda [(list _ _ e_1 e_2 _) (list "(→ " e_1 " " e_2 ")")])]
    ['-->    (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " → " e_2)])]
    ['extend (match-lambda [(list _ _ Γ x t _)   (list "" Γ ", " x ":" t)])]
    ['lookup (match-lambda [(list _ _ Γ x _)     (list "" Γ "(" x ")")])]
    ['meta-+ (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " + " e_2)])]
    ['meta-* (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " × " e_2)])]
    ['satisfies
             (match-lambda [(list _ _ γ Γ _)     (list "" γ " ⊨ " Γ)])]
    ['size   (match-lambda [(list _ _ e _)       (list "|" e "|")])]
    ['substitute
             (match-lambda [(list _ _ e x v _)   (list "" e "[" x ":=" v "]")])]
    ['types  (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)])]
    ['types/rec
             (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)])]
    ['types* (match-lambda [(list _ _ e t _)     (list "" e " : " t)])])
   (with-atomic-rewriter 't "τ" (begin expr0 expr ...))))

(define-syntax-rule (term e)
  (with-rewriters (render-term (default-language) e)))

(define-syntax-rule (types/r Γ e t)
  (term (types Γ e t)))

(define-syntax-rule (rulename n)
  (list "["  (symbol->string 'n) "]"))

(define-syntax-rule (langname n)
  (tt (symbol->string 'n)))

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

#;
(define (theorem-like/thunk kind name body)
  (if name
      (list* (bold (symbol->string kind)) " (" name ")." (body))
      (list* (bold (symbol->string kind) ".") (body))))

#;
(define-syntax (theorem-like stx)
  (syntax-parse stx
    [(_ kind:id :opt-name body:expr ...)
     #'(theorem-like/thunk 'kind name (λ () "" body ...))]))

(begin-for-syntax
  (define-splicing-syntax-class opt-name
    [pattern (~seq #:name name:expr)]
    [pattern (~seq)
             #:with name #'#false]))

(define-syntax (define-theorem-like stx)
  (syntax-parse stx
    [(_ fun:id kind:id)
     #'(define-syntax (fun stx1)
         (syntax-parse stx1
           [(_ kind-name:opt-name body:expr (... ...))
            #'(let ([name kind-name.name])
                (if name
                    (list (bold (symbol->string 'kind))
                          " (" name "). "
                          (emph body (... ...)))
                    (list (bold (symbol->string 'kind) ". ")
                          (emph body (... ...)))))]))]))

(define-theorem-like theorem Theorem)
(define-theorem-like lemma Lemma)
(define-theorem-like exercise Exercise)
(define-theorem-like proof Proof)
