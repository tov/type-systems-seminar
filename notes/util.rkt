#lang racket/base

(provide with-typesetting
         term langname rulename
         theorem lemma exercise proof
         render-reduction-rules
         render-judgment-rules
         render-nonterminals)

(require redex/pict
         scribble/base
         (only-in racket/match match-lambda)
         (only-in redex/reduction-semantics default-language)
         (for-syntax racket/base syntax/parse))

(define SERIF-FONT "Palatino")
(define MONO-FONT "Menlo")

(define (with-typesetting/thunk thunk)
  (with-compound-rewriters
   (['->     (match-lambda [(list _ _ e_1 e_2 _) (list "(→ " e_1 " " e_2 ")")])]
    ['-->    (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " → " e_2)])]
    ['extend (match-lambda [(list _ _ Γ x t _)   (list "" Γ ", " x ":" t)]
                           [(list _ _ Δ a _)     (list "" Δ ", " a)])]
    ['kinds  (match-lambda [(list _ _ Δ t _)     (list "" Δ " ⊢ " t)])]
    ['kinds/env
             (match-lambda [(list _ _ Δ Γ _)     (list "" Δ " ⊢ " Γ)])]
    ['lookup (match-lambda [(list _ _ Γ x _)     (list "" Γ "(" x ")")])]
    ['member (match-lambda [(list _ _ a Δ _)     (list "" a " ∈ " Δ)])]
    ['meta-+ (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " + " e_2)])]
    ['meta-* (match-lambda [(list _ _ e_1 e_2 _) (list "" e_1 " × " e_2)])]
    ['satisfies
             (match-lambda [(list _ _ γ Γ _)     (list "" γ " ⊨ " Γ)])]
    ['size   (match-lambda [(list _ _ e _)       (list "|" e "|")])]
    ['substitute
             (match-lambda [(list _ _ e x v _)   (list "" e "[" x ":=" v "]")])]
    ['types  (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)]
                           [(list _ _ Δ Γ e t _) (list "" Δ "; " Γ " ⊢ " e
                                                       " : " t)])]
    ['types/rec
             (match-lambda [(list _ _ Γ e t _)   (list "" Γ " ⊢ " e " : " t)])]
    ['types* (match-lambda [(list _ _ e t _)     (list "" e " : " t)])])
   (with-atomic-rewriter 't "τ"
    (parameterize
        ([default-style                  SERIF-FONT]
         [grammar-style                  SERIF-FONT]
         [label-style                    SERIF-FONT]
         [literal-style                  MONO-FONT]
         [metafunction-style             SERIF-FONT]
         [non-terminal-style             (cons 'italic SERIF-FONT)]
         [non-terminal-subscript-style   (cons 'subscript SERIF-FONT)]
         [non-terminal-superscript-style (cons 'superscript SERIF-FONT)]
         [paren-style                    SERIF-FONT])
      (thunk)))))

(define-syntax-rule (with-typesetting expr0 expr ...)
  (with-typesetting/thunk (λ () expr0 expr ...)))

(define-syntax-rule (term e)
  (with-typesetting (render-term (default-language) e)))

(define-syntax-rule (rulename n)
  (list "["  (symbol->string 'n) "]"))

(define-syntax-rule (langname n)
  (tt (symbol->string 'n)))

(define-syntax-rule (render-reduction-rules rel rule ...)
  (parameterize ([render-reduction-relation-rules '(rule ...)])
    (with-typesetting (centered (render-reduction-relation
                               rel #:style 'horizontal)))))

(define-syntax-rule (render-judgment-rules rel rule ...)
  (parameterize ([judgment-form-cases '(rule ...)])
    (with-typesetting (centered (render-judgment-form rel)))))

(define-syntax-rule (render-nonterminals lang nt ...)
  (parameterize ([render-language-nts '(nt ...)])
    (with-typesetting (centered (render-language lang)))))

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
