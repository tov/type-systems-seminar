#lang racket/base

(provide with-typesetting
         term langname rulename
         theorem lemma exercise proof
         render-reduction-rules
         render-judgment-rules
         render-judgment-rules/horiz
         render-nonterminals
         render-metas)

(require redex/pict
         scribble/base
         (only-in pict hbl-append)
         (only-in racket/class make-object)
         (only-in racket/draw font%)
         (only-in racket/match match-lambda)
         (only-in redex/reduction-semantics default-language)
         (for-syntax racket/base syntax/parse))

(define SERIF-FONT "Palatino")
(define MONO-FONT (make-object font% 14 "Menlo" 'modern))

(define-syntax rewriter
  (syntax-rules ()
    [(_ [(pat ...) term ...] ...)
     (match-lambda [(list _ _ pat ... _) (list term ...)] ...)]))

(define (with-typesetting/thunk thunk)
  (with-compound-rewriters
   (['∈      (rewriter [(a as)       "" a " ∈ " as])]
    ['∉      (rewriter [(a as)       "" a " ∉ " as])]
    ['>      (rewriter [(σ t)        "" σ " > " t ""])]
    ['=>     (rewriter [(k_1 k_2)    "(⇒ " k_1 " " k_2 ")"])]
    ['->     (rewriter [(t_1 t_2)    "(→ " t_1 " " t_2 ")"])]
    ['-->    (rewriter [(e_1 e_2)    "" e_1 " ⟶ " e_2])]
    ['-->*   (rewriter [(e_1 e_2)    "" e_1 " ⟶* " e_2])]
    ['<:     (rewriter [(t_1 t_2)    "" t_1 " <: " t_2])]
    ['<:~>   (rewriter [(t_1 t_2 e)  "" t_1 " <: " t_2 " ↝ " e])]
    ['\\     (rewriter [(as bs)      "" as " \\ " bs ""])]
    ['∪      (rewriter [(as bs)      "" as " ∪ " bs ""])]
    ['≡      (rewriter [(t_1 t_2)    "" t_1 " ≡ " t_2 ""])]
    ['≡/alt  (rewriter [(t_1 t_2)    "" t_1 " ≡ " t_2 ""])]
    ['apply-subst
             (rewriter [(S σ)        "" S "" σ ""])]
    ['compose-subst
             (rewriter [(S_1 S_2)    "" S_1 "∘" S_2 ""])]
    ['abs-evidence
             (rewriter [(Δ e_0 P e)  "" Δ " ⊩ " e_0 " ⇝ " P " ⇒ " e ""])]
    ['app-evidence
             (rewriter [(Δ P e_0 e)  "" Δ " ⊩ " P " ⇒ " e_0 " ⇝ " e ""])]
    ['apply-substitution
             (rewriter [(e γ)        "" e "" γ ""])]
    ['extend (rewriter [(Γ x t)      "" Γ ", " x ":" t ""]
                       [(Δ a)        "" Δ ", " a ""])]
    ['extend-subst
             (rewriter [(γ x v)      "" γ "[" x ":=" v "]"])]
    ['fresh  (rewriter [(a bs)       "# " bs])]
    ['ftv    (rewriter [(t)          "ftv(" t ")"])]
    ['generate
             (rewriter [(Γ e t)      "⟦" Γ " ⊢ " e " : " t "⟧"])]
    ['get-evidence
             (rewriter [(Δ e t)      "" Δ " ⊩ " e " : " t ""])]
    ['kinds  (rewriter [(Δ t)        "" Δ " ⊢ " t]
                       [(Γ t k)      "" Γ " ⊢ " t " :: " k ""])]
    ['kinds/env
             (rewriter [(Δ Γ)        "" Δ " ⊢ " Γ])]
    ['env-ok
             (rewriter [(Γ)          "⊢ " Γ])]
    ['lookup (rewriter [(Γ x)        "" Γ "(" x ")"])]
    ['member (rewriter [(a Δ)        "" a " ∈ " Δ])]
    ['meta-+ (rewriter [(e_1 e_2)    "" e_1 " + " e_2])]
    ['meta-* (rewriter [(e_1 e_2)    "" e_1 " × " e_2])]
    ['meta-- (rewriter [(e_1 e_2)    "" e_1 " – " e_2])]
    ['meta-= (rewriter [(e_1 e_2)    "" e_1 " == " e_2 " ? 0 : 1"])]
    ['meta-< (rewriter [(e_1 e_2)    "" e_1 " < " e_2 " ? 0 : 1"])]
    ['non-zero?
             (rewriter [(z)          "" z " ≠ 0"])]
    ['not-a-type-variable
             (rewriter [(t)          "" t " is not a type variable"])]
    ['parens (rewriter [(any)        "(" any ")"])]
    ['qimplies
             (rewriter [(P_1 P_2)    "" P_1 " ⊩ " P_2 ""])]
    ['qjoin  (rewriter [(P_1 P_2)    "" P_1 " ∪ " P_2 ""])]
    ['qtranslates
             (rewriter [(Δ Γ e_0 e t)"" Δ " | " Γ " ⊢ " e_0
                                          " ⇝ " e " : " t ""])]
    ['qtypes (rewriter [(P Γ e t)    "" P " | " Γ " ⊢ " e " : " t ""])]
    ['satisfies
             (rewriter [(γ Γ)        "" γ " ⊨ " Γ])]
    ['SN     (rewriter [(t e)        "(SN " t " " e ")"])]
    ['size   (rewriter [(e)          "|" e "|"])]
    ['solve-constraint
             (rewriter [(C S)        "solve(" C ") ↝ " S])]
    ['substitute
             (rewriter [(e x v)      "" e "[" x ":=" v "]"])]
    ['types  (rewriter [(Γ e t)      "" Γ " ⊢ " e " : " t]
                       [(Δ Γ e t)    "" Δ "; " Γ " ⊢ " e " : " t])]
    ['types/alt
             (rewriter [(Γ e t)      "" Γ " ⊢ " e " : " t])]
    ['types~>
             (rewriter [(Γ e t e_out)
                                     "" Γ " ⊢ " e " : " t " ↝ " e_out])]
    ['types* (rewriter [(e t)        "" e " : " t])]
    ['unify  (rewriter [(t_1 t_2 S)  "" t_1 " ~ " t_2 " ↝ " S])]
    ['W      (rewriter [(Γ e S t)   "W(" Γ "; " e ") = (" S "; " t ")"]
                       [(Γ e S t P) "W(" Γ "; " e ") = ("
                                         S "; " t "; " P ")"])])
   (with-atomic-rewriter 't "τ"
    (with-atomic-rewriter 'l "ℓ"
     (with-atomic-rewriter 'k "κ"
      (parameterize
        ([default-font-size              16]
         [default-style                  SERIF-FONT]
         [grammar-style                  SERIF-FONT]
         [label-style                    SERIF-FONT]
         [literal-style                  MONO-FONT]
         [metafunction-style             SERIF-FONT]
         [non-terminal-style             (cons 'italic SERIF-FONT)]
         [non-terminal-subscript-style   (cons 'subscript SERIF-FONT)]
         [non-terminal-superscript-style (cons 'superscript SERIF-FONT)]
         [paren-style                    SERIF-FONT])
        (thunk)))))))

(define-syntax-rule (with-typesetting expr0 expr ...)
  (with-typesetting/thunk (λ () (list expr0 expr ...))))

(define-syntax (term stx)
  (syntax-parse stx
    [(_ e) #'(with-typesetting (render-term (check-default-language 'util.rkt::term) e))]
    [(_ e #:lang L) #'(with-typesetting (render-term L e))]))

(define (check-default-language name)
  (define l (default-language))
  (unless l (error name "expected default-language to be set"))
  l)

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

(define-syntax-rule (render-judgment-rules/horiz rel rule ...)
  (with-typesetting
      (centered
       (hbl-append
        40
        (parameterize ([judgment-form-cases '(rule)])
          (render-judgment-form rel))
        ...))))

(define-syntax-rule (render-nonterminals lang nt ...)
  (parameterize ([render-language-nts '(nt ...)])
    (with-typesetting (centered (render-language lang)))))

(define-syntax-rule (render-metas fn ...)
  (with-typesetting
    (centered
      (render-metafunctions fn ... #:contract? #true))))

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
