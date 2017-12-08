#lang scribble/base

@(require (prefix-in r: "redex/qual.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λ-qual)
@define[λ-qual]{@langname[λ-qual]}

@title{Qualified types}

@section[#:tag "qual-syntax"]{Syntax}

@render-nonterminals[r:λ-qual e c z]

@section[#:tag "qual-dynamic"]{Dynamic semantics}

@render-nonterminals[r:λ-qual v E]

@render-reduction-rules[r:->val β-val let if-true if-false delta]

@render-metas[r:δ]

@section[#:tag "qual-static"]{Static semantics}

@render-nonterminals[r:λ-qual t as C π P σ Γ]

@render-metas[r:type-of]

@render-judgment-rules[r:> mono all]

@render-judgment-rules[r:qimplies refl dup eq-int eq-prod ord-int]
                                                        
@render-judgment-rules[r:qtypes var-inst const-inst abs app if0 prod let-gen]

@section[#:tag "qual-inference"]{Type inference algorithm}

@render-metas[r:inst]

@render-judgment-rules[r:unify var-same var-left var-right int prod arr]

@render-judgment-rules[r:W var const abs app prod if0 let]

@section[#:tag "qual-evidence"]{Evidence translation}

@render-nonterminals[r:λ-qual Δ]

@render-judgment-rules[r:app-evidence nil cons]

@render-judgment-rules[r:abs-evidence nil cons]

@render-judgment-rules[r:qtranslates var const abs app if0 prod let]