#lang scribble/base

@(require (prefix-in r: "redex/ml.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λ-ml)
@define[λ-ml]{@langname[λ-ml]}

@title{ML type inference}

@section[#:tag "ml-syntax"]{Syntax of @λ-ml}

@render-nonterminals[r:λ-ml/no-bool e x y]

@section[#:tag "ml-dynamic"]{Dynamic semantics}

@render-nonterminals[r:λ-ml/no-bool v E]

@render-reduction-rules[r:->val β-val let]

@section[#:tag "ml-static"]{Static semantics}

@render-nonterminals[r:λ-ml/no-bool t σ Γ a b]

@render-judgment-rules[r:> mono all]

@render-judgment-rules[r:types var abs app let]

@section[#:tag "ml-base"]{Adding base types}

@render-nonterminals[r:λ-ml t e v E]

@render-reduction-rules[r:->val if-true if-false]

@render-judgment-rules[r:types true false if]

@section[#:tag "ml-inference"]{Type inference algorithm}

@render-nonterminals[r:λ-ml/no-bool S]

@render-judgment-rules[r:unify var-same var-left bool-left arr-left arr]

@render-metas[r:inst r:gen]}

@render-judgment-rules[r:W var app abs let true false if]

@section[#:tag "ml-constraints"]{Constraint-based type inference}

@render-judgment-rules[r:solve true and equals exists]

@render-metas[r:generate]
