#lang scribble/base

@(require (prefix-in r: "redex/ml.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:λ-ml)
@define[λ-ml]{@langname[λ-ml]}

@title{ML type inference}

@section[#:tag "ml-syntax"]{Syntax of @λ-ml}

@render-nonterminals[r:λ-ml e x y]

@section[#:tag "ml-dynamic"]{Dynamic semantics}

@render-nonterminals[r:λ-ml v E]

@render-reduction-rules[r:->val β-val let]

@section[#:tag "ml-static"]{Static semantics}

@subsection[#:tag "ml-system"]{Algorithmic type system}

@render-nonterminals[r:λ-ml t σ Γ a b]

@render-judgment-rules[r:> mono all]

@render-judgment-rules[r:types var abs app let]

@subsection[#:tag "ml-inference"]{Type inference algorithm}

@render-nonterminals[r:λ-ml S]

@render-judgment-rules[r:unify var-same var-left var-right arr]

@centered{
 @with-typesetting{
  @render-metafunction[r:inst]

  @render-metafunction[r:gen]
 }
}

@render-judgment-rules[r:W var app abs let]

@section[#:tag "ml-constraints"]{Constraint-based type inference}

@render-judgment-rules[r:solve true and equal exists]

@centered{
 @with-typesetting{
  @render-metafunction[r:generate]
 }
}