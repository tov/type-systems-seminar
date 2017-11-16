#lang scribble/base

@(require (prefix-in r: "redex/fomega.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:fomega)
@define[fomega]{@langname[λ-ω]}

@title{The higher-order lambda calculus @fomega}

@render-nonterminals[r:fomega k t e]

@render-nonterminals[r:fomega v E]

@render-reduction-rules[r:->val β-val inst]

@render-nonterminals[r:fomega TE Γ]

@render-reduction-rules[r:->type β-type]

@render-judgment-rules[r:kinds var arr all abs app]

@render-judgment-rules[r:types var abs app tabs tapp]