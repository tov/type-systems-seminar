#lang scribble/base

@(require (prefix-in r: "redex/fomega.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:fomega)
@define[fomega]{@langname[λ-ω]}

@title{The higher-order lambda calculus @fomega}

@render-nonterminals[r:fomega k t e]


