#lang scribble/base

@(require (prefix-in r: "redex/record.rkt")
          "util.rkt"
          (only-in redex default-language)
          redex/pict)

@(default-language r:record)
@define[st<:]{@langname[λ-<:]}

@title{Subtyping with Records}

@section[#:tag "st<:-syntax"]{Syntax}

@render-nonterminals[r:record t e f]

@section[#:tag "st<:-dynamics"]{Dynamic Semantics}

@render-nonterminals[r:record v E].

@render-reduction-rules[r:->val prj]

@section[#:tag "st<:-statics"]{Static Semantics}


