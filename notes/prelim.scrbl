#lang scribble/base

@(require (prefix-in r: "redex/prelim.rkt")
          (only-in "redex/prelim.rkt" bounded-bst wrong-bst)
          "util.rkt"
          (only-in redex/reduction-semantics default-language)
          redex/pict
          (only-in scribble-math/dollar $ $$))

@(default-language r:prelim)
@define[let-zl]{@langname[let-zl]}

@title{Mathematical Preliminaries}

Throughout the course, we are going to define sets
recursively, define relations on those sets (also
recursively), and then prove relationships between these
sets and elements of the sets that satisfy specific
relations. We will also use a particularly expressive notion
called a @emph{context} as tool to streamline our
definitions of relations. This tool is very powerful and
expressive, so we'll explore it in a more familiar setting
here in this chapter before putting it to use in our study
of type systems.

@section{Defining Sets}

We will define sets via rules that describe the membership of the
set recursively. Generally, the definitions will consists of a
number of base case elements of the set and ways to build bigger
sets out of sets that are already built.

Here is a first example definition of a set, specifically
the set of binary trees:

@(parameterize ([language-make-::=-pict
                 (λ (nt-names)
                      ((current-text)
                       (cond
                         [(equal? nt-names '(z))
                          " ∈ "]
                         [else " ::= "])
                       (grammar-style)
                       (default-font-size)))])
   @render-nonterminals[r:prelim bt z])

In words, this definition says that @term[bt] is the
smallest set satisfying two conditions, one for each line of
the definition. The first line says that @term[leaf] is a
member of the set @term[bt]. The second line says that, for
any natural number @term[z] and any two other binary trees,
@term[bt_1] and @term[bt_2], @term[(node z bt_1 bt_2)] is a
member of the set @term[bt].

For example, we know that
@term[(node 2 (node 1 leaf leaf) leaf)] is a member of the set
@term[bt] by using the first rule three times and the second
rule two times. Conversely, we know that @term[(node 1 leaf)]
and @term[(node 1 (node 2) (node 3))] are not members of
the set, as the rules provide no way to build up elements
looking like those.

As a notational device, we will pun on the use of @term[bt]
both as the set and as an element of the set, using the name
of the element to indicate which set it comes from.

Throughout these notes, we will write out example terms
following the notation in the grammar, but for the specific
case of trees, it is often easier to see what is going on when we
visualize them like this, so we will do so, from time to time.
@centered{@tree[(node 2 (node 1 leaf leaf) leaf)]}

@section{Proving Properties by Induction}

To do proofs with these relations, we use structural
induction, a proof technique that generalizes the usual form
of induction on natural numbers. When we do a proof by
induction on natural numbers, we're proving a property
that's indexed by natural numbers. We start by proving that
the property is true when the natural number is zero, and
then we assume that the property is true for some given
natural number and prove that it holds for the next one.
These two lemmas enable us to build up a proof for any
particular natural number that we encounter later on, as any
particular natural number can be found by starting at zero
and counting up, one number at a time.

The root of this idea is the idea of a well-founded order,
specifically, an ordering on a set that covers all of the
elements in the set but where all of the descending chains
in the order are finite. For the natural numbers, the
ordering is simply the usual less-than ordering. That is,
given any particular natural number, there are only a finite
number of other naturals that are less than it, so chaining
together these lemmas will always eventually bottom out.

The way we define sets always gives us such a well-founded
order, meaning that any of the definitions of sets we use in
these notes are also amenable to proofs by induction.
Putting it another way, we can imagine that the set of
natural numbers is defined this way:
@render-nonterminals[r:prelim ℕ]
and that the usual natural-number based induction is
actually based on the natural numbers being defined in that
manner; we generalize this perspective to all of the
sets that we define.

Taking this idea to our binary tree set definition, there
are two ways to create binary trees, either they are leaves
or they are nodes (which contain two smaller trees). So, if
we want to prove some property of binary trees we can
organize the proof into two parts: first we prove the
property for leaves and then we assume the property holds
for two arbitrary trees and show that it holds for the tree
you get by combining the two together with an integer using
@term[node]. These then become the two lemmas that can be
chained together to obtain the proof for any particular
binary tree; that is, if we can prove those two lemmas, we
know the property holds for all of the binary trees.

Let's look at an example proof. Say we wished to prove that,
in a binary tree of height @${h}, there are at most @${2^h}
leaves. To do so, we have prove this fact for the two cases.

@itemlist[
 @item{ Case one: the tree is a leaf. In this case, the
  statement we are trying to prove is that a binary tree of
  height zero has at most @${2^0}, which is 1, nodes. Well, a
  leaf has zero nodes, so this case holds.}

 @item{Case two: the tree is built with @term[node]. Each
  node contains two binary trees; let's name them @term[bt_1]
  and @term[bt_1]. Let's also name their heights @${h_1} and
  @${h_2}, respectively and name the number of leaves they
  have @${l_1} and @${l_2}. Our goal is to show that the
  number of leaves in the tree @term[(node i bt_1 bt_2)],
  which is @${l_1+l_2} (since all of the leaves of both
  @term[bt_1] and @term[bt_2] are in the tree) is at most
  @${2^{max(h_1,h_2)+1}}, as the tree
  @term[(node i bt_1 bt_2)] has the height @${max(h_1,h_2)+1}
  (from the definition of the height of a tree).

  As we doing this proof by induction, we also get to assume
  that the lemma we are proving holds for the trees
  @term[bt_1] and @term[bt_2]. So, we know that @${l_1} is at
  most @${2^{h_1}} and @${l_2} is at most @${2^{h_2}}.

  To complete the proof, we need to use some facts about
  numbers. By adding the two inductive assumptions, we know
  that @$${l_1+l_2 ≤ 2^{h_1} + 2^{h_2}} Since the maximum of
  two numbers is larger than either of them and exponentiation
  is increasing, we know @$${2^{h_1} ≤ 2^{max(h_1,h_2)}} and
  similarly for @${l_2}, so we have @$${l_1 + l_2 ≤
   2^{max(h_1,h_2)} + 2^{max(h_1,h_2)}} We can rearrange the
  right-hand side using properties of exponentiation and
  arrive at @$${l_1+l_2 ≤ 2^{max(h_1,h_2) + 1}} which was the
  goal.}]


@section{Defining Relations on those Sets}

Once set have a set defined, we can define a relation that
captures properties of elements of the sets. For example, we
might want to characterize which of the binary trees are
binary search trees. To do that, we'll define a three-place
relation that relates a binary tree to two integers. We'll
write @term[(bounded-bst bt z_1 z_2)] to indicate that
@term[bt], @term[z_1], and @term[z_2] are related by the
relation and we'll interpret that to mean that @term[bt] is
a binary search tree and that all of the integers in
@term[bt] are between @term[z_1] and @term[z_2].

We define the relation inductively, just as the sets are
defined inductively, using rules. We will write the rules
are written as sequents, with premises (assumptions) above a
bar and a conclusion below the bar, and a name for the rule
beside the bar. Here is the rule for leaves

@render-judgment-rules[r:bounded-bst leaf]

It says that if @term[z_1] is less than @term[z_2], then
the empty binary tree is related to @term[z_1] and
@term[z_2].

There is one more rule, for interior nodes:

@render-judgment-rules[r:bounded-bst node]

If says that if @term[bt_1] is related to @term[z_1] and
@term[z_2], and if @term[bt_2] is related to
@term[z_2] and @term[z_3], then
@term[(node z_2 bt_1 bt_2)] is related to the integers
@term[z_1] and @term[z_3].

As when defining the sets, the rules define a relation
recursively, specifically the smallest relation that
satisfies all of the given rules, where satisfying the
relation means that, for any consistent replacement of the
variables in the rule with specific binary trees and
integers, either the premises are not in the relation or the
conclusion is in the relation.

As an example, @term[(bounded-bst (node 1 leaf leaf) 1 2)]
is in the relation. We can use the leaf rule to conclude that
@term[(bounded-bst leaf 1 1)] and that @term[(bounded-bst leaf 1 2)].
With those two triples established, we can use the node rule to
show that @term[(bounded-bst (node 1 leaf leaf) 1 2)].

It is convenient to collect the rationale for any particular
triple's membership in the relation into a @emph{derivation},
where the justification for each step is written above the
it, in a shape that matches how the rules are used. For example,
this binary tree
@centered{
 @tree[(node 1
             leaf
             (node 2 leaf leaf))]
}
is related to the integers @term[1] and @term[2], as justified
by this derivation

@render-derivation[
 r:prelim
 (bounded-bst (node 1
                    leaf
                    (node 2 leaf leaf))
              1 2)]

Also note, it is impossible to build a derivation (for any integers)
that this is a binary search tree.
@centered{
 @tree[(node 1
             (node 2 leaf leaf)
             leaf)]
}

The definition of the rules for the relations can be quite
subtle, however. For example, imagine a relation that looks
almost the same as our binary-search tree relation, but that
does not have the premise in the leaf rule:

@render-judgment-rules[r:wrong-bst leaf node]

This does @emph{not} correspond to our usual understanding
of binary search trees. Indeed, every tree is in the relation
with any two integers, using these rules.
For example, here's a derivation that the bad tree shown
earlier is in the bad relation

@render-derivation[
 r:prelim
 (wrong-bst (node 1
                  (node 2 leaf leaf)
                  leaf)
            0 0)]

@section{Proving Properties: Induction on Relation Definitions}

@render-judgment-rules[r:in-bt here_bt left_bt right_bt]

@render-judgment-rules[r:in-bst here_bst left_bst right_bst]

@section{Contexts}

right rotate as a relation; reflexive-transitive closure as linearization using contexts

@section{Contexts and Proofs}

