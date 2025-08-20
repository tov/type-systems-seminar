#lang scribble/base

@(require "redex/prelim.rkt"
          (only-in "redex/prelim.rkt")
          "util.rkt"
          (only-in redex/reduction-semantics default-language)
          redex/pict
          (only-in scribble-math/dollar $ $$))

@(default-language prelim)
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
   @render-nonterminals[prelim bt z])

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
@render-nonterminals[prelim ℕ]
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

@theorem{For any @term[bt] with @${l} leaves and height @${h},
 @${l ≤ 2^h}.}

@itemlist[
 @item{ Case one: the tree is a leaf. In this case,
       we know @${l} is 1 and @${h} is 0, so specializing
       the claim, we get @${1 ≤ 2^0}, which is true.}

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
  @term[bt_1] and @term[bt_2]. So, we know that @${l_1 ≤
   2^{h_1}} and @${l_2 ≤ 2^{h_2}}.

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


QED.

@section{Defining Relations to Identify Desired Subsets}

In order to capture particular, preferred subsets of terms,
we will use relations on the sets of terms. The idea is that
these subsets will have some nice property that we are
interested in studying. As a first example, we can define a
relation that captures which trees are perfect binary trees.
A perfect binary tree is one where every path from the root
to a leaf has the same length. We write
@term[(perfect bt z)] to indicate that @term[bt] is a
perfect binary tree and all the paths to leaves have length
@term[z].

We define the relation inductively, just as the sets are
defined inductively, using rules. We write the rules are
written as sequents, meaning we write premises (assumptions)
above a bar and a conclusion below the bar, and a name for
the rule beside the bar. We take this to mean that whenever
some term satisfies the premises, then the conclusion is
true. Just like the definitions of the sets, the relations
are the smallest ones that satisfy the rules.

Let's clarify this with an example. Here are the rules for
perfect trees:

@render-judgment-rules[perfect leaf node]

The first rule says that it is always the case (i.e.,
requiring no assumptions), that leaf nodes are perfect trees
with a path-length of zero. The second rule says that, if
@term[bt_1] is a perfect tree of length @term[n] and so is
@term[bt_2], then the tree @term[(node z bt_1 bt_2)] is a
perfect tree of length @term[(meta-add1 n)].

It can be helpful to collect the rationale for any particular
tree's membership in the relation into a @emph{derivation},
where the justification for each step is written above the
it, in a shape that matches how the rules are used. For example,
@centered{
 @tree[(node 1
             (node 0 leaf leaf)
             (node 2 leaf leaf))]
}
is a perfect binary tree with path-length 2 and we can see how
that is derived in the relation by putting the final tree
at the bottom and stacking up the uses of the rules upwards.

@render-derivation[
 prelim
 (perfect (node 1
                (node 0 leaf leaf)
                (node 2 leaf leaf))
          2)]

Perfect trees have only certain fixed sizes; there is, for
example, no perfect tree that has four nodes in it. We can
generalize the idea of a perfect trees a little bit to allow
such trees by saying that every path from the root to a leaf
has either a length @term[n] or @term[(meta-sub1 n)] and,
furthermore, all of the paths of length @term[n] are to the
left and the paths of length @term[(meta-sub1 n)] are to the
right, when drawn out. Such trees are called complete trees.

For example, the tree on the left is a complete tree of size
four and the tree on the right is a tree of size four that
is not complete because the bottom row of nodes is not
filled in from the left.

@centered{
 @tree[(node 2
             (node 1 (node 0 leaf leaf) leaf)
             (node 3 leaf leaf))]
 @hspace[4]
 @tree[(node 2
             (node 0 leaf (node 1 leaf leaf))
             (node 3 leaf leaf))]
}

We'll write @term[(complete bt n)] to indicate that
@term[bt] is a complete tree that has paths that are either
of length @term[n] or of length @term[(meta-sub1 n)]. We can
define the relation in a manner similar to the definition
for perfect trees, using rules with assumptions and
conclusions:

@render-judgment-rules[complete leaf left right]

Note that these rules introduce a subtle point: with
complete trees, there are two different rules that can both
construct trees that end with a @term[node].

Here's an example derivation, showing how the rules capture
the complete tree with four nodes shown above; it uses both
variants of the @term[node] rule.

@render-derivation[
 prelim
 (complete (node 2
                 (node 1 (node 0 leaf leaf) leaf)
                 (node 3 leaf leaf))
           3)]

@;{
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
 prelim
 (perfect (node 1
                (node 0 leaf leaf)
                (node 2 leaf leaf))
          2)]

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
}

@section{Proving Properties by Induction using Relations}

Earlier, we showed an exponential upper bound on the number
of leaves in a tree. For an arbitrary tree, it is possible
to include just a few nodes such that there is just one more
leaf than the height of the tree. For example, here's a tree
with with a height of 4 and 5 leaves:

@centered{
 @tree[(node 1
             leaf
             (node 2
                   leaf
                   (node 3
                         leaf
                         (node 4
                               leaf
                               leaf))))]
}

For perfect and complete binary trees, however, there must
be many more leaves than the height. Let's start with
perfect trees, where there must be at least @${2^h} leaves.

To prove this, we need to do induction again, and on the
structure of the tree, but because we know that the tree is
complete, we will have more information at each stage but we
will also have more requirements to be able to use
induction. The additional information and the additional
requirement both comes from the definition of the
@term[(perfect bt z)] relation.

To be able to use the relation, we first prove a result that
connects the shape of the binary tree (i.e., which rule was
used to construct the tree) to the definition of the
relation. This lemma is called inversion, and each relation
comes with an inversion lemma.

@lemma[#:name "Inversion"]
If @term[(perfect bt n)] then,
 @itemlist[
 @item{If @term[bt] is @term[leaf] then @term[z] must be 0.}
 @item{If @term[bt] is @term[(node z bt_1 bt_2)] then @term[(perfect bt_1 (meta-sub1 n))] and
          @term[(perfect bt_2 (meta-sub1 n))]}]
@proof[] By inspection of the rules.


Equipped with the inversion lemma, we can prove the result
about perfect binary trees.

@theorem{For any binary tree @term[bt] with @${l} leaves and
 height @${h}, if @term[(perfect bt n)], then @${2^h ≤ l}.}

@proof[] By induction on the structure of the tree.

@itemlist[
 @item{ Case one: the tree is a leaf. In this case,
  we know @${l} is 1 and @${h} is 0, so specializing
  the claim, we get @${2^0 ≤ 1}, which is true.}
 @item{Case two: the tree is a node, so there are two other
  trees @term[bt_1] and @term[bt_2] as well as an integer
  @term[z] such that @term[bt] is
  @term[(node z bt_1 bt_2)]. Let's say that the height of
  @term[bt_1] is @${h_1} and it has @${l_1} leaves; also the
  height of @term[bt_2] is @${h_2} and it has @${l_2} leaves.
  
  Now, as in the previous proof, we can do induction using
  @term[bt_1] and @term[bt_2]. But, just as the theorem we are
  proving requires us to know that @term[bt_1] and @term[bt_2]
  are perfect, so too the inductive hypothesis requires us to
  show that the trees are perfect before we can use it. Here
  is where the assumption of @term[(perfect bt n)] and the
  inversion lemma come in. Since we know that
  @term[(perfect (node z bt_1 bt_2) n)] is true, by inversion
  we know that @term[(perfect bt_1 (meta-sub1 n))] and
  @term[(perfect bt_2 (meta-sub1 n))]. This lets us apply
  induction, telling us that @${2^{h_1} ≤ l_1} and @${2^{h_2}
   ≤ l_2}.

  Our original tree @term[bt] has all of the leaves of
  @term[bt_1] and @term[bt_2] and no more, so we know that
  @${l = l_1 + l_2}. Using the inequations we obtained by
  induction (and transitivity of ≤ and some facts about the
  relationship between + and ≤), we know that @$${l ≤
   2^{h_1} + 2^{h_2}} Also, because the path length to any
  leaf is always the same, we know that @${h_1 = h_2} and thus
  @$${l ≤ 2^{h_1} + 2^{h_1} = 2^{h_1 + 1}}
  Finally, @${h_1+1} is the height of the original tree @term[bt],
  so we obtain the final result.}
 ]

QED.

@exercise{Our proof above used the fact that if two trees
 @term[bt_1] and @term[bt_2] are both perfect with the same
 @term[n], i.e., @term[(perfect bt_1 n)] and
 @term[(perfect bt_2 n)], then the heights of the two trees
 are the same. Prove this fact using induction.
}

We can prove a similar result for complete trees; because
the definition of complete trees is more complex, the proof
requires a little more sophistication, as we shall see.

@section{Contexts and Relations that Capture Computation}

right rotate as a relation; reflexive-transitive closure as linearization using contexts


@section{Contexts and Proofs}

