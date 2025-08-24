#lang scribble/base

@(require "redex/prelim.rkt"
          (only-in "redex/prelim.rkt")
          "util.rkt"
          (only-in redex/reduction-semantics default-language)
          redex/pict
          (only-in pict htl-append)
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
leaves. Here is the definition of the height of a binary tree:
@render-metas[height]

@theorem{For any @term[bt] with @${l} leaves and height @${h},
 @${l ≤ 2^h}.}

@proof[] We have two cases to consider, based on the two ways
we can have elements of the set of binary trees.
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
 @item{If @term[bt] is @term[(node z bt_1 bt_2)] then @term[n] must be
  at least @term[1] and @term[(perfect bt_1 (meta-sub1 n))] and
          @term[(perfect bt_2 (meta-sub1 n))]}]
@proof[] By inspection of the rules.


Equipped with the inversion lemma, we can prove the result
about perfect binary trees.

@theorem{For any binary tree @term[bt] with @${l} leaves and
 height @${h}, if @term[(perfect bt n)], then @${2^h = l}.}

@proof[] By induction on the structure of the tree.

@itemlist[
 @item{ Case one: the tree is a leaf. In this case,
  we know @${l} is 1 and @${h} is 0, so specializing
  the claim, we get @${2^0 = 1}, which is true.}
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
  induction, telling us that @${2^{h_1} = l_1} and @${2^{h_2}
   = l_2}.

  From here, we have to do algebraic manipulations to obtain
  the goal. Let's start by adding the left- and right-hand
  sides of the facts we obtained from induction to get
  @$${2^{h_1} + 2^{h_2} = l_1 + l_2}
  Since our original tree @term[bt] has all of the leaves of
  @term[bt_1] and @term[bt_2] and no more, we can simplify
  the right-hand side to just @${l}:
  @$${2^{h_1} + 2^{h_2} = l}
  Because the path length to any
  leaf is always the same, we know that @${h_1 = h_2} and thus
  we know that
  @$${2^{h_1} + 2^{h_1} = l}
  Using properties of the exponential function we
  can simplify the left-hand side:
  @$${2^{h_1+1} = l}
  Furthermore, using the fact that @${h_1} and @${h_2}
  are the same and a property of @${max}, we can adjust
  the left-hand side to 
  @$${2^{max(h_1,h_2)+1} = l}
  Now, the left-hand side looks like the definition of the
  height function, so we can replace it with @${h}:
  @$${2^h = l}
  which completes the proof.}
 ]

QED.

@exercise{Our proof above used the fact that if two trees
 @term[bt_1] and @term[bt_2] are both perfect with the same
 @term[n], i.e., @term[(perfect bt_1 n)] and
 @term[(perfect bt_2 n)], then the heights of the two trees
 are the same. It is possible to prove this fact using
 induction, but a simpler fact to prove is that if
 @term[(perfect bt n)], then the height of @term[bt] is
 @term[n], and it implies the desired lemma. Prove it.
}

Complete trees do not have a simple characterization for the
exact number of leaves, but there still have to be many
leaves compared to the example from the start of this
section. In particular, we can bound the number of leaves in
a complete tree from below; in a complete binary tree of
height @${h} must be at least @${2^{h-1}} leaves.

Because the definition of complete trees is more complex,
the proof requires a little more sophistication. To start we
need an inversion lemma.

@lemma[#:name "Inversion"]
If @term[(complete bt n)] then,
 @itemlist[
 @item{If @term[bt] is @term[leaf] then @term[z] must be 0.}
 @item{If @term[bt] is @term[(node z bt_1 bt_2)] then either
  @itemlist[
 @item{
    @term[n] is at least 1,
    @term[(perfect bt_1 (meta-sub1 n))], and
    @term[(complete bt_2 (meta-sub1 n))], or}
 @item{
    @term[n] is at least 2,
    @term[(complete bt_1 (meta-sub2 n))], and
    @term[(perfect bt_2 (meta-sub1 n))]}]}]
@proof[] By inspection of the rules.

@theorem{For any complete tree @term[bt] with @${l} leaves and
 height @${h}, if @term[(complete bt n)], then @${2^{h-1} ≤ l}.}

@proof[] By induction on the structure of the tree.

@itemlist[
 @item{ Case one: the tree is a leaf. In this case,
  we know @${l} is 1 and @${h} is 0, so specializing
  the claim, we get @${2^{-1} ≤ 1}, which is true.}
 @item{ Case two: the tree is @term[(node z bt_1 bt_2)].
  Let's say we have @term[bt_1] has height @${h_1} and @${l_1} leaves, 
  and that @term[bt_2] has height @${h_2} and @${l_2} leaves.
  
  Since the addition of one in the definition
  of the height and the subtraction of one from the theorem
  statement cancel out, our goal is that
  @$${2^{max(h_1,h_2)} ≤ l_1 + l_2}
                              
  Inversion tells us we have two subcases
  @itemlist[
 @item{@term[n] is at least 1,
    @term[(perfect bt_1 (meta-sub1 n))], and
    @term[(complete bt_2 (meta-sub1 n))].
    In this case, we can use our earlier theorem about perfect trees to
    conclude that @${2^{h_1} ≤ l_1} and induction to conclude that
    @${2^{h_2-1} ≤ l_2}. Furthermore, by the proof in the exercise above and
    the one in the exercise below, we know that the height of @term[bt_1]
    and @term[bt_2] are both @term[n_1] and thus equal to each other, so let's
    replace the @${h_2}s in the goal with @${h_1},
    and we can simplify the use of @${max}. So, our
    our goal specializes to
    @$${2^{h_1} ≤ l_1 + l_2}
    From the induction on @term[bt_1], and since adding @${l_2} onto
    @${l_1} does not decrease it, we have finished this case.
    
    }
 @item{In the other subcase, we know that @term[n] is at
    least 2, @term[(complete bt_1 (meta-sub2 n))], and
    @term[(perfect bt_2 (meta-sub1 n))]. As in the previous case,
    by the results from the two exercises, we know that the
    @${max} expression in the goal specializes to @${h_2},
    meaning our goal becomes @$${2^{h_2} ≤ l_1 + l_2} We can
    also use the previous result about perfect trees to conclude
    that @${2^{h_2} = l_2}, which gives us the overall result. }]
  }
 ]

@exercise{Show that, if we know that @term[(complete bt n)], then
 the height of @term[bt] is @term[n].
}

@section{Contexts and Relations that Capture Computation}

Beyond using relations to capture particular desirable
subsets of the sets we have defined, we can also use
relations to capture a form of computation, where we relate
one element of a set to another one. The interpretation of
these relations will be that some small amount of
computation has occurred to transform one tree into the
other one.

For our binary trees, we'll use a relation that, step by
step, adds up the values in nodes, removing one node at a
time as it does so. The relation is written
@term[(--> bt_1 bt_2)] to indicate that we can add two
integers together in @term[bt_1] and update the tree by
removing one of the nodes to produce @term[bt_2].

Before we define the relation, we need to introduce the idea
of a @emph{context}. In particular we will write
@term[(in-hole C bt)], to @emph{decompose} a binary tree
into two pieces, a @emph{context} @term[C], which is a
binary tree with a specific spot called the @emph{hole}
somewhere inside it, plus another binary tree that is placed
at the hole in the context.

Here is the definition of the set of contexts @term[C]; they
use the same grammar-based definition technique as before,
but when we define them, we ensure that the definition is
formulated so that there is exactly one hole, written
@term[hole], in each element of the set @term[C].

@render-nonterminals[prelim C]

As an example, on the left we have an element of the set
@term[C], and on the right we have an ordinary binary tree.

@centered{
 @term[(node 4
             (node 2
                   (node 1 leaf leaf)
                   (node 3 leaf leaf))
             hole)]
 @hspace[4]
 @term[(node 1
             (node 1 leaf leaf)
             (node 1
                   leaf
                   leaf))]
}

Contexts can also be drawn as trees, but we just write
@term[hole] somewhere at the bottom. Here's the same context
and tree:

@centered{
 @tree[(node 4
             (node 2
                   (node 1 leaf leaf)
                   (node 3 leaf leaf))
             hole)]
 @hspace[4]
 @tree[(node 1
             (node 1 leaf leaf)
             (node 1
                   leaf
                   leaf))]
}

We can combine them by placing the tree in the hole:

@centered{
 @term[(node 4
             (node 2
                   (node 1 leaf leaf)
                   (node 3 leaf leaf))
             (node 1
                   (node 1 leaf leaf)
                   (node 1 leaf leaf)))]
}

Or, drawn as a tree:
@centered{
  @tree[(node 4
             (node 2
                   (node 1 leaf leaf)
                   (node 3 leaf leaf))
             (node 1
                   (node 1 leaf leaf)
                   (node 1 leaf leaf)))]
}

Contexts offer great expressiveness in defining relations
because we can factor out the specific computational step
from the place where it occurs inside the tree. Here is the
the definition of the relation to illustrate the idea.

@render-judgment-rules[--> two\ children one\ child]

This relation has two rules. First, focus on the part inside
the hole in the first rule. In the portion before the arrow,
it has a node with two children that each have two leaves
for children. In the portion after the arrow, we remove the
right child, and update the left child's value to be the sum
of the two values in the original children. The second rule
is similar, but this time the outer node has one node for a
child and a leaf, and we sum the values into the node.

Because the rules are each surrounded with
@term[(in-hole C ...)], it means that the rules can apply in
any context in the set @term[C]. The simplest such context
is just @term[hole], meaning that the relation relates these
two trees by the first rule:
@centered{
 @(htl-append
   40
   @tree[(node 1
             (node 1 leaf leaf)
             (node 1 leaf leaf))]
   @tree[(node 1 (node 2 leaf leaf) leaf)])
}

But because the @term[C] in the rule can be an arbitrary
element of the set @term[C], it might also have been the
example above, meaning that these two trees are also related
by the relation, as are many others.

@centered{
  @tree[(node 4
             (node 2
                   (node 1 leaf leaf)
                   (node 3 leaf leaf))
             (node 1
                   (node 1 leaf leaf)
                   (node 1 leaf leaf)))]
   @hspace[4]
   @tree[(node 4
             (node 2
                   (node 1 leaf leaf)
                   (node 3 leaf leaf))
             (node 1
                   (node 2 leaf leaf)
                   leaf))]
}

@section{Contexts and Proofs}

The two rules in the definition of the
@term[(--> bt_1 bt_2)] relation are enough to reduce every
binary tree that has any numbers to one that contains just a
single number. Additionally, it is even possible to reduce
every complete tree to another complete tree. Let us attempt
a proof.

@theorem[]
 For every binary tree @term[bt], if @term[(complete bt n)], then
 either
 @itemlist[
 @item{ @term[bt] is @term[leaf] }
 @item{ @term[bt] is @term[(node z leaf leaf)] for some @term[z], or }
 @item{ There is a @term[bt_′] and @term[(complete bt n_′)] for some
   @term[n_′] and @term[(--> bt bt_′)].}
 ]

As stated, this theorem is true, but not amenable to
induction. Let's see what goes wrong.

@not-proof[] By induction on @term[bt].
@itemlist[
 @item{
  @term[bt] is @term[leaf], which is one of the cases in the conclusion.
 }
 @item{ @term[bt] is @term[(node z bt_1 bt_2)] for some
  @term[z], @term[bt_1], and @term[bt_2].
  Since @term[(complete bt n)], by inversion we know that
  there are two subcases. Let's focus on the first one
  to see where the proof goes wrong. It says that
  @term[n] is at least 1,
  @term[(perfect bt_1 (meta-sub1 n))], and
  @term[(complete bt_2 (meta-sub1 n))]. Since we know that
  @term[bt_2] is complete, we can apply induction, which gives us
  three possibilities. The first one is that
  @term[bt_2] is @term[leaf] and the second one is that
  @term[bt_2] is @term[(node z_2 leaf leaf)], and these are not problematic.

  In the third situation that induction gives us, we know
  that there is a @term[bt_2′] such that
  @term[(complete bt_2′ n_2)] for some @term[n_2], and
  @term[(--> bt_2 bt_2′)]. At this point, we might wish to say
  that binary tree @term[(node z bt_1 bt_2′)] is complete to
  finish this case. Unfortunately, all we know is that
  @term[(complete bt_2′ n_2)] and we need to know that
  @term[(complete bt_2′ n)]. In particular, we do not know
  that @term[n] is the same as @term[n_2]. And, in fact, it
  might not be! For example, the tree
  @centered{@tree[(node 1 (node 1 leaf leaf) leaf)]} is
  complete with height 2, and it is related to
  @centered{@tree[(node 2 leaf leaf)]} by the
  @rulename[one\ child] rule, but that binary tree has height 1.

  This does not make the theorem false, however. What has
  gone wrong is that our inductive hypothesis is not strong
  enough. That is, the information we learn from induction is
  weaker than what is actually true. This is one of the
  essential truths when working with proofs by induction:
  sometimes we have to prove state a stronger result to be
  able to get useful facts from induction. Indeed, this
  becomes a balancing act, as stating a strong result gives us
  more information from induction, but also means we have to
  establish harder-to-prove goals.
  }]
