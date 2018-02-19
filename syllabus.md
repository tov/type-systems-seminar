# Type Systems Seminar (Winter 2018 @ Northwestern)

## Schedule

  - 01/09: [Intro to type systems: let/zl][letzl]

  - 01/11: continued

  - 01/16: continued

  - 01/18: continued

  - 01/23: [Simply-typed lambda calculus][stlc]

  - 01/25: continued

  - 01/30: [Subtyping with record types][lamsub]
     - Pre-reading: TAPL, Chapter 11 “Simple Extensions”
         - It looks long, but skip the exercises and skim some
         - Be sure to read the section on records, since we’ll be using that
      - Pre-task: Install up-to-date Racket and Racket package from
        GitHub: https://github.com/tov/type-systems-seminar

  - 02/01: [System F][sysf]
      - Pre-reading: [Reynolds 1974, “Towards a Theory of Type
        Structure”][reynolds74] (pages 1–8)

  - 02/06: continued, including [Higher-order types][fomega]; final
    presentation discussion
      - Post-reading: [Wadler 1989, “Theorems for Free”][wadler89]

  - 02/08: [Damas–Hindley–Milner type inference][mlinf]
      - Pre-reading: [Damas and Milner 1982, “Principal type-schemes for
        functional programs”][dm82]
      - Pre-task: [Get this OCaml program working][ocaml]

  - 02/13: [Qualified types][qual]
      - Pre-reading: [Jones 1992, “A Theory of Qualified Types”][jones92]
      - Pre-task: Install GHC.

  - 02/15: Occurrence Typing in Typed Racket
      - Pre-reading: [Tobin-Hochstadt 2010, “Logical Types for Untyped
        Languages”][samth2010]

  - 02/20: [Dependent types][lcube]
      - Pre-reading: Lambda Cube: [Barendregt, *Lambda Calculi with
        Types,*][barendregt] §5 “Typing à la Church”

  - ?: Substructural types
      - Pre-reading: [Tov 2012, *Practical Programming with
        Substructural Types*][tov12], Chapter 2

  - 02/22: Dan & Ethan: Rust
      - Pre-reading: [Tov 2012, *Practical Programming with Substructural Types*][tov12], Chapter 2, up to page 10, with particular emphasis on the typing rules on page 10.

  - 02/27: Jennie & Chris H.: intersection types

  - 03/01: Chris K. & Shu-Hung: Is inheritance subtyping?

  - 03/06: Sasha & Meg: Swift

  - 03/08: Nathan S. & Spencer: ReactiveML

  - 03/13: Sarah & Josh: JavaScript types

  - 03/15: Jared, Nathan L. & John: C++ templates (and concepts)

## Grading

Your grade will be based on three things:

  - Class participation

  - An implementation of a type system that you write

  - The class that you lead (final presentation)

## Presentations

### Presentation guidelines

To prepare for your presentation, plan to meet with us twice, once two
weeks before your presentation and once one week before your
presentation. 

For the first meeting, please prepare by reading up on your topic to
see if you need help to understand it. Come to the first meeting with
that understanding as well as these items:

1) a reading assignment (one technical paper is the most we want to assign)

2) specific worked exercises that you believe can be completed in
pairs if students generally understood the reading

One good approach to leading your class period is to start by asking
"did you understand the reading?" and then to answer the questions
that come up. If people generally seemed to have understood it, then
you'll give your prepared exercises. (If we spend the entire time
talking about the content of the reading, prepare to hand out the
exercises as self-study for those interested in digging into the topic
more.) Not all topics work well this way, so if you have one that you
think needs more explicit lecture-style content in the class, then
think about what that would look like too.

Expect that your first try at an exercise won't work, either because
it will be too hard, will send people in an uninteresting direction,
or just generally because designing good exercises isn't trivial.

Based on how it goes when you show us the materials in the first
meeting, we'll set you specific goals for the second meeting.

### Suggested presentation topics

  - Extensible records and variants
  - Mixing Hindley-Milner and System F
  - Programming with linear types
  - Strong normalization for System F
  - Intersection types
  - What the heck is a monad?
  - Present an actual language from a type systems perspective
      - Robby will do an example (Typed Racket)
  - Cardelli’s [Typeful Programming][cardelli] and Quest
  - ML module system

[cardelli]:
   http://www.lucacardelli.name/Papers/TypefulProg.pdf

[dm82]:
    http://web.cs.wpi.edu/~cs4536/c12/milner-damas_principal_types.pdf

[letzl]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/The_let-zl_language.html

[stlc]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/The_simply-typed_lambda_calculus__-st.html

[lamsub]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/_-sub__subtyping_with_records.html

[sysf]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/The_polymorphic_lambda_calculus__-2.html

[mlinf]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/ML_type_inference.html

[fomega]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/The_higher-order_lambda_calculus__-_.html

[lcube]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/The_Lambda_Cube___-cube.html

[qual]:
    http://users.eecs.northwestern.edu/~jesse/course/type-systems/main/Qualified_types.html

[wadler89]:
    https://people.mpi-sws.org/~dreyer/tor/papers/wadler.pdf

[reynolds74]:
    http://repository.cmu.edu/cgi/viewcontent.cgi?article=2289&context=compsci

[jones92]:
    http://web.cecs.pdx.edu/~mpj/pubs/rev-qual-types.pdf

[tov12]:
    http://users.eecs.northwestern.edu/~jesse/pubs/dissertation/tov-dissertation-screen.pdf

[barendregt]:
    https://github.com/tov/type-theory-seminar/blob/master/reading/Barendregt%20-%20Lambda%20Calculi%20with%20Types.pdf

[samth2010]:
    https://www.ccs.neu.edu/racket/pubs/icfp10-thf.pdf

[ocaml]:
      https://github.com/tov/type-systems-seminar/blob/master/exercises/stlc-ml/README.md
