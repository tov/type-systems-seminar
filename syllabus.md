# Type Systems Seminar (Winter 2018 @ Northwestern)

## Schedule

  - 01/09: [Intro to type systems: let/zl][letzl]

  - 01/11: continued

  - 01/16: [Simply-typed lambda calculus][stlc]

  - 01/18: continued

  - 01/23: [Subtyping with record types][lamsub]
     - Pre-reading: TAPL, Chapter 11 “Simple Extensions”
         - It looks long, but skip the exercises and skim some
         - Be sure to read the section on records, since we’ll be using that

  - 01/25: [System F][sysf]
      - Pre-reading: [Reynolds 1974, “Towards a Theory of Type
        Structure”][reynolds74] (pages 1–8)

  - 01/30: continued; final presentation discussion
      - Post-reading: [Wadler 1989, “Theorems for Free”][wadler89]

  - 02/01: [Damas–Hindley–Milner type inference][mlinf]
      - Pre-reading: [Damas and Milner 1982, “Principal type-schemes for
        functional programs”][dm82]

  - 02/06: Qualified types
      - Pre-reading: [Jones 1992, “A Theory of Qualified Types”][jones92]

  - 02/08: Occurrence Typing in Typed Racket
      - Pre-reading: [Tobin-Hochstadt 2010, “Logical Types for Untyped
        Languages”][samth2010]

  - 02/13: [Higher-order types][fomega] and dependent types
      - Pre-reading: Lambda Cube: [Barendregt, *Lambda Calculi with
        Types,*][barendregt] §5 “Typing à la Church”

  - 02/15: Dependent types continued

  - 02/20: Substructural types
      - Pre-reading: [Tov 2012, *Practical Programming with
        Substructural Types*][tov12], Chapter 2

  - 02/22: student-led [TBA]

  - 02/27: student-led [TBA]

  - 03/01: student-led [TBA]

  - 03/06: student-led [TBA]

  - 03/08: student-led [TBA]

  - 03/13: student-led [TBA]

  - 03/15: student-led [TBA]

## Grading

Your grade will be based on three things:

  - Class participation

  - An implementation of a type system that you write

  - The class that you lead (final presentation)

### Suggested presentation topics:

  - Extensible records and variants
  - Mixing Hindley-Milner and System F
  - Programming with linear types
  - Strong normalization for System F
  - Intersection types
  - What the heck is a monad?
  - Present an actual language from a type systems perspective
      - R should do an example (Typed Racket)
  - Cardelli’s [Typeful Programming][cardelli] and Quest
  - ML pattern matching

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
