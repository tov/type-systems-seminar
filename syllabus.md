# Schedule

  - 01/09–11: Intro to type systems: [let/zl][letzl]

  - 01/16–18: [Simply-typed lambda calculus][stlc]

  - Subtyping with record types
     - Pre-reading: TAPL, Chapter 11 "Simple Extensions"
         - It looks long, but skip the exercises and skim some
         - Be sure to read the section on records, since we’ll be using that

  - System F
      - Pre-reading: Reynolds 1974, "Towards a Theory of Type Structure"
      (pages 1–8)
      - Parametricity?
      - Reading: Theorem for free?

  - Damas–Hindley–Milner type inference
      - Pre-reading: [Damas and Milner 1982, "Principal type-schemes for
        functional programs"][dm82]
      - Constraint-based inference?
         - Reading: Wand
         - Reading: Pottier and Rémy, "The Essence of ML Type Inference"

  - Qualified types
      - for overloading à la Haskell
      - for subtyping
      - evidence translation
    (Jones 1992, "A Theory of Qualified Types")

  - Higher-order and Dependent types
      - Lambda Cube: Barendregt, "Lambda Calculi with Types", §5 "Typing
        à la Church"
      - LF
      - CoC

  - Substructural types
      - Reading: Tov 2012, chapter 2

# Suggested presentation topics:

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

