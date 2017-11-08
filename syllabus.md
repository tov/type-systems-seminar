# Topics

  - Intro: let/zl

  - Simply-typed lambda calculus

  - Subtyping with record types
     - Pre-reading: TAPL, Chapter 11 "Simple Extensions"
         - It looks long, but skip the exercises and skim some
         - Be sure to read the section on records, since we’ll be using that

  - System F
      - Pre-reading: Reynolds 1974, "Towards a Theory of Type Structure"
      (pages 1–8)
      - Parametricity?

  - Damas–Hindley–Milner type inference
      - Pre-reading: [Damas and Milner 1982, "Principal type-schemes for
        functional programs"][dm82]
      - soundness & completeness?
      - constraint-based inference
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

Presentation topics:

  - Extensible records and variants
  - Mixing Hindley-Milner and System F
  - Programming with linear types
  - Strong normalization for System F
  - Intersection types
  - What the heck is a monad?
  - Present an actual language from a type systems perspective
      - J or R or should (each?) do an example
  - Cardelli’s [Typeful Programming][cardelli] and Quest
  - ML pattern matching

[cardelli]:
   http://www.lucacardelli.name/Papers/TypefulProg.pdf

[dm82]:
    http://web.cs.wpi.edu/~cs4536/c12/milner-damas_principal_types.pdf
