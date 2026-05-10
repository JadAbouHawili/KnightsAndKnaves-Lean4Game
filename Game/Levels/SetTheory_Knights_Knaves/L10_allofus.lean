import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 10

Title ""

open Inhabitant'

Introduction
"
`A` says `B` is a knight

`B` says all of us are knights

`C` says `A` is a knight or `B` is a knight
"

Statement
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stB : B ∈ Knight ↔ Knight={A,B,C} }
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
: Knight={A,B,C} ∨ Knave={A,B,C}:= by
  Hint
  "
Let's consider the possibilities of `A`

`knight_or_knave A`
  "
  knight_or_knave A with AKnight AKnave
  Hint
  "
From `A`'s statement , conclude that `B ∈ Knight`
  "
  have BKnight := stA.mp AKnight
  Hint
  "
Conclude that everyone is a knight and close the goal
  "
  have := stB.mp BKnight
  left ; assumption

  Hint
  "
Now this is the case where `A ∈ Knave`

Interpret `stA` in terms of knaves
  "
  knave_interp at stA
  Hint
  "
Conclude `B ∈ Knave`
  "
  have BKnave := stA.mp AKnave
  Hint
  "
  Notice that neither `A` is a knight nor `B` is a knight , and so the statement `C` made is false.
  And so `C ∈ Knave`

  But first , interpret `C`'s statement in terms of knaves
  "
  knave_interp at stC
  Hint
  "
Simplify `stC` concluding that `C ∈ Knave`
  "
  simp [AKnave,BKnave] at stC
  Hint
  "
  Now everyone is a knave , choose that direction to prove the goal. It is the `right` direction
  "
  right
  Hint
  "
  When `A ∈ Knave` , `B ∈ Knave` , `C ∈ Knave` then we can conclude that everyone is a knave i.e
  `Knave = \{A,B,C}`

  `full3 (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) : Knave = \{A, B, C}` is useful here
  "
  exact full3 AKnave BKnave stC

Conclusion
"
"

NewTheorem full3
