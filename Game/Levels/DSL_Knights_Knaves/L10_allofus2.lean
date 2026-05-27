import Game.MathlibTheorems
import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 10

Title "allKnights or allKnaves"

Introduction
"
`A` : All of us are knights

`B` : Exactly one of us is a knave
"

open Islander

#check allKnights
#check allKnaves
Statement
{stA : A said (A.isKnight ∧ B.isKnight)}
{stB : B said (A.isKnave ∨ B.isKnave)}
: A.isKnave := by
  Hint (strict := true)
  "
First, take cases for `B`.
  "
  knight_or_knave B
  Hint
  "
We are at the case where `B.isKnight`
Conclude that `B`'s statement is true
  "
  have all := knight_said stB h
  Hint
  "
Take cases for {all} and close the goal accordingly
  "
  cases all ; assumption
  contradiction

  Hint
  "
We are at the case where `B.isKnave`

Interpret this in terms of knights
  "
  knight_interp at h
  Hint
  "
So, `A`'s statement is false because `B` is not a knight

Conclude that `A` is a knave.

Remember the term `not_false : ¬False` a proof of `¬False`
  "
  simp [h] at stA
  have := said_knave stA not_false
  assumption

Conclusion
"
"

