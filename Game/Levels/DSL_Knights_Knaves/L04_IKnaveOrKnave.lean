import Game.Metadata

import Game.LevelLemmas.dsl_KnightsAndKnaves

World "DSL_Knights_Knaves"
Level 4

Title ""
-- prob 28
--A: 'At least one of us is a knave.'
--What are A and B?
Introduction
"
`A` says 'I am a knave or `B` is a knave'.
"

open Islander
Statement
{A B : Islander}
{stA : A said (A.isKnave or B.isKnave)}
: A.isKnight and B.isKnave := by
  Hint (strict:=true)
  "
Let's start with proving that `A` is a knight. (use `have`)
  "
  have AKnight : A.isKnight
  Hint (strict := true)
  "
  Change the goal to `¬isKnave A` using the `knight_to_knave` tactic
  "
  knight_to_knave
  Hint
  "
Assume `isKnave A`
  "
  intro AKnave

  Hint (strict := true)
  "
Let's first prove `isKnave A ∨ isKnave B`. Type `∨` by \\or.
  "
  have orexp: isKnave A or isKnave B
  Hint
  "
Choose which side to prove, `left` or `right`?
  "
  left
  assumption
  Hint
  "
  `A`'s statement is true, so `A` is a knight.
  "
  have AKnight := said_knight stA orexp
  Hint
  "
But we already knew that `A` is a knave, `contradiction`.
  "
  contradiction

  Hint "
`A` is a knight, so we can conclude `A`'s statement.
  "
  have orexp := knight_said stA AKnight
  Hint
  "
`{orexp}` can be simplified, using `simp` and the fact that `A` is a knight and that knights are not knaves.

  First, change `isKnave A` in `{orexp}` to `¬isKnight A` then use `simp` and the fact that `A` is a knight to simplify `{orexp}`
  "
  knave_to_knight at orexp
  simp [AKnight] at orexp

  Hint
  "
Now close the goal
  "
  knight_to_knave at orexp
  constructor
  assumption ; assumption

Conclusion
"
"
NewTactic knight_to_knave
