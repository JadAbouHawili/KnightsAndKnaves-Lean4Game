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
  Hint 
  "
Let's start with proving that `A` is a knight. (use `have`)
  "
  have AKnight : A.isKnight 
  Hint
  "
  Change the goal to ¬isKnave A
  "
  knight_to_knave
  Hint "

Assume `isKnave A`
  "
  intro AKnave

  Hint
  "
Let's first prove `isKnave A or isKnave B`.

  "
  --apply said_knight at stA
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
  contradiction

  Hint "
`A` is a knight, so we can conclude `A`'s statement.
  "
  have orexp := knight_said stA AKnight
  Hint
  "
`orexp` can be simplified, using `simp` and the fact that `A` is a knight and that knights are not knaves.

  You could also obtain that `¬isKnave A` and use `notleft_right` to get `isKnave B`.

  After which, close the goal.
  "
  --apply notleft_right at orexp 
  --exact orexp (isKnight_notisKnave AKnight)
  --apply orexp
  simp [isKnight_notisKnave,AKnight] at orexp
  --contradiction
  constructor
  assumption ; assumption

Conclusion 
"
"
NewTactic knight_to_knave knave_to_knight
