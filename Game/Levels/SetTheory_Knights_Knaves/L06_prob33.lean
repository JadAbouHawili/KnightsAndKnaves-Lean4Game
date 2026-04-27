import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 6

Title "Intro"

Introduction
"
Suppose `A` says, 'I am a knave, but `B` isn't.'
What are `A` and `B`?

Change the goal to `A ∉ Knight`. You write `¬` by \\not.
"

-- changes made here , change corresponding dsl version
Statement
{stA : A ∈ Knight ↔ (A ∈ Knave  and  B ∉ Knave) }
: A ∈ Knave and B ∈ Knave := by
  have AnK : A ∈ Knave
  knight_interp
  Hint "
Assume `A` is a knight.
  "
  intro AKnight
  Hint
  "
Conclude that `A`'s statement is true.
  "
  have AKnave := stA.mp AKnight
  Hint (strict := true)
  "
Now you have that `A` is a knave, which is a contradiction

Remeber that `{AKnave}.left : A ∈ Knave`.
  "
  have AKnave := AKnave.left
  contradiction

  Hint
  "
Now that we know that `A` is not a knight, we know that what `A` said was a lie.

`knave_interp at stA`
  "

--Use
--```
--notknight_said
--    (stA : A said P)
--    ( notKnight : ¬isKnight A) : ¬P
--```
  -- doing this instead of introducing stAn
  knave_interp at stA
  simp [AnK] at stA
  constructor
  assumption
  assumption
  /- dsl goes on and on..
  have st := stAn.mp AnK
  Hint
  "
Use `not_and_or` at `{st}`
  "
  rw [not_and_or] at st
  Hint
  "
`A` is not a knight means that `A` is a knave, so `{st}` could be simplified.

Obtain `A.isKnave` using `knight_to_knave`, and simplify `{st}` obtaining `B.isKnave`.

After that, close the goal
  "
  set_knight_to_knave at AnK
  simp [AnK] at st

  constructor
  set_knight_to_knave
  assumption
  assumption
  -/

Conclusion
"
"
