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

  knave_interp at stA
  Hint
  "
use `{AnK}` to simplify `stA`
  "
  simp [AnK] at stA
  constructor
  assumption
  assumption

Conclusion
"
"
