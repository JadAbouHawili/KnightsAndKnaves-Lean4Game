
import Game.LevelLemmas.settheory_KnightsAndKnaves

open Inhabitant

World "SetTheory_Knights_Knaves"
Level 4

Title "Intro"

Introduction
"
`A` says 'I am a knave or `B` is a knave'.
"

Statement
{stA : A ∈ Knight ↔ (A ∈ Knave or B ∈ Knave)}
: A ∈ Knight and B ∈ Knave := by
  Hint (strict:=true)
  "
Let's start with proving that `A` is a knight. (use `have`)
  "
  have AKnight : A ∈ Knight
  Hint (strict := true)
  "
  Change the goal to `A ∉ Knave` using the `knave_interp` tactic
  "
  knave_interp
  Hint
  "
Assume `A ∈ Knave`
  "
  intro AKnave

  Hint (strict := true)
  "
Let's first prove `A ∈ Knave ∨ B ∈ Knave`. Type `∨` by \\or.
  "
  have orexp: A ∈ Knave or B ∈ Knave
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
  have AKnight := stA.mpr orexp
  Hint
  "
But we already knew that `A` is a knave, `contradiction`.
  "
  contradiction

  -- AKnight : A ∈ Knight
  Hint "
`A` is a knight, so we can conclude `A`'s statement.
  "
  have orexp := stA.mp AKnight
  -- orexp : A ∈ Knave or B ∈ Knave
  Hint
  "
`{orexp}` can be simplified, using `simp` and the fact that `A` is a knight and that knights are not knaves.

  First, change `A ∈ Knave` in `{orexp}` to `A ∉ Knight` then use `simp` and the fact that `A` is a knight to simplify `{orexp}`
  "
  knight_interp at orexp
  simp [AKnight] at orexp

  Hint
  "
Now close the goal
  "
  knave_interp at orexp
  constructor
  assumption ; assumption

Conclusion
"
"
