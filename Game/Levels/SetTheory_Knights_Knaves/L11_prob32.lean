import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 11

Title ""

open Inhabitant'

Title "allKnaves, exactlyOneIsKnave"

Introduction
"
`A`: All of us are knaves.

`B`: Exactly one of us is a knave.

In this level , we take a different approach when formalizing the statements of `A` and `B` than the
corresponding `DSL` level
"

Statement
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant') = {A,B,C}}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant').card = 1}
: A ∈ Knave ∧ C ∈ Knight := by
  Hint
  "
Let's start by proving `A ∈ Knave`
  "
  have AKnave: A ∈ Knave
  Hint
  "
Interpret the goal in terms of knights and assume `A ∈ Knight`
  "
  knight_interp
  intro AKnight
  Hint
  "
Conclude that everyone is a knave from `stA`
  "
  have allKnave := stA.mp AKnight
  Hint
  "
This is means that `A ∈ Knave` which is a contradiction. Change the goal to `A ∈ Knave`
  "
  have : A ∈ Knave
  Hint
  "
`rw [{allKnave}]`
  "
  rw [allKnave]
  Hint
  "
`simp` will do the job
  "
  simp
  Hint
  "
We now have a `contradiction`
  "
  contradiction

  Hint
  "
  Since we have proven that `A ∈ Knave` , let's intrepret `stA` in terms of knaves
  "
  knave_interp at stA
  Hint
  "
Conclude not everyone is a knave
  "
  have notallKnave := stA.mp AKnave
  Hint
  "
Let's close the first part of the goal using `constructor` and `{AKnave}`
  "
  constructor ; assumption
  Hint
  "
Let's think about each case of `B`

If `B` were a knight then by `stB` we know there is only one knave(which would be `A`) so `C ∈
Knight`. This we can use to close the goal directly

If `B` were a knave then if we were to assume that `C ∈ Knave` we can derive a contradiction because
everyone would be a knave contradicting `{notallKnave}`.

Take cases for `B`
  "
  Hint (hidden:=true)
  "
In both cases we can close the goal so do `knight_or_knave B with BKnight BKnave`
  "
  knight_or_knave B with BKnight BKnave
  Hint
  "
`B` is a knight then by `stB` we know there is only one knave
  "
  have oneKnave := stB.mp BKnight
  Hint
  "
`rw [Finset.card_eq_one] at {oneKnave}`
  "
  rw [Finset.card_eq_one] at oneKnave
  Hint
  "

  obtain ⟨a,ha⟩ :={oneKnave}
(which would be `A`) so `C ∈
Knight`. This we can use to close the goal directly
  "
  obtain ⟨a,ha⟩ :=oneKnave
  have CKnight : C ∈ Knight
  knave_interp
  intro CKnave

  grind
  grind
  knave_interp
  intro CKnave
  exact notallKnave (full3 AKnave BKnave CKnave)

Conclusion
"
"
