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

In this level , we take a different approach when formalizing the statements of `A` and `B`
"

Statement
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant') = {A,B,C}}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant').card = 1}
: A ∈ Knave ∧ C ∈ Knight := by
  have AKnave: A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  have : A ∈ Knave
  rw [allKnave]
  simp ; contradiction

  knave_interp at stA
  have notallKnave := stA.mp AKnave
  knight_or_knave B with BKnight BKnave
  have oneKnave := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnave
  obtain ⟨a,ha⟩ :=oneKnave
  have CKnight : C ∈ Knight
  knave_interp
  intro CKnave

  grind
  grind
  constructor
  assumption
  knave_interp
  intro CKnave
  exact notallKnave (full3 AKnave BKnave CKnave)

Conclusion
"
"
