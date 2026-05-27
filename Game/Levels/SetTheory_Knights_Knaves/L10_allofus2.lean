import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 10

Title ""

open Inhabitant'

Introduction
"
`A` : All of us are knights

`B` : Exactly one of us is a knave
"


/-
"
"
-/
Statement
{stA : A ∈ Knight ↔ (Knight={A,B}) }
{stB: B ∈ Knight ↔  (Knave={A} ∨ Knave={B}) }
  : A ∈ Knave := by
  {
    knight_interp
    intro AKnight
    have allKNight := stA.mp AKnight
    have : B ∈ Knight
    rw [allKNight] ; simp
    have oneKnave := stB.mp this
    rcases oneKnave with h|h
    have : A ∈ Knave
    rw [h] ; simp ; exact disjoint AKnight this

    have : B ∈ Knave
    rw [h] ; simp ; contradiction

}

NewTheorem disjoint
