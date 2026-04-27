import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 11

Title ""

open Inhabitant

Title "allKnaves, exactlyOneIsKnave"

Introduction
"
`A`: All of us are knaves.

`B`: Exactly one of us is a knave.

In this level , we take a different approach when formalizing the statements of `A` and `B`

explain how this is equivalent to Knave={A,B,C}
"

Statement
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant).card = 3}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant).card = 1}
: A ∈ Knave ∧ C ∈ Knight := by
  -- create a custom tactic that would transform stA into stAn and vice versa
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have allKnave := stA.mp AKnight
  have Knavesubset: Knave ⊆ {A,B,C}
  by_universe
  have KnaveAll: Knave = {A,B,C}
  apply eq_of_subset_card_eq Knavesubset
  -- doing simp would just work
  #check Finset.card_insert_of_notMem
  simp
  assumption
  have AKnave : A ∈ Knave
  rw [KnaveAll] ; simp
  contradiction

  constructor
  assumption

  knave_interp
  intro CKnave
  knight_or_knave B with BKnight BKnave
  have oneKnave := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnave
  have ⟨a,ha⟩ := oneKnave
  rw [ha] at AKnave
  rw [ha] at CKnave
  simp at AKnave
  simp at CKnave
  rw [←CKnave] at AKnave
  contradiction
  /-
  -- reasong is too roundabout
  have knaveSub : {A,C} ⊆ Knave
  intro x h
  mem_finset at h
  rcases h with h|h
  rw [h] ; assumption
  rw [h] ; assumption

  have : 2 ≤ Knave.card
  #check Finset.card_le_card
  have := Finset.card_le_card knaveSub
  have : ({A,C} : Finset Inhabitant).card = 2
  rw [Finset.card_eq_two]
  use A
  use C
  constructor
  exact AneC
  trivial
  rw [←this] ; assumption

  rw[oneKnave] at this ; contradiction
  -/

  have : Knave.card=3
  rw [Finset.card_eq_three]
  use A,B,C
  simp
  #check eq_of_subset_card_eq
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  --rcases h with h|h|h
  --`(tactic| (cases $t1 ; assumption ; (next h''' => all_cases_satisfy_goal h''')))

  --rcases h with @h'

 ---- <;> next h => sorry
  --have h_1 : 2=2 := sorry
  --cases h

  --rcases h
  all_cases_satisfy_goal h
  knave_interp at stA
  have := stA.mp AKnave
  contradiction

Conclusion
"
"
