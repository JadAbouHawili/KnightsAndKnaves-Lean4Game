
import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 10

Title ""

open Inhabitant

Introduction
"
"
/-
A says B is a knight
B says all of us are knights
C says A  is a knight or B is a knight
-/
-- to get by_universe, need knightsknaves_3 in scratch/kknprobs setup but that file needs cleanup so skip for now
Statement
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stAn : A ∈ Knave ↔ ¬ (B ∈ Knight) }
{stB : B ∈ Knight ↔Knight={A,B,C}}
{stBn : B ∈ Knave ↔ ¬Knight={A,B,C}
}
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
{stCn : C ∈ Knave ↔ ¬ (A ∈ Knight ∨ B ∈ Knight)}
: Knight={A,B,C} ∨ Knave={A,B,C}:= by
  knight_or_knave A with AKnight AKnave
  have BKnight := stA.mp AKnight
  simp [AKnight] at stC
  left
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  -- custom tactic , all cases true
  all_cases_satisfy_goal h

  have BKnave := stAn.mp AKnave
  knight_interp at AKnave
  simp [AKnave,BKnave] at stCn
  right
  apply Finset.Subset.antisymm
  by_universe
  intro x h
  simp at h
  knave_interp at AKnave
  knave_interp at BKnave
  all_cases_satisfy_goal h

Conclusion
"
"
