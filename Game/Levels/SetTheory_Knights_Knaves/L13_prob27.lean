import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 13

Title ""

open Inhabitant'


Statement
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔(Knight : Finset Inhabitant').card = 1))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
  : B ∈ Knave ∧ C ∈ Knight := by
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  knight_interp at stC
  have CKnave := stC.mpr BKnight
  have stA := stB.mp BKnight
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have KnightCard := stA.mp AKnight
  rw [Finset.card_eq_one] at KnightCard
  have ⟨a,ha⟩ := KnightCard
  rw [ha] at AKnight
  rw [ha] at BKnight
  simp at AKnight
  simp at BKnight
  rw [←AKnight] at BKnight
  contradiction
  knight_interp at AKnave
  simp [AKnave] at stA
  have : (Knight : Finset Inhabitant').card = 1

  rw [Finset.card_eq_one]
  use B
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  assumption
  intro x h
  rcases all' x with h'|h'|h'
  rw [h'] at h ; contradiction
  assumption
  rw [h'] at h ; contradiction

  contradiction
  have CKnight := stC.mpr BKnave
  exact And.intro BKnave CKnight


Conclusion
"
"
