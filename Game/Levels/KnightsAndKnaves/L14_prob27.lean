
import Game.Metadata_KnightsAndKnaves


World "KnightsAndKnaves" 
Level 

Title "" 

Introduction 
"
"

Statement 
  :  := by

  {

  }





Conclusion 
"
"

open settheory_approach
Statement
{A B C : Inhabitant}
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ @oneKnight A B C))
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  have : ¬B ∈ Knight 
  intro BKnight
  set_knave_to_knight at stC
  set_knight_to_knave at stC
  rw [not_iff_not.symm] at stC  
  simp at stC
  set_knave_to_knight at stC
  have CKnave := stC.mpr BKnight

  have oneK := stB.mp BKnight
  set_knight_or_knave A with AKnight AKnave
  have oneK := oneK.mp AKnight
  unfold oneKnight at oneK
  simp [AKnight, CKnave, BKnight] at oneK
  set_knave_to_knight at oneK 
  simp [ CKnave, BKnight] at oneK
  contradiction

  set_knave_to_knight at AKnave
  rw [not_iff_not.symm] at oneK
  have notone := oneK.mp AKnave 
  unfold oneKnight at notone
  simp [AKnave, CKnave, BKnight] at notone
  set_knave_to_knight at notone
  simp [AKnave] at notone
  contradiction

  set_knight_to_knave at this
  have CKnight := stC.mpr this
  constructor
  repeat assumption

