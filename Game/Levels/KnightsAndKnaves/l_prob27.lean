import Game.Metadata_KnightsAndKnaves


World "KnightsAndKnaves" 
Level 

Title "" 

Introduction 
"
"

open settheory_approach
variable [DecidableEq Inhabitant]
def oneKnight {A B C : Inhabitant} : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)
Statement

{A B C : Inhabitant}
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ @oneKnight A B C))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )

  : B ∈ Knave ∧ C ∈ Knight := by 
  have : ¬B ∈ Knight 
  intro BKnight
  set_knave_to_knight B at stC
  set_knight_to_knave C at stC
  rw [not_iff_not] at stC  
  have CKnave := stC.mpr BKnight

  have oneK := stB.mp BKnight
  set_knight_or_knave A with AKnight AKnave
  have oneK := oneK.mp AKnight
  unfold oneKnight at oneK
  simp [AKnight, CKnave, BKnight] at oneK
  set_knave_to_knight A at oneK 
  set_knave_to_knight B at oneK 
  simp [ CKnave, BKnight] at oneK
  contradiction

  set_knave_to_knight A at AKnave
  rw [not_iff_not.symm] at oneK
  have notone := oneK.mp AKnave 
  unfold oneKnight at notone
  simp [AKnave, CKnave, BKnight] at notone
  set_knave_to_knight A at notone
  simp [AKnave] at notone

  set_knight_to_knave B at this
  simp [this,stC]

Conclusion 
"
"
