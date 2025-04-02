import Game.Metadata_KnightsAndKnaves


World "" 
Level 

Title "" 

Introduction 
"
"

Statement 
  :  := by

  {

  }

-- prob 27
open settheory_approach
variable [DecidableEq Inhabitant]
/-
Suppose the stranger, instead of asking A what he is, 
asked A, "How many knights are among you?" Again A 
answers indistinctly. So the stranger asks B, "What did A 
say? B replies, "A said that there is one knight among us." 
Then C says, "Don't believe B; he is lying!" 
Now what are B and C? 
-/
def oneKnight {A B C : Inhabitant} : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

example
{A B C : Inhabitant}
--(h : Knight ∩ Knave = ∅ )
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔ @oneKnight A B C))
--(stBn : (B ∈ Knave) → (A ∈ Knight → ¬ (
--  (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)) ) )
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
--(stnC : ( C ∈ Knave → B ∈ Knight) )

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
