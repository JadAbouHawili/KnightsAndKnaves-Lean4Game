import Game.Metadata


World "" 
Level 

Title "" 

Introduction 
"
"

/-
A says B is a knight
B says all of us are knights
C says A  is a knight or B is a knight
-/
open Islander

variable {A B C : Islander}
def allKnights := A.isKnight ∧ B.isKnight ∧ C.isKnight
example 
{stA : A said B.isKnight}
{stB : B said (A.isKnight and B.isKnight and C.isKnight)}
{stC : C said A.isKnight or B.isKnight}
: (@allKnights A B C) or (A.isKnight ∧ B.isKnight ∧ C.isKnight)  ∨ A.isKnave ∧ B.isKnave ∧ C.isKnave:= by 
-- proof state looks horrible

/-
  apply notisKnave_isKnight
  intro AKnave
  have BnK := knave_said stA AKnave
  have AnK := isKnave_notisKnight AKnave
  simp [AnK] at stB
  -/
   
  sorry






Conclusion 
"
"

/- Use these commands to add items to the game's inventory. -/

--NewTactic 
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

