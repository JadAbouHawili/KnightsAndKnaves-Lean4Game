import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves


--World "" 
--Level 
--
--Title "" 
--
--Introduction 
--"
--"

/-
A says B is a knight
B says all of us are knights
C says A  is a knight or B is a knight
-/
open Islander

variable {A B C : Islander}
def allKnights := A.isKnight ∧ B.isKnight ∧ C.isKnight
def allKnaves := A.isKnave ∧ B.isKnave ∧ C.isKnave
#check allKnights
example 
{stA : A said B.isKnight}
{stB : B said (A.isKnight and B.isKnight and C.isKnight)}
{stC : C said A.isKnight or B.isKnight}
: (@allKnights A B C)  ∨ (@allKnaves A B C):= by 
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
