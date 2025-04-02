import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves


World "" 
Level 

Title "" 

Introduction 
"
"

-- prob 31
open Islander
set_option push_neg.use_distrib true
variable {A B C : Islander}
def oneisknight := (A.isKnight ∧ B.isKnave ∧ C.isKnave)  ∨(A.isKnave ∧  B.isKnight ∧ C.isKnave) ∨ (A.isKnave ∧ B.isKnave ∧  C.isKnight)
example 
{stA : A said @allKnaves A B C}
{stB : B said @oneisknight A B C}
: A.isKnave ∧ B.isKnight ∧ C.isKnave := by 
  have AKnave : ¬A.isKnight  
  intro AKnight
  have allknave := knight_said stA AKnight
  unfold allKnaves at allknave
  have AKnave := allknave.left 
  contradiction

  have notallknave := notknight_said stA AKnave 
  have BKnight : ¬B.isKnave
  intro BKnave
  have notoneknight := knave_said stB BKnave
  unfold oneisknight at notoneknight
  knight_to_knave at AKnave
  #check isKnight_notisKnaveIff
  simp [AKnave, BKnave , isKnave_notisKnightIff.mp BKnave, isKnave_notisKnightIff.mp AKnave] at notoneknight
  knight_to_knave at notoneknight
  unfold allKnaves at notallknave
  simp [AKnave, BKnave, notoneknight] at notallknave

  knave_to_knight at BKnight 
  have one := knight_said stB BKnight
  unfold oneisknight at one
  simp [AKnave,BKnight] at one
  knave_to_knight at one
  simp [AKnave,BKnight] at one
  knight_to_knave at one 
  knight_to_knave at AKnave
  simp [AKnave,BKnight,one]

Conclusion
"
"
