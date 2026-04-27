
import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 10

Title ""

open Inhabitant'

Introduction
"
A says B is a knight
B says all of us are knights
C says A  is a knight or B is a knight
"

Statement
{stA : A ∈ Knight ↔ (B ∈ Knight) }
{stB : B ∈ Knight ↔Knight={A,B,C}}
{stC : C ∈ Knight ↔ A ∈ Knight ∨ B ∈ Knight}
: Knight={A,B,C} ∨ Knave={A,B,C}:= by
  knight_or_knave A with AKnight AKnave
  have BKnight := stA.mp AKnight
  have := stB.mp BKnight
  left ; assumption

  knave_interp at stA
  have BKnave := stA.mp AKnave
  knave_interp at stC
  simp [AKnave,BKnave] at stC
  right
  exact full3 AKnave BKnave stC

Conclusion
"
"
