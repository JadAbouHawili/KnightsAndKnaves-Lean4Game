import Game.Metadata


World "KnightsAndKnaves2" 
Level 3

Title ""

Introduction
"
Generated from [here](https://philosophy.hku.hk/think/logic/knights.php)

You have met a group of 3 islanders. Their names are Xavier, Gary, and Alice.

Gary says: Alice is my type.
Alice says: Gary never lies.
Gary says: Xavier never lies.
"

/-
use_module(library(clpb)).

sat( (G =:= (A =:= G) ) * (A =:= G ) * (G =:= X) ) , labeling([A,G,X]).

G = A, A = X, X = 1.
-/

Statement
{Gary Xavier Alice : Prop}
{stG : Gary ↔ (Alice ↔ Gary)}
{stA : Alice ↔ Gary}
{stG2 : Gary ↔ Xavier}
: Alice ∧ Gary ∧ Xavier := by 
  have Al : Alice
  #check not_not.symm
 -- rw [not_not.symm]
  by_contra nAlice
  #check iff_false_right
  have nGary: ¬Gary := by
    exact (iff_false_right nAlice).mp (id (Iff.symm stA))

  have same : ¬Alice ↔ ¬Gary := by
    exact not_congr stA
  have same2 := iff_of_false nAlice nGary
  have Gary := stG.mpr same2
  contradiction

  have Ga := stA.mp Al
  have Xa := stG2.mp Ga
  constructor <;> try constructor
  repeat assumption 

Conclusion
"
"
