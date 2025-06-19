import Game.Metadata

World "KnightsAndKnaves2" 
Level 4

Title ""

Introduction
"
You have met a group of 3 islanders. Their names are `Xavier`, `Gary`, and `Alice`.

`Gary` says: `Alice` is my type.

`Alice` says: `Gary` never lies.

`Gary` says: `Xavier` never lies.
"

/-
use_module(library(clpb)).

sat( (G =:= (A =:= G) ) * (A =:= G ) * (G =:= X) ), labeling([A,G,X]).

G = A, A = X, X = 1.
-/

Statement
{Gary Xavier Alice : Prop}
{stG : Gary ↔ (Alice ↔ Gary)}
{stA : Alice ↔ Gary}
{stG2 : Gary ↔ Xavier}
: Alice ∧ Gary ∧ Xavier := by 
  Hint 
  "
Use `stA` and `stG` to prove `Gary`
  "
  Hint (hidden := true)
  "
Note that,
```
stG.mpr : (Alice ↔ Gary) ↔ Gary  
```
and so
```
stG.mpr stA : Gary
```
  "
  have G := stG.mpr stA
  Hint
  "
Use `Gary` to prove `Xavier` and `Alice` and close the goal.
  "
  have X := stG2.mp G
  have A := stA.mpr G
  exact ⟨A,G,X⟩

example
{Gary Xavier Alice : Prop}
{stG : Gary ↔ (Alice ↔ Gary)}
{stA : Alice ↔ Gary}
{stG2 : Gary ↔ Xavier}
: Alice ∧ Gary ∧ Xavier := by 
  Hint
  "
Start by proving `Alice`
  "
  have Al : Alice
  #check not_not.symm
 -- rw [not_not.symm]
  Hint
  "
To prove `Alice`, assume `¬Alice` then derive a contradiction
  "
  by_contra nAlice
  #check iff_false_right
  Hint
  "
  By `stA`, `Alice` and `Gary` are the same type so we can prove `¬Gary`. Change the goal to that.
  "
  have nGary: ¬Gary 
  Hint
  "
Simplify `stA` using `{nAlice}` to prove `¬Gary`
  "
  simp [nAlice] at stA
  assumption


  --have same : ¬Alice ↔ ¬Gary := by
  --  exact not_congr stA
  have same2 := iff_of_false nAlice nGary
  have Gary := stG.mpr same2
  contradiction

  have Ga := stA.mp Al
  have Xa := stG2.mp Ga
  constructor
  assumption
  constructor
  assumption
  assumption

Conclusion
"
"
