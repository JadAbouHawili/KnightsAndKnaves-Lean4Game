import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Game.LevelLemmas.Logical
import Game.LevelLemmas.settheory
#check and_imp
#check and
theorem IamKnave
  {A : Inhabitant}
  [inst : DecidableEq Inhabitant]
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
(h : Knight ∩ Knave = ∅ )
(h1 : A ∈ Knight ∨ A ∈ Knave )
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases h1 with AKnight|AKnave

    · have := stA.mp AKnight
      exact disjoint h AKnight this

    · have := stA.mpr AKnave
      exact disjoint h this AKnave
  }

theorem IamKnaveIffFalse
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  (h : (Knight ∩ Knave) = ∅)
  (Or : (A ∈ Knight ∨ A ∈ Knave))
: False ↔  (A ∈ Knight  ↔ (A ∈ Knave))  
   := by
    constructor
    exact fun a => a.elim
    exact IamKnave h Or 

--axiom not_both
--  {Inhabitant : Type}
--  {A : Inhabitant}
--  {inst : DecidableEq Inhabitant}
--  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
--  (AKnight : A ∈ Knight) (AKnave : A ∈ Knave)  : False
macro_rules
| `(tactic| contradiction) => 
  do `(tactic |first | ( apply disjoint  ; repeat assumption) )
