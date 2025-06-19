import Game.Metadata
--import Game.LevelLemmas.KnightsAndKnaves
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic
import Game.LevelLemmas.settheory

namespace settheory_approach

axiom  Inhabitant : Type
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant
axiom either (A : Inhabitant): A ∈ Knight or A ∈ Knave
variable [DecidableEq Inhabitant]
axiom dis : Knight ∩ Knave = ∅

def oneKnight {A B C : Inhabitant} : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

theorem disjoint_without
(Aleft : A ∈ Knight)
(Aright : A ∈ Knave)  : False := by
  have := Finset.mem_inter_of_mem Aleft Aright
  rw [dis] at this
  #check dis
  contradiction

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve | ( apply disjoint_without  ; repeat assumption) )

theorem IamKnave
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases either A with AKnight|AKnave

    · have := stA.mp AKnight
      exact disjoint_without AKnight this

    · have := stA.mpr AKnave
      exact disjoint_without this AKnave
  }

theorem IamKnaveIffFalse
: False ↔  (A ∈ Knight  ↔ (A ∈ Knave))
   := by
    constructor
    exact fun a => a.elim
    exact IamKnave

axiom isKnight_notisKnaveIff {A : Inhabitant} : A ∈ Knight ↔ A ∉ Knave

axiom isKnave_notisKnightIff {A : Inhabitant} : A ∈ Knave ↔ A ∉ Knight
-- *
macro "set_knight_to_knave" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff] at $t1)
-- goal
macro "set_knight_to_knave" : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff])
-- hypothesis
macro "set_knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
simp [isKnight_notisKnaveIff] at $t1)

-- *
macro "set_knave_to_knight" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [isKnave_notisKnightIff] at $t1)
-- goal
macro "set_knave_to_knight" : tactic =>
do`(tactic| simp [isKnave_notisKnightIff])
-- hypothesis
macro "set_knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic|
simp [isKnave_notisKnightIff] at $t1)

macro "set_knight_or_knave" t1:term  : tactic =>
do`(tactic| cases (either $t1)  )

macro "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat   : tactic =>
do`(tactic| obtain $t2|$t3 := (either $t1)  )
end settheory_approach

