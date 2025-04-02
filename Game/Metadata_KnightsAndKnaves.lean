import Game.Metadata
import Game.LevelLemmas.KnightsAndKnaves
-- environment
namespace settheory_approach
axiom  Inhabitant : Type
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant
--axiom inst : DecidableEq Inhabitant
--variable ( inst : DecidableEq Inhabitant)
variable [DecidableEq Inhabitant]

axiom dis : Knight ∩ Knave = ∅ 

theorem disjoint_without
(Aleft : A ∈ Knight)
(Aright : A ∈ Knave)  : False := by 
  have := Finset.mem_inter_of_mem Aleft Aright
  rw [dis] at this
  contradiction

/-
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
-/
--example {h : Knight ∩ Knave = ∅ }
--: 2=2 := by
--  sorry

axiom either (A : Inhabitant): A ∈ Knight or A ∈ Knave 
-- *
macro "set_knight_to_knave" t2:term "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inleft_notinrightIff (either $t2) dis] at $t1)
-- goal
macro "set_knight_to_knave" t2:term : tactic =>
do`(tactic| simp [inleft_notinrightIff (either $t2) dis])
-- hypothesis
macro "set_knight_to_knave" t2:term "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| 
simp [inleft_notinrightIff (either $t2) dis] at $t1)

-- *
macro "set_knave_to_knight" t2:term "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [inright_notinleftIff (either $t2) dis] at $t1)
-- goal
macro "set_knave_to_knight" t2:term : tactic =>
do`(tactic| simp [inright_notinleftIff (either $t2) dis])
-- hypothesis
macro "set_knave_to_knight" t2:term "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| 
simp [inright_notinleftIff (either $t2) dis] at $t1)

macro "set_knight_or_knave" t1:term  : tactic =>
do`(tactic| cases (either $t1)  )

macro "set_knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat   : tactic =>
do`(tactic| obtain $t2|$t3 := (either $t1)  )
end settheory_approach
