import Game.Metadata
import Game.LevelLemmas.KnightsAndKnaves
-- environment
namespace settheory_approach
axiom  Inhabitant : Type
axiom Knight : Finset Inhabitant
axiom Knave : Finset Inhabitant
--axiom inst : DecidableEq Inhabitant
--variable ( inst : DecidableEq Inhabitant)
namespace test
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)
-- include command not in lean 4.7
--include a b c d e h1 h2 h3 h4

theorem T1 : a = e :=
  calc
    a = b := h1
    b = c + 1 := h2
    c + 1 = d + 1 := congrArg Nat.succ h3
    d + 1 = 1 + d := Nat.add_comm d 1
    1 + d = e := Eq.symm h4

#print T1
end test
-- theorem T1 : ∀ (a b c d e : Nat),
--   a = b → b = c + 1 → c = d → e = 1 + d → a = e := ...
variable [DecidableEq Inhabitant]
-- variable [DecidableEq Inhabitant]

axiom dis : Knight ∩ Knave = ∅ 
example {A : Inhabitant} {hA : A ∈ Knight } : 2=2 := by
  have := dis
  #check disjoint
  sorry

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
end settheory_approach
