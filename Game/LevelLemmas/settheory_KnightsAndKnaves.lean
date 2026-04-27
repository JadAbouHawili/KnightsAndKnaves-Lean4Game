import Game.MathlibTheorems
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Game.LevelLemmas.settheory
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype
import Game.LevelLemmas.settheory_knightsknavesfoundation

inductive Inhabitant
| A
| B
deriving DecidableEq , Fintype

noncomputable instance world : World' Inhabitant :=  by exact W


#check Finset.mem_insert
#check Finset.mem_singleton
#check Finset.mem_univ

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )

open Inhabitant
theorem all : ∀x : Inhabitant , x = A ∨ x = B := by
  intro x
  cases x <;> aesop

macro "by_universe" : tactic =>
  `(tactic| (apply set_subset_univ2 ; intro x ; exact all x))

example (h : A ∈ Knight) : A ∉ (Knave : Finset Inhabitant) := by
  knight_interp
  sorry
