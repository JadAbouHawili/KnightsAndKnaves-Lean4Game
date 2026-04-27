import Game.MathlibTheorems
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Game.LevelLemmas.settheory
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype
import Game.LevelLemmas.settheory_knightsknavesfoundation

inductive Inhabitant'
| A
| B
| C
deriving DecidableEq , Fintype

noncomputable instance world'' : World' Inhabitant' :=  by exact W

open Inhabitant'

macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant'  ; repeat assumption) )


theorem all' : ∀x : Inhabitant' , x = .A ∨ x = .B ∨ x = .C := by
  intro x
  cases x <;> aesop


def oneKnight  : Prop:=   (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) ∨ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knight)

def oneKnave  : Prop:=   (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) ∨ (A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave)

def allKnave : Prop := A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave

macro "by_universe3" : tactic =>
  `(tactic| (apply set_subset_univ3 ; intro x ; exact all x))
