--import Game.Metadata
--import Mathlib


import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.ApplyFun
theorem contrapositive (forward: P → Q) :  ¬Q → ¬P := by

  {

    intro nq
    intro p
    exact nq (forward p)
  }




theorem disjunctiveSyllogism (h : P ∨ Q) (np : ¬P)
  : Q := by

  {
  /-
    apply Or.elim (Classical.em Q)
    intro hQ
    assumption 

    intro hnQ 
    have := And.intro np hnQ
    rw [not_or.symm] at this
    contradiction
    -/
  cases h
  · contradiction
  · assumption
  }


