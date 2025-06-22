import Mathlib.Data.Multiset.Basic

theorem notleft_right {P Q : Prop} (Or : P ∨ Q)(notleft : ¬P) : Q := by
  cases Or
  contradiction
  assumption

theorem notright_left {P Q : Prop} (Or : P ∨ Q)(notright : ¬Q) : P := by
  cases Or
  assumption
  contradiction

theorem IfToIff (h : p → q) (h' : ¬p → ¬q) : p ↔ q := by
  constructor
  · assumption
  · intro hq
    exact (Function.mtr h') hq

theorem IffToIf (h : p ↔ q) : (p → q) ∧ (¬p → ¬q) := by
  constructor
  · exact h.mp
  · exact Function.mt (h.mpr)
