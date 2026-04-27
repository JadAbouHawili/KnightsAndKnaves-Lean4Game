import GameServer.Commands
import Mathlib.Data.Multiset.Basic

theorem notleft_right {P Q : Prop} (Or : P ∨ Q)(notleft : ¬P) : Q := by
--  simp only [notleft, false_or] at Or
  cases Or
  contradiction
  assumption

theorem notright_left {P Q : Prop} (Or : P ∨ Q)(notright : ¬Q) : P := by
  cases Or
  assumption
  contradiction

#check Iff.symm
#check not_iff_comm
#check not_iff_not
theorem not_iff' {P Q : Prop}
 : ¬(P ↔ Q) ↔ (P ↔ ¬Q) := by
  rw [@iff_comm P Q]
  rw [@iff_comm P ¬Q]
  exact Classical.not_iff
  /-
  nth_rw 2 [(@not_not P).symm]
  rw [not_iff_not]
  exact Classical.not_iff
  -/

syntax "all_cases_satisfy_goal" term : tactic
macro_rules
    | `(tactic| all_cases_satisfy_goal $t1:term) =>
      `(tactic| first
        | (rw [($t1)]; assumption)  -- base case
        | (rcases ($t1) with h | h <;>
            first
            | (rw [h]; assumption)
            | all_cases_satisfy_goal h))
