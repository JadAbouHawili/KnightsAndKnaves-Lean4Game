import GameServer.Commands
--import Mathlib.Tactic
--import Mathlib.Util.Delaborators
import Mathlib.Tactic.Have
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Data.Multiset.Basic

infixr:35 " and " => And
infixr:30 " or  "  => Or
/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file lean file per world
that imports all its levels.
-/

theorem not_iff' {P Q : Prop}
 : ¬(P ↔ Q) ↔ (P ↔ ¬Q) := by
  #check Iff.symm
  #check not_iff_comm
  #check not_iff_not
  nth_rw 2 [(@not_not P).symm]
  rw [not_iff_not]
  exact Classical.not_iff
