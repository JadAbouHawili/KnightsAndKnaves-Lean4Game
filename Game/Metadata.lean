import GameServer.Commands
import Game.LevelLemmas.KnightsAndKnaves
import Game.LevelLemmas.settheory
--import Mathlib.Tactic
--import Mathlib.Util.Delaborators
import Mathlib.Tactic.Have
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.ApplyFun
--import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Basic

-- hide all this from the user

axiom Islander : Type

namespace Islander

axiom isKnight : Islander → Prop

axiom isKnave : Islander → Prop

axiom isKnight_or_isKnave (A : Islander) : A.isKnight ∨ A.isKnave

axiom not_isKnight_and_isKnave {A : Islander} : ¬ (A.isKnight ∧ A.isKnave)

axiom Said : Islander → Prop → Prop

/-
the following 4 axioms can be proven from the previous ones...
-/
theorem isKnight_notisKnave (A : Islander) : A.isKnight → ¬A.isKnave := by
  intro AKnight 
  intro AKnave
  apply not_isKnight_and_isKnave
  constructor
  assumption ; assumption
axiom isKnave_notisKnight (A : Islander) : A.isKnave → ¬A.isKnight
axiom notisKnight_isKnave (A : Islander) : ¬A.isKnight → A.isKnave
axiom notisKnave_isKnight (A : Islander) : ¬A.isKnave → A.isKnight

--------------
-- number affects where brackets will be needed
notation A " said " P:200 => Said A P
infixr:35 " and " => And
infixr:30 " or  "  => Or

axiom knight_said {A : Islander} {P : Prop} : (A said P) → A.isKnight → P
axiom said_knight {A : Islander} {P : Prop} : (A said P) →  P → A.isKnight 

theorem said_knave {A : Islander} {P : Prop} : A said P →  ¬P → A.isKnave := by 
  intro AsaidP
  intro nP
  apply notisKnight_isKnave 
  intro AKnight 
  have hP := knight_said AsaidP AKnight
  contradiction

section tactics
-- make custom tactics for finset.card stuff...

macro "knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat : tactic => do`(tactic| obtain ($t2 | $t3) := isKnight_or_isKnave $t1)

-- tell the user to use this instead of explaining stuff... this custom tactic hides not_isKnight_and_isKnave from the user and makes it so that the user doesn't need to interface with that directly.
--macro "contra_knight_knave" : tactic =>
--  `(tactic | (repeat (solve | apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption ) ))
--
macro "contra_knight_knave" : tactic =>
  `(tactic | ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ))

-- this creates a new macro contradiction, and extends the behavior of the contradiction tactic. but when seeing docstring, you don't get that its contradiction tactic
--macro "contradiction" : tactic =>
--  `(
--  tactic | 
--  first | 
--  ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ) | contradiction
--  )
macro "contradict2" : tactic =>
  `(tactic |  (solve | apply not_isKnight_and_isKnave | apply And.intro | assumption | assumption ) )

-- this truly extends contradiction tactic, preserving doc string
macro_rules
| `(tactic| contradiction) => 
  do `(tactic |first | ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ) )
--solve | contradiction ; contradict)

theorem knave_said {A : Islander} {P : Prop} : A said P → A.isKnave → ¬ P := by 
  intro AP
  intro AKnave
  intro hP
  have AKnight := said_knight AP hP

  contradiction
  --apply not_isKnight_and_isKnave
  --constructor <;>
  --assumption
example {hP : P} {hnP : ¬P} : False := by 
  contradiction
end tactics

end Islander

open Islander

-- Easy example
/-
A is a knight. A says that B is a knave. Prove that B is a knave.
-/
example {A B : Islander} (hA : A.isKnight) (hAB : A said B.isKnave) : B.isKnave := by
  exact knight_said hAB hA

/-
A : I am a Knave or B is a Knave.
-/
example {A B : Islander} (hAB : A said (A.isKnave or B.isKnave)) : A.isKnight and B.isKnave := by
  --have AnKnave : ¬IsKnave A
  --intro AKnave
  --have Or := knave_said hAB AKnave
  --rw [not_or] at Or
  --exact Or.left AKnave

  --have AKnight := notisKnave_isKnight A AnKnave
  --have Or := knight_said hAB AKnight
  --simp [AnKnave] at Or
  --exact And.intro AKnight Or
  --apply isKnight_notisKnave
  --intro IsKnight
  --have 
  knight_or_knave A with hA hA

  --obtain hA | hA := A.isKnight_or_isKnave
  · obtain hA' | hB := knight_said hAB hA
    · exact (not_isKnight_and_isKnave ⟨hA, hA'⟩).elim
    · exact ⟨hA, hB⟩
  · have := knave_said hAB hA
    tauto

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file lean file per world
that imports all its levels.
-/
