--import Mathlib.Tactic
import Game.Metadata
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.ApplyFun

-- hide all this from the user

axiom Islander : Type

namespace Islander

axiom isKnight : Islander → Prop

axiom isKnave : Islander → Prop

axiom isKnight_or_isKnave (A : Islander) : A.isKnight ∨ A.isKnave

axiom not_isKnight_and_isKnave (A : Islander) : ¬ (A.isKnight ∧ A.isKnave)

axiom Said : Islander → Prop → Prop
notation A " said " P:200 => Said A P

/-
the following 4 axioms can be proven from the previous ones...
-/
theorem isKnight_notisKnave {A : Islander} : A.isKnight → ¬A.isKnave := by
  intro AKnight 
  intro AKnave
  apply not_isKnight_and_isKnave
  constructor
  assumption ; assumption
axiom isKnave_notisKnight {A : Islander} : A.isKnave → ¬A.isKnight
axiom isKnight_notisKnaveIff {A : Islander} : A.isKnight ↔ ¬A.isKnave

axiom notisKnight_isKnave {A : Islander} : ¬A.isKnight → A.isKnave
axiom notisKnave_isKnight {A : Islander} : ¬A.isKnave → A.isKnight
axiom isKnave_notisKnightIff {A : Islander} : A.isKnave ↔ ¬A.isKnight

--------------
-- number affects where brackets will be needed

axiom knight_said {A : Islander} {P : Prop} : (A said P) → A.isKnight → P
axiom said_knight {A : Islander} {P : Prop} : (A said P) →  P → A.isKnight 
axiom knave_said {A : Islander} {P : Prop} : (A said P) →  A.isKnave → ¬P

axiom notknight_said {A : Islander} {P : Prop} : (A said P) → ¬A.isKnight → ¬P
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

-- *
macro "knight_to_knave" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff] at $t1)
-- goal
macro "knight_to_knave" : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff])
-- hypothesis
macro "knight_to_knave" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| simp [isKnight_notisKnaveIff] at $t1)

-- *
macro "knave_to_knight" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic => 
do`(tactic| simp [isKnave_notisKnightIff] at $t1)
macro "knave_to_knight" : tactic =>
do`(tactic| simp [isKnave_notisKnightIff])
-- hypothesis
macro "knave_to_knight" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| simp [isKnave_notisKnightIff] at $t1)

-- tell the user to use this instead of explaining stuff... this custom tactic hides not_isKnight_and_isKnave from the user and makes it so that the user doesn't need to interface with that directly.
--macro "contra_knight_knave" : tactic =>
--  `(tactic | (repeat (solve | apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption ) ))
--

--macro "contra_knight_knave" : tactic =>
--  `(tactic | ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ))

-- this creates a new macro contradiction, and extends the behavior of the contradiction tactic. but when seeing docstring, you don't get that its contradiction tactic
--macro "contradiction" : tactic =>
--  `(
--  tactic |
--  first |
--  ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ) | contradiction
--  )

#check solve
-- this truly extends contradiction tactic, preserving doc string
macro_rules
| `(tactic| contradiction) => 
  do `(tactic |first | ( apply not_isKnight_and_isKnave ; constructor ; assumption ; assumption   ) )

theorem knave_said2 {A : Islander} {P : Prop} : A said P → A.isKnave → ¬ P := by 
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
    · exact (not_isKnight_and_isKnave A ⟨hA, hA'⟩).elim
    · exact ⟨hA, hB⟩
  · have := knave_said hAB hA
    sorry

open Islander
theorem dsl_iamknave (hAKn : A said A.isKnave): False := by 
  knight_or_knave A with hA hnA 
  · have hnA := knight_said hAKn hA
    --#check not_isKnight_and_isKnave
    apply @not_isKnight_and_isKnave A
    constructor
    assumption ; assumption
  · have hnA := knave_said hAKn hnA
    contradiction
