import Game.Metadata
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.ApplyFun

-- hide all this from the user

set_option push_neg.use_distrib true

axiom Islander : Type

namespace Islander

axiom isKnight : Islander → Prop

axiom isKnave : Islander → Prop

axiom isKnight_or_isKnave (A : Islander) : A.isKnight ∨ A.isKnave

axiom not_isKnight_and_isKnave {A : Islander} (AKnight : A.isKnight) (AKnave : A.isKnave) : False

axiom Said : Islander → Prop → Prop
notation A " said " P:200 => Said A P

/-
the following 4 axioms can be proven from the previous ones...
-/
theorem isKnight_notisKnave {A : Islander} : A.isKnight → ¬A.isKnave := by
  intro AKnight
  intro AKnave
  apply not_isKnight_and_isKnave
  assumption ; assumption
axiom isKnave_notisKnight {A : Islander} : A.isKnave → ¬A.isKnight
axiom isKnight_notisKnaveIff {A : Islander} : A.isKnight ↔ ¬A.isKnave

axiom notisKnight_isKnave {A : Islander} : ¬A.isKnight → A.isKnave
axiom notisKnave_isKnight {A : Islander} : ¬A.isKnave → A.isKnight
axiom isKnave_notisKnightIff {A : Islander} : A.isKnave ↔ ¬A.isKnight

axiom knight_said {A : Islander} {P : Prop}
  (stA : A said P) (AKnight : A.isKnight) :  P
axiom said_knight {A : Islander} {P : Prop}
(stA : A said P) (hP : P) : A.isKnight
axiom knave_said {A : Islander} {P : Prop}
(stA : A said P) (AKnave : A.isKnave) :  ¬P
theorem said_knave {A : Islander} {P : Prop} (AsaidP : A said P) (nP : ¬P) : A.isKnave := by
  apply notisKnight_isKnave
  intro AKnight
  have hP := knight_said AsaidP AKnight
  contradiction
axiom notknight_said {A : Islander} {P : Prop} : (A said P) → ¬A.isKnight → ¬P

section tactics
-- make custom tactics for finset.card stuff...

macro "knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat : tactic => do`(tactic| obtain ($t2 | $t3) := isKnight_or_isKnave $t1)

macro "knight_or_knave" t1:term : tactic => do`(tactic| cases isKnight_or_isKnave $t1)

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

#check solve
macro_rules
| `(tactic| contradiction) =>
  do `(tactic |first | ( apply not_isKnight_and_isKnave ; assumption ; assumption   ) )

end tactics

theorem dsl_iamknave (hAKn : A said A.isKnave): False := by
  knight_or_knave A with hA hnA
  · have hnA := knight_said hAKn hA
    apply not_isKnight_and_isKnave
    assumption ; assumption
  · have hnA := knave_said hAKn hnA
    contradiction


--variable {A B C : Islander}
def allKnights {A B C : Islander}:= A.isKnight ∧ B.isKnight ∧ C.isKnight
def allKnaves {A B C : Islander} := A.isKnave ∧ B.isKnave ∧ C.isKnave
def oneisknight {A B C : Islander} := (A.isKnight ∧ B.isKnave ∧ C.isKnave)  ∨(A.isKnave ∧  B.isKnight ∧ C.isKnave) ∨ (A.isKnave ∧ B.isKnave ∧  C.isKnight)
def exactlyOneIsKnave {A B C : Islander} : Prop := (A.isKnave and B.isKnight and C.isKnight) ∨ (A.isKnight and B.isKnave and C.isKnight) ∨ (A.isKnight and B.isKnight and C.isKnave)
end Islander
