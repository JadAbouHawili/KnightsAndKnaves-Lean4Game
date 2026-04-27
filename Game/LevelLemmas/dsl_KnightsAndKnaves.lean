import Game.MathlibTheorems
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.ApplyFun

-- hide all this from the user

set_option push_neg.use_distrib true

axiom Islander : Type

namespace Islander

axiom A : Islander
axiom B : Islander
axiom C : Islander

axiom Robert : Islander
axiom Ira : Islander

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

macro "knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat : tactic => do`(tactic| obtain ($t2 | $t3) := isKnight_or_isKnave $t1)

macro "knight_or_knave" t1:term : tactic => do`(tactic| cases isKnight_or_isKnave $t1)


macro "knave_interp" : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] ); simp only[isKnight_notisKnaveIff ,not_not])
)

macro "knave_interp" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] at $t1 ); simp only[isKnight_notisKnaveIff ,not_not] at $t1)
)

macro "knave_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] at $t1 ); simp only[isKnight_notisKnaveIff ,not_not] at $t1)
)



macro "knight_interp" : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] ); simp only[isKnave_notisKnightIff,not_not])
)

macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] at $t1 ); simp only[isKnave_notisKnightIff,not_not] at $t1)
)

macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] at $t1 ); simp only[isKnave_notisKnightIff,not_not] at $t1)
)


macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve | (exfalso ; apply not_isKnight_and_isKnave  ; assumption ; assumption   ) )

end tactics

theorem dsl_iamknave {A : Islander} (hAKn : A said A.isKnave): False := by
  knight_or_knave A with hA hnA
  · have hnA := knight_said hAKn hA
    contradiction
  · have hnA := knave_said hAKn hnA
    contradiction

--variable {A B C : Islander}
def allKnights {A B C : Islander}:= A.isKnight ∧ B.isKnight ∧ C.isKnight
def allKnaves {A B C : Islander} := A.isKnave ∧ B.isKnave ∧ C.isKnave
def oneisknight {A B C : Islander} := (A.isKnight ∧ B.isKnave ∧ C.isKnave)  ∨(A.isKnave ∧  B.isKnight ∧ C.isKnave) ∨ (A.isKnave ∧ B.isKnave ∧  C.isKnight)
def exactlyOneIsKnave {A B C : Islander} : Prop := (A.isKnave and B.isKnight and C.isKnight) ∨ (A.isKnight and B.isKnave and C.isKnight) ∨ (A.isKnight and B.isKnight and C.isKnave)
end Islander
