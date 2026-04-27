import Game.LevelLemmas.settheory

universe u

class World' (Inhabitant : Type u) [DecidableEq Inhabitant] where
  -- tells the truth
  Knight : Finset Inhabitant
  -- always lies
  Knave : Finset Inhabitant
  dis : Knight ∩ Knave = ∅
  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave

variable {Inhabitant : Type}
[DecidableEq Inhabitant]

namespace hidden
axiom  Knight : Finset Inhabitant
axiom  Knave : Finset Inhabitant
axiom  dis : (Knight : Finset Inhabitant) ∩ Knave = ∅
axiom  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave
end hidden

noncomputable instance W : World' Inhabitant where
  Knight := hidden.Knight
  Knave := hidden.Knave
  dis := hidden.dis
  KorKn := hidden.KorKn

--[W: World Inhabitant]
--local notation "Knight" => W.Knight
--local notation "Knave" => W.Knave
--local notation "KorKn" => W.KorKn
--local notation "dis" => W.dis

noncomputable def Knight : Finset Inhabitant := W.Knight
noncomputable def Knave : Finset Inhabitant := W.Knave
noncomputable def  dis : Knight ∩ (Knave : Finset Inhabitant) = ∅ := W.dis
noncomputable def  KorKn : ∀ x : Inhabitant, x ∈ Knight ∨ x ∈ Knave := W.KorKn

#check Finset.instUnion
instance : OrOp Prop  :=
  ⟨fun a b ↦ Or a b⟩
#check xor_def

example : (Xor' (2=2) (2=2)) ↔ (2=2 ↔ 2≠2) := by
  exact xor_iff_iff_not
-- open World is no good

theorem disjoint
{A : Inhabitant}
(AKnight : A ∈ Knight)
(AKnave : A ∈ Knave)  : False := by
  exact disjoint_finset dis AKnight AKnave

-- needs to be repeated in every file...
/-
modifies the behavior of contradiction
-/
macro_rules
| `(tactic| contradiction) =>
  do `(tactic |solve  | ( exfalso ; apply @disjoint Inhabitant  ; repeat assumption) )

-- A : I am knave
theorem IamKnave
{A : Inhabitant}
-- representation of the statement that A made
(stA : A ∈ Knight  ↔ (A ∈ Knave) )
  : False := by

  {
    rcases KorKn A with AKnight|AKnave
    -- A ∈ Knight
    · have := stA.mp AKnight
      /-

AKnight : A ∈ Knight
this : A ∈ Knave
      -/
      contradiction

    · have := stA.mpr AKnave
      contradiction
  }

theorem IamKnaveIffFalse
{A : Inhabitant}
: (A ∈ Knight  ↔ (A ∈ Knave)) ↔ False
   := by
    constructor
    exact IamKnave
    exact fun a => a.elim

theorem knight_notknave
{A : Inhabitant}
(h' : A ∈ Knight) : A ∉ Knave := by
  exact inleft_notinright_finset dis h'

theorem notknight_knave
{A : Inhabitant}
(h' : A ∉ Knight) : A ∈ Knave := by
  exact notleft_right (KorKn A) h'

theorem knave_notknight
{A : Inhabitant}
(h' : A ∈ Knave) : A ∉ Knight := by
  exact inright_notinleft_finset dis h'

theorem notknave_knight
{A : Inhabitant}
(h' : A ∉ Knave) : A ∈ Knight := by
  exact notright_left (KorKn A) h'


-------------------
theorem knight_notknaveIff
{A : Inhabitant}
: A ∈ Knight ↔  ¬(A ∈ Knave) := by
  constructor
  · exact knight_notknave
  · exact notknave_knight

theorem notknight_knaveIff
{A : Inhabitant}
: A ∉ Knight ↔  A ∈ Knave := by
  constructor
  · exact notknight_knave
  · exact knave_notknight

theorem knave_notknightIff
  {A : Inhabitant}
: A ∈ Knave ↔  A ∉ Knight := by
  constructor
  · apply @knave_notknight Inhabitant
  · exact notknight_knave

theorem notknave_knightIff
  {A : Inhabitant}
 : A ∉ Knave ↔  A ∈ Knight := by
  constructor
  · exact notknave_knight
  · exact knight_notknave


-- hypothesis
/--
Interpret statements in terms of knaves
-/
macro "knave_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| ( (try rw [not_iff_not.symm] at $t1) ; simp only[knight_notknaveIff,not_not] at $t1)
)
/--
Interpret statements in terms of knaves
-/
-- goal , usually goal doesn't have Iff
macro "knave_interp" : tactic =>
do`(tactic| ((try rw [not_iff_not.symm]) ; simp only[knight_notknaveIff,not_not] )
)
/--
Interpret statements in terms of knaves
-/
-- *
macro "knave_interp" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| ( (try rw [not_iff_not.symm] at $t1) ; simp only[knight_notknaveIff,not_not] at $t1)
)


#check knave_notknightIff
-- hypothesis
/--
Interpret statements in terms of knights
-/
macro "knight_interp" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic| ((try rw [not_iff_not.symm] at $t1 ); simp only[knave_notknightIff,not_not] at $t1)
)
-- goal , usually goal doesn't have Iff
/--
Interpret statements in terms of knights
-/
macro "knight_interp" : tactic =>
do`(tactic| ((try rw [not_iff_not.symm]) ; simp only[knave_notknightIff,not_not] )
)
-- *
/--
Interpret statements in terms of knights
-/
macro "knight_interp" "at"  t1:Lean.Parser.Tactic.locationWildcard : tactic =>
do`(tactic| ( (try rw [not_iff_not.symm] at $t1) ; simp only[knave_notknightIff,not_not] at $t1))


macro "knight_or_knave" t1:term  : tactic =>
do`(tactic| cases (KorKn $t1)  )

macro "knight_or_knave" t1:term "with" t2:rcasesPat t3:rcasesPat  : tactic =>
do`(tactic| obtain $t2|$t3 := (KorKn $t1)  )

example {A : Inhabitant} (h : A ∈ Knight) : A ∉ Knave := by
  #check knight_notknaveIff
  knight_interp
  assumption


--#check Finset.subset_insert_iff_of_not_mem
--hypothesis
macro "remove_top" "at" t1:Lean.Parser.Tactic.locationHyp : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_notMem] at $t1 <;> try assumption)
--goal
macro "remove_top" : tactic =>
do`(tactic |  rw[ Finset.subset_insert_iff_of_notMem] <;> try assumption)
