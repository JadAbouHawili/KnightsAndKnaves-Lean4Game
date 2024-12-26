import Game.Metadata

World "KnightsAndKnaves2"
Level 5

Title ""

Introduction
"
`A`: If `C` is a knave, then `B` is a knave.
`B`: `A` is a knight, if and only if `C` is a knave.
"
/-
A ⇔ (¬C  ¬B)
B ⇔ (A ⇔ ¬C)
-/

#check imp_true_iff
#check true_implies
Statement {A B C : Prop}
{stA : A ↔ (¬C → ¬B)}
{stAn : ¬A ↔ ¬(¬C → ¬B)}
{stB : B ↔ (A ↔ ¬C)}
{stBn : ¬B ↔ ¬(A ↔ ¬C)}
: A ∧ ¬B ∧ C := by
  Template
  have hC : C := by
    by_contra nC
    Hint
    "
Assuming `¬C` to prove `False` i.e `¬C → False` i.e `¬¬C` i.e `C`:

- Since `¬C` is true by `nC : ¬C`, then `A ↔ ¬C` and `A` have the same truth value. If `A` is true then `A ↔ ¬C` is true, and if `A` is false then `A ↔ ¬C` is false.
Use `iff_true_right (ha : a) : (b ↔ a) ↔ b` to replace `A ↔ ¬C` with `A`.
In our case, `b ↔ a` is `A ↔ ¬C`.

- Rewrite `¬C` in `stA` with true using `eq_true`
- Rewrite `True → ¬B` in `stA` with `¬B` using `true_implies`
- Rewrite `¬B` in `stA` with `¬A` using `stBn`
- Prove `False` using `not_iff_self`
    "
    Hole
    rw [iff_true_right nC] at stBn
    #check true_implies
    rw [eq_true nC] at stA
    rw [true_implies (¬B)] at stA
    rw [stBn] at stA 
    #check not_iff_self
    exact not_iff_self stA.symm

    --simp only [nC,not_false_eq_true,true_implies] at stA 
    ----nth_rw 1 [stA] at stB
    --simp [nC] at stB
    --rw [stB] at stA
    --#check iff_not_self
    --apply iff_not_self
    --exact stA

  Hole
  Hint 
  "
Rewrite `¬C` in `stA` as `¬True` using `eq_true`
  "
  rw [eq_true hC] at stA 
  #check not_true
  Hint
  "
Rewrite `¬True` in `stA` as `False` using `not_true`
  "
  rw [not_true] at stA
  Hint
  "
Rewrite `False → ¬B` in `stA` as `¬B` using `false_implies`
  "
  rw [false_implies] at stA
  #check iff_true_iff
  Hint
  "
Rewrite `stA` using `iff_true_iff`.
  "
  rw [iff_true_iff] at stA

  -- similarly here, let user use simp
  Hint
  "
- Use simp and `hC : C` to simplify `stB`
- Rewrite `stB` using `iff_not_comm` obtaining `stB : A ↔ ¬B`
- Prove `¬B` using and conclude the goal
  "
  simp [hC] at stB
  rw [iff_not_comm] at stB 
  have nB := stB.mp stA
  exact ⟨stA,nB,hC⟩ 

Conclusion
"
"
NewTheorem iff_true_right true_implies eq_true not_iff_self not_true false_implies iff_true_iff

