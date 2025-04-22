import Game.Metadata

World "KnightsAndKnaves2"
Level 8

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
  Hint
    "
Use `have` to set `C` as the goal
    "
  have hC : C
  by_contra nC
  Hint
    "
Assuming `¬C` to prove `False` i.e `¬C → False` i.e `¬¬C` i.e `C`:

- Since `¬C` is true by `nC : ¬C`, then `A ↔ ¬C` and `A` have the same truth value. 

In other words, if `A` is true then `A ↔ ¬C` is true, and if `A` is false then `A ↔ ¬C` is false.

Use 
```
iff_true_right (ha : a) : (b ↔ a) ↔ b
``` 
to replace `A ↔ ¬C` with `A`.
(In our case, `b ↔ a` is `A ↔ ¬C`)

This reduction would transform `stB` from
```
¬B ↔ ¬(A ↔ ¬C)
```
to
```
¬B ↔ ¬A 
```
"
  rw [iff_true_right nC] at stB
  #check true_implies

  Hint
  "
- Rewrite `¬C` in `stA` with true using `eq_true`
- Rewrite `True → ¬B` in `stA` with `¬B` using `true_implies`
- Rewrite `¬B` in `stA` with `¬A` using `stBn`
- Prove `False` using `not_iff_self`
  "
  rw [eq_true nC] at stA
  rw [true_implies (¬B)] at stA
  rw [stB] at stA 
  #check not_iff_self
  exact not_iff_self stA.symm

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
This is it for this approach of knights and knaves.

If you want more, you can try the other approaches.
"
NewTheorem iff_true_right true_implies eq_true not_iff_self not_true false_implies iff_true_iff
