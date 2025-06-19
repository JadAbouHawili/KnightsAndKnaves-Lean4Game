import Game.Metadata

World "KnightsAndKnaves2"
Level 5

Title ""

/-
wolfram generated
A ⇔ (C ∨ B)
B ⇔ (A ⇔ C)
-/
Introduction
"
`A`: `C` is a knight or `B` is a knight.

`B`: `A` is a knight, if and only if `C` is a knight.
"

#check iff_true_right
#check iff_true_intro
Statement {A B C : Prop}
{stA : A ↔ (C ∨ B)}
{stAn : ¬A ↔ (¬C ∧ ¬B)}
{stB : B ↔ (A ↔ C)}
{stBn : ¬B ↔ ¬(A ↔ C)}
: A ∧ B ∧ C := by
  Hint (strict := true)
    "
Use `have` to set `A` as the new goal.

We want to prove `A`, to do this we will prove `¬¬A` (which is equivalent to `A`) i.e `¬A → False`. The tactic `by_contra` facilitates this.

`by_contra h` assumes `h : ¬A` and changes the goal to `False`.

This is called a proof by contradiction because we are assuming the negation of what we want to prove and getting a contradiction.

Assuming `nA : ¬A`,
- Prove `nCnB : ¬C ∧ ¬B` from `stAn`
- Prove `AdiffC : ¬(A ↔ C)` from `stBn`, `nCnB.right : ¬B`
- Prove `AiffC : A ↔ C` from `iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b `, `nA:¬A`, `nCnB.left : ¬C`
- Prove `False` from `AdiffC : ¬(A ↔ C)`  `AiffC : (A ↔ C)`
    "
  have hA: A
  by_contra nA
  have nCnB := by exact stAn.mp nA
  have AdiffC := stBn.mp nCnB.right
  have AiffC := iff_of_false nA nCnB.left
  contradiction

  Hint (strict := true)
    "
Prove `CorB : C ∨ B` using `stA`, `{hA}`.
    "
  have CorB := stA.mp hA

  Hint
  "
Now consider cases for `CorB` and for every case prove the goal.

(proof by cases)
  "
  cases CorB
  Hint
  "
  Prove `AiffC : A ↔ C` using `iff_of_true (ha : a) (hb : b) : a ↔ b`, `hA : A`, `h : C`

  `iff_of_true` says that we can conclude `P ↔ Q` is true when `P` is true, `Q` is true (check the truth table).
  "
  have AiffC := iff_of_true hA h
  Hint
  "
  Prove `hB : B` using `stB`, `{AiffC}`.
  "
  have hB :=  stB.mpr AiffC
  Hint
  "
  Prove the goal using `{hA}`, `{hB}` ,`h`.

  Use `constructor` tactic to split the goal in two, the first being `A` and the second being `B ∧ C` or use ⟨⟩ notation or us `And.intro` or use `have` to first construct a proof of `B ∧ C` then use `And.intro` etc...

The proof of the second case for `h : B` would require using `stB`.
  "
  constructor
  exact hA
  exact And.intro hB h

  Hint (strict := true)
      "
We are now in the case where `B` is true, `h : B`.

Prove `AiffC : A ↔ C` using `stB`, `h`.
      "
  have AiffC := stB.mp h

  Hint (strict := true)
      "
Prove `C` using `{AiffC}`, `{hA}`
      "
  have hC := AiffC.mp hA
  constructor
  exact hA
  exact And.intro h hC

Conclusion
"
"
