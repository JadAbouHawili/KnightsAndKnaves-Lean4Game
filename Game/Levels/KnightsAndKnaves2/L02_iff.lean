import Game.Metadata

World "KnightsAndKnaves2"
Level 2

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
/-
Everytime you need to assume, and for every bullet point, you would need to use the `have` tactic.

Notice that `¬A` means `¬C, ¬B` where ¬B gives that A and C dont have the same type. This is a contradiction of course so the proposition ¬A is not true which means that A is true.  

Now we know A, which gives C ∨ B
¬B means C, and it also means ¬(A ↔ C). But we know A ↔ C from A,C so we get a contradiction.

lets take cases for C ∨ B. Having C gives us (A ↔ C) which gives us B. So we get as a final answer, A ∧ B ∧ C. 
Having B, we get that (A ↔ C) which gives us C. The final answer is A ∧ B ∧ C.

Now we know A,B. From B we get that A ↔ C, which means C.

Now we know A,B,C.
-/

    #check iff_true_right
    #check iff_true_intro
    #check iff_of_true
Statement {A B C : Prop}
{stA : A ↔ (C ∨ B)}
{stAn : ¬A ↔ (¬C ∧ ¬B)}
{stB : B ↔ (A ↔ C)}
{stBn : ¬B ↔ ¬(A ↔ C)}
: A ∧ B ∧ C := by
  Hint 
    "
We want to prove `A`, to do this we will prove `¬¬A` i.e `¬A → False`. The tactic `by_contra` facilitates this, assuming `¬A` and changing the goal to `False`.

Assuming `nA : ¬A`,
- Prove `nCnB : ¬C ∧ ¬B` from `stAn`
- Prove `AdiffC : ¬(A ↔ C)` from `stBn` , `nCnB.right : ¬B`
- Prove `AiffC : A ↔ C` from `iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b `, `nA:¬A` , `nCnB.left : ¬C`
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
Prove `CorB : C ∨ B` using `stA` , `{hA}`.
    "
  have CorB := stA.mp hA

  Hint
  "
Now consider cases for `CorB`.
  "
  cases CorB
  Hint
  "
  Prove `AiffC : A ↔ C` using `iff_of_true (ha : a) (hb : b) : a ↔ b` , `hA : A` , `h : C`
  "
  have AiffC := iff_of_true hA h
  Hint 
  "
  Prove `hB : B` using `stB` , `{AiffC}`.
  "
  have hB :=  stB.mpr AiffC
  Hint
  "
  Prove the goal using `{hA}`, `{hB}` ,`h`.

  Use `constructor` tactic to split the goal in two, one would be proving the left side of `∧` and the other being the right side.

The proof of the second case for `h : B` is similar.
  "
  constructor
  exact hA
  exact And.intro hB h

--  Hint
--      "
--Prove `AiffC : A ↔ C` using `stB` , `h`.
--      "
  have AiffC := stB.mp h

--  Hint
--      "
--Prove `C` using `{AiffC}` , `{hA}`
--      "
  have hC := AiffC.mp hA
--  Hint
--    "
--    Similarly use `constructor`
--    "
  constructor
  exact hA
  exact And.intro h hC

Conclusion
"
"
NewTactic by_contra
NewTheorem iff_of_false iff_of_true
