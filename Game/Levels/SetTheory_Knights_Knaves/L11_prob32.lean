import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 11

Title ""

open Inhabitant'

Title "allKnaves, exactlyOneIsKnave"

Introduction
"
`A`: All of us are knaves.

`B`: Exactly one of us is a knave.

In this level , we take a different approach when formalizing the statements of `A` and `B` than the
corresponding `DSL` level
"

Statement
{stA : A ∈ Knight ↔ (Knave : Finset Inhabitant') = {A,B,C}}
{stB : B ∈ Knight ↔ (Knave : Finset Inhabitant').card = 1}
: A ∈ Knave ∧ C ∈ Knight := by
  Hint
  "
Let's start by proving `A ∈ Knave`
  "
  have AKnave: A ∈ Knave
  Hint
  "
Interpret the goal in terms of knights and assume `A ∈ Knight`
  "
  knight_interp
  intro AKnight
  Hint
  "
Conclude that everyone is a knave from `stA`
  "
  have allKnave := stA.mp AKnight
  Hint
  "
This is means that `A ∈ Knave` which is a contradiction. Change the goal to `A ∈ Knave`
  "
  have : A ∈ Knave
  Hint
  "
`rw [{allKnave}]`
  "
  rw [allKnave]
  Hint
  "
`simp` will do the job
  "
  simp
  Hint
  "
We now have a `contradiction`
  "
  contradiction

  Hint
  "
  Since we have proven that `A ∈ Knave` , let's intrepret `stA` in terms of knaves
  "
  knave_interp at stA
  Hint
  "
Conclude not everyone is a knave
  "
  have notallKnave := stA.mp AKnave
  Hint
  "
Let's close the first part of the goal using `constructor` and `{AKnave}`
  "
  constructor ; assumption
  Hint
  "
Let's think about each case of `B`

If `B` were a knight then by `stB` we know there is only one knave(which would be `A`) so `C ∈
Knight`. This we can use to close the goal directly

If `B` were a knave then if we were to assume that `C ∈ Knave` we can derive a contradiction because
everyone would be a knave contradicting `{notallKnave}`.

Take cases for `B`
  "
  Hint (hidden:=true)
  "
In both cases we can close the goal so do `knight_or_knave B with BKnight BKnave`
  "
  knight_or_knave B with BKnight BKnave
  Hint
  "
`B` is a knight then by `stB` we know there is only one knave
  "
  have oneKnave := stB.mp BKnight
  Hint
  "
`rw [Finset.card_eq_one] at {oneKnave}`
  "
  rw [Finset.card_eq_one] at oneKnave
  Hint
  "

  obtain ⟨a,ha⟩ :={oneKnave}
(which would be `A`) so `C ∈
Knight`. This we can use to close the goal directly
  "
  obtain ⟨a,ha⟩ :=oneKnave
  Hint
  "
Let's prove `C ∈ Knight`
  "
  have CKnight : C ∈ Knight
  Hint
  "
Interpret the goal as knaves and assume `CKnave`
  "
  knave_interp
  intro CKnave

  Hint
  "
`Knave = \{a}`.

`A ∈ Knave` so `A ∈ \{a}` so `A = a`(by simp)
`A ∈ Knave` so `C ∈ \{a}`(by `rw`) so `C = a`(by `simp`)

Therefore , `A = C` which is a contradiction
  "
  rw [ha] at CKnave
  simp at CKnave
  rw [ha] at AKnave
  simp at AKnave
  rw [←CKnave] at AKnave
  contradiction
  Hint
  "
Now we know that `C ∈ Knight` and can close the case where `B ∈ Knight`
  "
  assumption
  Hint
  "
Now in the case where `B ∈ Knave`

We want to prove `C ∈ Knight`, if we were to assume other i.e `C ∈ Knave` then we would want to
prove a contradiction.

We can do so because now everyone is a knave

As usual , assume `CKnave`
  "
  knave_interp
  intro CKnave
  Hint
  "
Use the following theorem to obtain a contradiction and close the goal
```
full3 (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) : S = \{A, B, C}
```
  "
  exact notallKnave (full3 AKnave BKnave CKnave)

Conclusion
"
"
NewTheorem full3 Finset.card_eq_one
