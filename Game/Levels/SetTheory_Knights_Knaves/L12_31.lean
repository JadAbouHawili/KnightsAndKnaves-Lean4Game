import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 12

Title "Everyone is a knave"

open Inhabitant'

Introduction
"
`A` : All of us are Knaves

`B` : Exactly one of us is a knight
"

Statement
{stA : A ∈ Knight ↔ Knave = {A,B,C}}
{stB : B ∈ Knight ↔ (Knight : Finset Inhabitant').card = 1  }
: A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave := by
  Hint
  "
Change the goal to `A ∈ Knave`
  "
  have AKnave : A ∈ Knave
  Hint
  "
Interpret the goal in terms of knights
  "
  knight_interp
  Hint
  "
Assume `AKnight`
  "
  intro AKnight
  Hint
  "
Conclude that everyone is a knave from `stA`
  "
  have allknave := stA.mp AKnight
  Hint
  "
  Since everyone is a knave , then `A` is a knave. Change the goal to `A ∈ Knave`
  "
  have AKnave : A ∈ Knave
  Hint
  "
rewrite `Knave` in the goal with `\{A,B,C}`
  "
  rw [allknave]
  simp
  Hint
  "
  Now that we know `A ∈ Knight` and `A ∈ Knave` we have a `contradiction`
  "
  contradiction

  Hint
  "
  Now that we know `A ∈ Knave` , let's interpret `stA` in terms of knaves
  "
  Hint (hidden := true)
  "
`knave_interp at stA`
  "
  knave_interp at stA
  Hint (strict:=true)
  "
Conclude from `stA` that not everyone is a knave
  "
  have := stA.mp AKnave
  Hint (strict:=true)
  "
Let's move on to prove `B ∈ Knight`
  "
  have BKnight : B ∈ Knight
  Hint
  "
  As usual, interpret in terms of knaves and assume `B ∈ Knave`
  "
  knave_interp
  intro BKnave
  Hint
  "
  Since `A ∈ Knave` , `B ∈ Knave` then we know `C ∈ Knight` because not everyone is a knave.
  Moreover, we know `Knight.card = 1`.

  Change the goal using `have oneKnight : (Knight : Finset Inhabitant').card = 1`
  "
  have oneKnight : (Knight: Finset Inhabitant').card = 1
  Hint
  "
  What it means to have cardinality equal one is given by `Finset.card_eq_one`

`Finset.card_eq_one : s.card = 1 ↔ ∃ a, s = \{a}`

`rw [Finset.card_eq_one]`
  "
  rw [Finset.card_eq_one]
  Hint
  "
We know this element has to be `C` so `use C`
  "
  use C
  Hint
  "
  What it means for a set to be equal to a singleton is given by
  `Finset.eq_singleton_iff_unique_mem`

  `rw [Finset.eq_singleton_iff_unique_mem]`
  "
  rw [Finset.eq_singleton_iff_unique_mem]
  Hint (strict:=true)
  "
We know `C ∈ Knight` because other everyone would be a knave.

Change the goal to `C ∈ Knight` and as usual interpret as knaves and assume `C ∈ Knave`
  "
  have CKnight : C ∈ Knight
  knave_interp
  intro CKnave
  Hint
  "
  Let's prove the contradiction , we know that `¬Knave=\{A,B,C}` but we can prove that
  `Knave=\{A,B,C}` so change the goal to proving `Knave = \{A,B,C}`
  "
  have : Knave = {A,B,C}
  Hint
  "
Close the goal using `full3`

`full3 (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) : Knave = \{A, B, C}`
  "
  exact full3 AKnave BKnave CKnave
  Hint
  "
  We know `¬Knave=\{A,B,C}` and `Knave=\{A,B,C}`
  "
  contradiction
  Hint
  "
Close the first part of `and` using `constructor`
  "
  constructor
  assumption
  Hint
  "
  The goal now states: for every arbitrary inhabitant that is a knight , this inhabitant is equal to
  `C`

  `intro x h` to take an arbitrary inhabitant `x` and assume `h : x ∈ Knight`
  "
  intro x h
  Hint(strict:=true)
  "
  `all_possibilities x` takes cases for what `x` might be
  "
  all_possibilities x
  Hint
  "
  If `x` where `A` , then `A ∈ Knight` and `A ∈ Knave`
  "
  rw [isA] at h ; contradiction
  Hint
  "
  If `x` where `B` , then `B ∈ Knight` and `B ∈ Knave`
  "
  rw [isB] at h ; contradiction
  assumption
  Hint
  "
  Now that we know there is only one knight , conclude that `B ∈ Knight` from `stB`
  "
  have BKnight := stB.mpr oneKnight
  Hint
  "
This contradicts our initial assumption that `B ∈ Knave`
  "
  contradiction
  Hint
  "
We now know that `B ∈ Knight` so there is only one knight.
  "
  have oneKnight := stB.mp BKnight
  Hint
  "
`Finset.card_eq_one : s.card = 1 ↔ ∃ a, s = \{a}`

Remember that you can think of `↔` as `=`
  "
  rw [Finset.card_eq_one] at oneKnight
  Hint
  "
We know that there exists some `a` such that `Knight = \{a}`

We can extract these two facts using `obtain ⟨a,ha⟩ := {oneKnight}`
  "
  obtain ⟨a,ha⟩ := oneKnight

  Hint
  "
  We know that there is only one knight and that knight is `B` ,  this element `a` is `B` (`B = a`) so `C` must be a knave.

  Change the goal to proving `C ∈ Knave` , interpret as knight and assume `C ∈ Knight`
  "
  have CKnave: C ∈ Knave
  knight_interp
  intro knight
  Hint
  "
  `C ∈ Knight` but `Knight =\{a}` and so `C = a` but we also know that `B = a` which means `B = C` , a
  contradiction.

Rewriting `Knight = \{a}` at `C ∈ Knight` and simplifying will yield `C = a`. You can similarly show
`B = a` then prove `B = C`(a contradiction)

  "

  rw [ha] at BKnight
  simp at BKnight

  rw [ha] at knight
  simp at knight
  rw [←knight] at BKnight
  contradiction
  Hint
  "
  We have proven that `A ∈ Knave` , `B ∈ Knight` , `C ∈ Knave` so you can close the goal (many
  options like
  `And.intro` , `constructor` , `simp`)
  "
  simp [AKnave,BKnight,CKnave]


Conclusion
"
"

NewTheorem Finset.eq_singleton_iff_unique_mem
NewTactic all_possibilities use
