import Game.LevelLemmas.settheory_KnightsAndKnaves3

World "SetTheory_Knights_Knaves"
Level 13

Title ""

open Inhabitant'

Introduction
"
Suppose the stranger, instead of asking A what he is, asked A, 'How many knights are among you?' Again A answers indistinctly.

So the stranger asks B, 'What did A say? B replies, 'A said that there is one knight among us.'

Then C says, \"Don't believe B; he is lying!\"

Now what are B and C?
"

Statement
(stB : (B ∈ Knight) ↔ (A ∈ Knight ↔(Knight : Finset Inhabitant').card = 1))
(stC : ( C ∈ Knight ↔ B ∈ Knave) )
  : B ∈ Knave ∧ C ∈ Knight := by
  Hint
  "
  Notice that `B` and `C` are of opposite types which means one of them is a knight , there is at
  least one knight. This detail is important and will show up later in our reasoning

Take cases for `A`
  "
  knight_or_knave A with AKnight AKnave
  Hint
  "
`stB` simplifies to `B ∈ Knight ↔ Knight.card = 1`
  "
  simp [AKnight] at stB
  Hint
  "
`B` can't be a knight because if `B` where a knight then we can conclude there is one knight which
is a contradiction

Change the goal to proving `B ∈ Knave` , interpret as knight and assume `B ∈ Knight`
  "
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  Hint
  "
Conclude there is only one knight
  "
  have oneKnight := stB.mp BKnight
  rw [Finset.card_eq_one] at oneKnight
  Hint
  "
  You don't have to go through the reasoning again here , just do `grind`
  "
  grind
  Hint
  "
  Now that we know `B ∈ Knave` , we can conclude `C ∈ Knight` and close the goal
  "
  have CKnight := stC.mpr BKnave
  constructor ; assumption ; assumption

  Hint
  "
  Now we are in the case where `A ∈ Knave` , interpret as knights and simplify `stB`
  "
  knight_interp at AKnave
  simp [AKnave] at stB

  Hint
  "
  If `B ∈ Knight` , then `C ∈ Knave`. `stB` gives us `¬Knight.card = 1` but that is the case
  (`Knight = \{B})

Change the goal to `B ∈ Knave` and assume `B ∈ Knight`
  "
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  Hint
  "
Conclude `¬Knight.card = 1` from `stB`
  "
  have notoneKnight := stB.mp BKnight
  Hint
  "
Interpret `stC` in terms of `B ∈ Knight` and conclude that `C ∉ Knight`
  "
  knight_interp at stC
  have CKnave := stC.mpr BKnight
  Hint
  "
Now we can prove `have : (Knight : Finset Inhabitant').card = 1`
  "
  have : (Knight : Finset Inhabitant').card = 1
  Hint
  "
Rewrite `Finset.card_eq_one`
  "
  rw [Finset.card_eq_one]
  Hint
  "
`Knight = \{B}` so `use B`
  "
  use B
  Hint
  "
`Finset.eq_singleton_iff_unique_mem`
  "
  rw [Finset.eq_singleton_iff_unique_mem]
  Hint
  "
Close the left side of `∧` and take all `all_possibilities x` to close the right side
  "
  constructor ; assumption
  intro x h
  all_possibilities x
  rw [isA] at h ; contradiction
  assumption
  rw [isC] at h ; contradiction
  contradiction
  Hint
  "
You have everything you need to close the goal
  "
  grind


/-
  have BKnave : B ∈ Knave
  knight_interp
  intro BKnight
  knight_interp at stC
  have CKnave := stC.mpr BKnight
  have stA := stB.mp BKnight
  have AKnave : A ∈ Knave
  knight_interp
  intro AKnight
  have KnightCard := stA.mp AKnight
  rw [Finset.card_eq_one] at KnightCard
  grind
  knight_interp at AKnave
  simp [AKnave] at stA
  have : (Knight : Finset Inhabitant').card = 1

  rw [Finset.card_eq_one]
  use B
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  assumption
  intro x h
  all_possibilities x
  rw [isA] at h ; contradiction
  assumption
  rw [isC] at h ; contradiction

  contradiction
  have CKnight := stC.mpr BKnave
  exact And.intro BKnave CKnight
-/


Conclusion
"
"
NewTactic grind
