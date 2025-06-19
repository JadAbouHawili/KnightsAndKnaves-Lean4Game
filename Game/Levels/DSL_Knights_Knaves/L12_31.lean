import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves


World "DSL_Knights_Knaves"
Level 12

Title ""

Introduction
"
Again we have three people, `A`, `B`, `C`, each of whom is either a knight or a knave.

`A` and `B` make the following statements:

`A`: All of us are knaves.

`B`: Exactly one of us is a knight.

What are `A`, `B`, `C`?

Change the goal to `A.isKnave`
"

-- prob 31
open Islander
set_option push_neg.use_distrib true
Statement
{stA : A said @allKnaves A B C}
{stB : B said @oneisknight A B C}
: A.isKnave ∧ B.isKnight ∧ C.isKnave := by
  have AKnave : A.isKnave
  Hint (strict:=true)
  "
Change the goal from `knave_to_knight`
  "
  knave_to_knight
  Hint
  "
Assume `A.isKnight`
  "
  intro AKnight
  Hint
  "
Conclude `A`'s statement
  "
  have allknave := knight_said stA AKnight
  Hint
  "
Now we have that everybody is a knave, but we know `A` is a knight. Therefore, we have a contradiction.

`unfold allKnaves` and obtain a contradiction.
  "
  unfold allKnaves at allknave
  have AKnave := allknave.left
  contradiction

  Hint (strict:=true)
  "
Now that we know `A` is a knave, conclude the negation of `A`'s statement.
  "
  have notallknave := knave_said stA AKnave

  Hint (strict := true)
  "
Let's move on to proving `B.isKnight`
  "
  have BKnight : B.isKnight
  Hint (strict:=true)
  "
Convert from `knight_to_knave`.
  "
  knight_to_knave
  Hint (strict:=true)
  "
Assume `B.isKnave`.
  "
  intro BKnave
  Hint
  "
Conclude that `B`'s statement is false
  "
  have notoneknight := knave_said stB BKnave
  Hint
  "
  `{notoneknight}` means that there are no knights or there are two or more knights.

  Since we know that `A,B` are knaves then it is the former i.e. there are no knights. This means that `C` is a knave.

  To obtain this result:
  - First start by unfolding `{notoneknight}`.
  - Use `simp` given what you know to simplify the obtained expression after unfolding.
  - The final answer after simplification would be that `C` is a knave.

  After obtaining that `C` is a knave, we now know that everyone is a knave but we also know that `{notallknave} : ¬allKnaves` and so a contradiction.

  To obtain this contradiction, `unfold allKnaves at {notallknave}` then simplify the unfolded expression or construct a proof of `A.isKnave and B.isKnave and C.isKnave`.
  "
  unfold oneisknight at notoneknight
  knight_to_knave at notoneknight
  -- , isKnave_notisKnightIff.mp BKnave, isKnave_notisKnightIff.mp AKnave
  simp [AKnave, BKnave ] at notoneknight
  unfold allKnaves at notallknave
  simp [AKnave, BKnave, notoneknight] at notallknave

  Hint
  "
Now, we know that `A` is a knave and `B` is a knight.

Conclude `B`'s statement.
  "
  have one := knight_said stB BKnight
  Hint
  "
We now have that not everyone is a knave and that there is only one knight. Since we know that knight is `B`, then `C` can't be a knight and must be a knave.

Use `simp`,`{one}`,`{AKnave}`,`{BKnight}` to prove that `C` is a knave.

After which, you can close the goal.
  "
  unfold oneisknight at one
  simp [AKnave,BKnight] at one
  knave_to_knight at one
  simp [AKnave,BKnight] at one
  knight_to_knave at one
  simp [AKnave,BKnight,one]

Conclusion
"
"
