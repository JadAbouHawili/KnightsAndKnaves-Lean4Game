import Game.Metadata


World "KnightsAndKnaves2" 
Level 1

Title "" 

Introduction 
"
A very special island is inhabited only by knights and knaves. Knights always tell the truth, and knaves always lie.

You meet two inhabitants: Zoey and Mel. Zoey tells you that Mel is a knave. Mel says, “Neither Zoey nor I are knaves.”

Can you determine who is a knight and who is a knave?

Note that `stZ` and `stZn` are saying the same thing, saying that `Zoey` and `¬Mel` have the same truth value i.e both are true or both are false is equivalent to saying that `¬Zoey` and `Mel` have the same truth value.

First change the goal to `Zoey` using the `have` tactic.
"

Statement 
{Zoey Mel : Prop}
(stZ : Zoey ↔ ¬Mel)
(stZn : ¬Zoey ↔ Mel)
(stM : Mel ↔ Mel ∧ Zoey)
  : Zoey ∧ ¬Mel := by
  {
  have hZ : Zoey
  Hint
  "
To prove `Zoey`, we will do a proof by contradiction.

We will assume `¬Zoey` and show a contradiction, proving that `¬Zoey → False` i.e `¬¬Zoey` which is equivalent to `Zoey`.

`by_contra hnZ` will assume `¬Zoey` adding,
```
hnZ : ¬Zoey
```
to the list of assumptions in the proof state.
  "
  by_contra nZ
  Hint
  "
Prove `Mel` using `¬Zoey`, `stZn`.
  "
  have hM := stZn.mp nZ
  Hint
  "
Prove `Mel and Zoey` using `Mel`, `stM`
  "
  have hMZ := stM.mp hM
  Hint
  "
We have `Zoey` and `¬Zoey`
  "
  exact nZ hMZ.right

  Hint
  "
Use constructor and close the first goal.
  "
  constructor
  assumption
  Hint
  "
Prove the second goal using `Zoey`, `stZ`
  "
  have nM := stZ.mp hZ
  assumption
  }

Conclusion
"
"
NewTactic by_contra
