import Game.MathlibTheorems

World "Logic"
Level 11

Title "`have`"

Introduction
"
In this level, we introduce the `have` tactic.

You have to prove `R` using `hQR` but to do that, you need `Q` first.

Type `have hQ : Q` to change the goal to proving `Q`. And when the proof is done, `hQ : Q` is
added to the proof state and can be used.
"

Statement {P Q R : Prop}
{hP : P}
{hPQ : P → Q}
{hQR : Q → R}
  : R := by
  {
  have hQ : Q
  Hint
  "
  `hPQ` takes `hP` and gives you a proof of `Q`
  "
  exact hPQ hP

  Hint
  "
Now that you proved `Q`, its proof `{hQ} : Q` has been added to the proof state.

`hQR` takes `{hQ}` and gives you a proof of `R` which is the goal.
  "
  exact hQR hQ
  }

Conclusion
"
Redo the level with the following approach.

Coming back to `have`,

If you can prove something in one step, then
```
have theorem-name := proof
```
will do.

For example, you can obtain a proof of `Q` in one step by
```
hPQ hP
```
then `have hQ := hPQ hP` will add `hQ : Q` to the proof state, i.e. you have proven `Q` and `hQ` is the proof.

Then `hQR hQ` would be a proof of `R` that closes the goal


"

NewTactic «have»
