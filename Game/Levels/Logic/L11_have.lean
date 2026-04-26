import Game.MathlibTheorems

World "Logic"
Level 11

Title ""

Introduction
"
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

Statement {P Q R : Prop}
{hP : P}
{hPQ : P → Q}
{hQR : Q → R}
  : R := by
  exact hQR (hPQ hP)

Conclusion
"
You could have also not used `have` here by passing `hQR` a proof of `P` which is `hPQ hP`. Try it
before moving on.
"
