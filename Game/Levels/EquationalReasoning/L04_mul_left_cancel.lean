import Game.Metadata

World "EquationalReasoning"
Level 4

Title "`Nat.mul_left_cancel`, Divide both sides of an equation"

Introduction
"
We know that `4 * y = 16`. Dividing both sides by `4` gives us `y = 4` which is the goal.

The theorem to do this is:
```
Nat.mul_left_cancel firstarg
                    secondarg
```
where `firstarg` is a theorem that the number you are cancelling from both sides is positive, in our case this would be `four_pos`.

`secondarg` would be the equation you are working with, in this case `h`.

`Nat.mul_left_cancel firstarg secondarg` would be a proof of the resulting equation after cancelling the positive number specified in `firstarg` from both sides of the equation specified in `secondarg`.

Give this proof to Lean using `exact`.
"

Statement (h : 4*y=16) : y = 4 := by{
  exact Nat.mul_left_cancel four_pos h
}

Conclusion
"
Here is the type signature of `Nat.mul_left_cancel`:
  ```
Nat.mul_left_cancel
(np : 0 < n)
(h : n * m = n * k)
: m = k
  ```
  `Nat.mul_left_cancel` takes two arguments which are:
   - `np`, a proof that some number `n` is positive.
   - `h`, the equation which has `n` on both sides of the equation multiplied on the left.

  The result is whats after `:`, canceling `n` from both sides of the equation giving a proof `m = k`.
"

NewTheorem Nat.mul_left_cancel four_pos
NewDefinition UnicodeSymbols
