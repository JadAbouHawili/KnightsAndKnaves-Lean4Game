import Game.Metadata

World "EquationalReasoning"
Level 4

Title "`Nat.mul_left_cancel` , Divide both sides of an equation"

Introduction
"
We know that `4 * y = 16`. Dividing both sides by `4` gives us `y = 4` which is the goal.

The theorem to do this is:
```
Nat.mul_left_cancel firstarg 
                    secondarg
```
where the `firstarg` is a theorem that the number you are cancelling from both sides is positive, in our case this would be `four_pos`. 

The `secondarg` would be the equation you are working with, in this case `h`.

`Nat.mul_left_cancel firstarg secondarg` would be a proof of the resulting equation after cancelling the positive number specified in `firstarg` from both sides of the equation specified in `secondarg`.

Give this proof to Lean using `exact`.
"

Statement (h : 4*y=16) : y = 4 := by{
  exact Nat.mul_left_cancel four_pos h
}

/-
--------------
We will add the theorem `16=4*4` to the proof state, and use it to prove the goal.

Heres an example:
`have twoEqualstwo : 2=2 := by rfl` will add an object named `twoEqualstwo` of type `2=2` to the proof state which would look as follows:
```
Assumptions:
twoEqualstwo : 2=2
```

You can choose any name after `have` and any type after `:`.

For this problem, we want `16=4*4` instead of `2=2`.
Adapt this example to `16 = 4*4` and include after `by` its proof.
-/

example (h : 4*y=16) : y = 4 := by{
  Hint (hidden := true) 
  "
  For the proof, we need to carry out the calculation of `4 * 4` and as in the previous level, the tactic for that is `norm_num`. Typing that as the proof will work. 
  "

  -- Notice that if `16` were in the goal, you would do `rw [{helper}]` to replace `16` with with `4*4`. We want to do the same thing at `h`. So, `rw ... at h` will do it. 

  have helper : 16=4*4 := by norm_num 
  Hint "Now, using `rw`, we want to replace the `16` in `h` with `4 * 4`. "
  -- In other words, we want to do `rw [{helper}]` and have it be applied on h. 
  Hint (hidden := true) "`rw [{helper}] at h`" 
  rw [helper] at h 
  Hint "
 Using `Nat.mul_left_cancel`, cancel the `4` on both sides of `h` obtaining `y=4` which is the goal.

  For example, given the following proof state:
  ```
  equation : 2*x = 2*3
  ```
  `Nat.mul_left_cancel` is of the form:
  ```
  Nat.mul_left_cancel firstArgument secondArgument
  ```

  The following expression cancels `3` from both sides of `equation`:
  ```
  (Nat.mul_left_cancel two_pos equation) : x = 3
  ```

  Note that:
  ```
  two_pos : 0 < 2
  ```
  where 'pos' stands for positive.

  Arguments are given without paranthesis
  is the first argument given to `Nat.mul_left_cancel` and `equation` is the second.

  Adapt this to the current problem.
  "
  Hint (hidden:=true) "
  Notice that `mul_left_cancel₀ four_ne_zero h` has type `y = 4`. So, `exact mul_left_cancel₀ four_ne_zero h` will do it."
  exact Nat.mul_left_cancel four_pos h
}

Conclusion
"
Here is the type signature of Nat.mul_left_cancel:
  ```
Nat.mul_left_cancel 
(np : 0 < n) 
(h : n * m = n * k) 
: m = k
  ```
  `Nat.mul_left_cancel` takes two arguments which are:
   - `np`, a proof that some number `n` is positive.
   - `h`, the equation which has `n` on both sides of the equation multiplied on the left.

  The result is whats after `:` , canceling `n` from both sides of the equation giving a proof `m = k`.
"

NewTheorem Nat.mul_left_cancel four_pos
NewDefinition UnicodeSymbols
