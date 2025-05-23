import Game.Metadata

World "Logic" 
Level 10

Title "`have`" 

Introduction 
"
In this level, we introduce the `have` tactic. 
You have to prove `R` but to do that, you need `Q` first. 

Use `have hQ : Q` to change the goal to proving `Q`. And when the proof is done, it would be named `hQ` and added to the assumptions in the proof state.
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
Now that you proved `Q`, its proof `{hQ} : Q` has been added to the assumptions.

`hQR` takes `{hQ}` and gives you a proof of `R` which is the goal.
  "
  exact hQR hQ
  }

Conclusion
"
`have h : P` changes the goal to proving `P` and adds the proof `h` after that goal is closed.
"
NewTactic «have»


/-
--------------
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
