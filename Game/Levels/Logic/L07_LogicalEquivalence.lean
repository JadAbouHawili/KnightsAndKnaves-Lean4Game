import Game.MathlibTheorems
import Game.LevelLemmas.Logical


World "Logic"
Level 7

Title "Logical Equivalence, `↔`"

Introduction
"
`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`.

Forward Direction: `PsameQ.mp` (`P → Q`)

Backward Direction: `PsameQ.mpr` (`Q → P`)

Which direction do you need to prove the goal?
"

Statement {P Q : Prop} (PsameQ : P ↔ Q) (hP : P)
  : Q := by

  {
  Hint (hidden:=true)
  "
  The forward direction.

  exact PsameQ.mp hP
  "
  exact PsameQ.mp hP
  }

Conclusion
"
`↔` truth table:
$
\\begin{array}{|c c|c c|c|}
\\hline
P & Q & P → Q & Q → P & P → Q ∧ Q → P \\\\\\\\
\\hline
T & T & T & T & T \\\\\\\\
\\hline
T & F & F & T & F \\\\\\\\
\\hline
F & T & T & F & F \\\\\\\\
\\hline
F & F & T & T & T \\\\\\\\
\\hline
\\end{array}
$

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e. when `P` and `Q` have the same
truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective.

Since `PsameQ` means that `P` and `Q` have the same truth value, you can consider think of `PsameQ : P ↔ Q` as `PsameQ : P = Q` and `rw [PsameQ] at hP`. Try it!
"

NewDefinition Iff
