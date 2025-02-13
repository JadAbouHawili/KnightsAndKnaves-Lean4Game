import Game.Metadata


World "Logic" 
Level 8

Title "Logical Equivalence, `↔`" 

Introduction 
"
`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`.

Its truth table looks like the folowing:
$
\\begin{array}{|c c|c c|c|} 
\\hline
P & Q & P → Q & Q → P & P → Q ∧ Q → P\\\\
\\hline
T & T & T & T & T \\\\
\\hline
T & F & F & T & F \\\\
\\hline
F & T & T & F & F \\\\
\\hline
F & F & T & T & T \\\\
\\hline
\\end{array}
$

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e when `P` and `Q` have the same truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective regardless what the statement of `P` and of `Q` is.

In this level we have `PsameQ : P ↔ Q`(`P`, `Q` have the same truth value) and `hP : P`(`P` is true) and so `Q` is true as well.

There are a number of ways to prove this level:
- You can extract the forward direction of `h :P ↔ Q` which is `h.mp : P → Q` and use `hP : P` to prove `Q`(`h.mpr : Q → P` is the backward direction).
- Since `PsameQ` means that `P` and `Q` have the same truth value, you can pretend `↔` is instead `=` and use `rw` at `hP : P` to obtain `hP : Q` and then close the goal.
"

Statement (PsameQ : P ↔ Q) (hP : P)
  : Q := by

  {
  exact PsameQ.mp hP
  }

Conclusion 
"
"
--NewTactic cases
NewTactic «have» cases
