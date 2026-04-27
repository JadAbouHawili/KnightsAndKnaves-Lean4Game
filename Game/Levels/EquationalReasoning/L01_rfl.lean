import Game.MathlibTheorems
import Game.Doc.doc
import Game.Doc.tactic_doc

World "EquationalReasoning"
Level 1

Title "`rfl`, A Number Equals Itself"

Introduction "In this exercise, we will prove `2 = 2`

`rfl` will do the job.

`rfl` is short for reflexivity, which is the property that for any number `a`, `a = a`

"

Statement
  : 2 = 2 := by

  {
    rfl
  }

Conclusion
"
Notice the yellow highlights in the right side pane , showing newly introduced tactics/definitions/theorems which you will need to solve the current level and can use in future levels as well.

Use this as a reference for documentation and examples if you ever get stuck.
"

NewTactic rfl
