import Game.Metadata
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

Conclusion "Notice that 'level completed! 🎉' on the bottom. We say that the goal is closed/proven. "

NewTactic rfl
