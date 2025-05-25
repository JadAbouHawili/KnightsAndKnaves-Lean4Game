import Game.Metadata
import Game.LevelLemmas.dsl_KnightsAndKnaves


World "DSL_Knights_Knaves"
Level 2
-- prob 30
Title ""

Introduction
"
`A` says 'I am a knave or 2+2=5'.

`2+2=5` is false

`P or False` is `P`

Use `simp` to do these simplications for you.
"
open Islander
Statement {A : Islander} (stA : A said (A.isKnave or (2+2=5)))
: False := by
  Hint (hidden := true)
  "
`simp at stA`
  "
  simp at stA
  Hint
  "
This should look familiar.

Don't repeat the proof!
  "
  Hint (hidden:=true)
  "
Use `dsl_iamknave`.
  "
  exact dsl_iamknave stA

Conclusion
"
"
NewTheorem Islander.dsl_iamknave
