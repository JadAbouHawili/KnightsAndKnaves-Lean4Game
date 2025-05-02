import Game.Levels.Simp_World.L01_or_false
import Game.Levels.Simp_World.L02_true_or
import Game.Levels.Simp_World.L03_not_or
import Game.Levels.Simp_World.L04_not_and
import Game.Levels.Simp_World.L05_iff_of_false
import Game.Levels.Simp_World.L06_iff_of_true
import Game.Levels.Simp_World.L07_not_iff
import Game.Levels.Simp_World.L08_not_iff_not

World "Simp_World"
Title "Simplification"
Introduction
"
In the previous world, we introduced logical connectives and how to construct new propositions using them.

In this world, we have these expressions and some assumptions about their building blocks and we use this to simplify the expression.

For the first half of this world, all simplifications will be done manually after which the `simp` tactic is introduced. In the second half, you will redo those simplifications but now using the `simp` tactic.(which most if not all of the work)
"
