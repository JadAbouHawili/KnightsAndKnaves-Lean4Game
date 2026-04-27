import Game.Levels.Simp_World.L01_or_false
import Game.Levels.Simp_World.L02_true_or
import Game.Levels.Simp_World.L03_not_or
import Game.Levels.Simp_World.L04_not_and_or
import Game.Levels.Simp_World.L05_not_not
import Game.Levels.Simp_World.L06_iff_of_false
import Game.Levels.Simp_World.L07_iff_of_true
import Game.Levels.Simp_World.L08_not_iff
import Game.Levels.Simp_World.L09_not_iff_not

World "Simp_World"
Title "Simplification"
Introduction
"
In the previous world, we introduced logical connectives and how to construct new propositions using them.

In this world, we will simplify logical expressions involving these connectives. The `simp` tactic
can take care of that.

But in this world , simplifications will be done manually so you gain an idea of what `simp` is
capable of and you should almost always use `simp` in upcoming worlds.

"
