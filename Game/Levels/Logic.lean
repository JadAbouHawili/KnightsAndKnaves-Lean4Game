import Game.Levels.Logic.L01_Intro
import Game.Levels.Logic.L02_And
import Game.Levels.Logic.L03_Or
import Game.Levels.Logic.L04_Implication
import Game.Levels.Logic.L05_ImpGoal
import Game.Levels.Logic.L06_cases
import Game.Levels.Logic.L07_LogicalEquivalence
import Game.Levels.Logic.L08_Not
import Game.Levels.Logic.L09_False
import Game.Levels.Logic.L10_have
import Game.Levels.Logic.L11_have
import Lean
#check Lean.MonadMCtx
World "Logic"
Title "Logic"
Introduction
"
In this world, we will be dealing with `Objects` of type `Prop`, i.e. propositions. You can think of a proposition as a true/false statement. You have seen propositions before like `x=2`, `y=6` etc..

Given `h : P` where `P : Prop`, then we say that `h` is a proof of the statement `P`(imagine `x = 2` instead of `P` if you wish).

In a proof state, this would look like the following:
```
Objects
P : Prop
Assumptions
h : P
```
"
