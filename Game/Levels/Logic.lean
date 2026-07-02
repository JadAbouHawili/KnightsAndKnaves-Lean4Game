import Game.Levels.Logic.L01_Intro
import Game.Levels.Logic.L02_And
import Game.Levels.Logic.L03_And_elimination
import Game.Levels.Logic.L04_Or
import Game.Levels.Logic.L05_Implication
import Game.Levels.Logic.L06_ImpGoal
import Game.Levels.Logic.L07_cases
import Game.Levels.Logic.L08_LogicalEquivalence
import Game.Levels.Logic.L09_Not
import Game.Levels.Logic.L10_False
import Game.Levels.Logic.L11_have
import Game.Levels.Logic.L12_have

World "Logic"
Title "Logic"
Introduction
"
In this world, we will be working with `Objects` of type `Prop`, i.e. propositions.

You can think of a proposition as a statement that is either true or false. You have seen propositions before like `x = 2`, `y = 6` etc..

Given `h : P` where `P : Prop`, we say that `h` is a proof of the statement `P`.

For example `h : x = 2` is a proof that `x = 2`


In a proof state, this would look like the following:
```
Objects
P : Prop
Assumptions
h : P
```
"
