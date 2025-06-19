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
--import Game.Levels.Logic.L10_notleft
--import Game.Levels.Logic.L11_notright

World "Logic"
Title "Logic"
Introduction
"
In this world, we will be dealing with `Objects` of type `Prop` i.e propositions. You can think of a proposition as a statement that is either true or false (obviously, it can't be both at the same time). You have seen propositions before like `x=2`, `y=6` etc..

When you have `h : P` where `P : Prop`, then we say `h` is a proof of the statement `P`(imagine `x=2` instead of `P` if you wish).

In a proof state, this would look like the following:
```
Objects
P : Prop
Assumptions
h : P
```

Moreover, we will discuss constructing new propositions from old ones.

Here's an example in natural language, given the two propositions 'The sun is shining', 'It is Monday', you can construct 'The sun is shining and it is monday'.

Another example would be, having the following:
```
h : `x=2`
h' : `y=6`
```
where `P` is `x=2` and `Q` is `y=6`, we can construct a new proposition `P ∧ Q` which is read as `x=2 and y=6`. Here we know what `P`,`Q` stand for. But, the proposition `P ∧ Q` can still be constructed and reasoned about regardless. Think of reasoning about unknown numbers like `x : ℕ`,`y : ℕ` etc...

But here, the values `P,Q` can take is either true or false.
"
