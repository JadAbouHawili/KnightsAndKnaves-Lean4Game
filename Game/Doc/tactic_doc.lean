import Game.Metadata
/--
`by_contra h` proves `P` by contradiction, introducing a hypothesis `h : ¬P` and proving False i.e proving `¬¬P` which is equivalent to `P`.

If `P` is a negation `¬Q`, h : `Q` will be introduced instead of `¬¬Q`.
-/
TacticDoc by_contra

/--
`rfl` is short for reflexivity. In the context of numbers, it is the property that for any number `a`, `a = a`.

`rfl` also applies more generally, `rfl` will close any goal of the form `A=B` where `A`,`B` are identical. If needed, `rfl` will unfold both sides into their definitions and then check if they are equal. In other words, `rfl` can prove the equality of two things that are 'equal by definition'.

In fact, `rfl` is not a tactic but syntactic sugar for `exact rfl`. `rfl` is of type `a = a` for any `a`.

## examples
```
x - 7 = x - 7
```
`rfl` will close this goal.
-/
TacticDoc rfl

/--
The assumption tactic searches for an assumption that matches the goal, and closes the goal if it finds one.

Given,
```
Objects
P : Prop

Assumptions
hP : P

Goal
P
```
`assumption` will close the goal.
-/
TacticDoc assumption

/--
Given,
```
PorQ : P ∨ Q

Goal
some-goal
```
`cases PorQ` will first assume `P` and ask you to prove `some-goal` and then it will assume `Q` and ask you to prove `some-goal`. So in both cases, `some-goal` is true. Therefore we can conclude `some-goal`. This is called a proof by cases.
-/
TacticDoc cases
/--
`intro` tactic is used to deal with goals of the form `P → Q`.

Having the following:
```
Goal:
P → Q
```
We want to prove that 'If `P` is true, then `Q` is true'. 

To do this, we first need to assume `P` then prove `Q`. Assuming `P` is done using `intro name` for any 'name'.
-/
TacticDoc intro

/--
The `constructor` tactic will split a goal of the form `P ∧ Q` into two subgoals `P`,`Q` where you can deal with each one separately.
-/
TacticDoc constructor

/--
Contradiction is a tactic that detects if you have contradictory assumptions and if so, closes the goal.

Having
```
h : False
```
or
```
hP : P 
hnP : ¬P
```
(or other 'simple' contradictions)
`contradiction` will close any goal.
-/
TacticDoc contradiction

/--
Given the following:
```
Assumptions:
h : A = B

Goal:
some expression involving A
```

`rw [h]` would change the goal by replacing every occurrence of `A` with `B`.

By default, rw uses an equation in the forward direction, matching the left-hand side of the equation `h` with an occurrence of `A` in the goal, and replaces it with the right-hand side i.e `B`. 

The notation `rw [←h]` can be used to instruct the tactic to use the equality `h` in the reverse direction i.e replace an occurrence of `B` with `A`.

## Behavior with `=` and `↔`
For `rw [h]`, the behavior is exactly the same for both, whether you had `h : x=2` or `h : P ↔ Q`.
-/
TacticDoc rw

/--
Having the goal of the form:
```
P ∨ Q
```
for `P Q : Prop`, `left` transforms the goal to `P`.
-/
TacticDoc left

/--
Having the goal of the form:
```
P ∨ Q
```
for `P Q : Prop`, `right` transforms the goal to `Q`.
-/
TacticDoc right

/--
## Overview
For the following proof state:
```
Objects
P : Prop

Assumptions
hP : P

Goal:
P
```
Remember that `hP : P` where `P : Prop` means `hP` is a proof of `P`.

Since the goal is to prove `P`, the only thing we have to do is to let Lean know that we do have such a proof. This is done by `exact h`.

In other words, `hP` is EXACTLY whats needd to prove the goal, the type of `hP` EXACTLY matches the goal, so `exact h` will do the job.
-/
TacticDoc exact

/--
The `have` tactic allows you to add theorems to the context(which you would have to prove, of course).

## one step 
If the proof is one step, then the following:
```
have theorem-name := proof
```
will do.

## multiple steps
If the proof is multiple steps, then:
```
have theorem-name : theorem-prop
```
where `theorem-prop : Prop` will change the current goal to `theorem-prop`.

After being proven, the original goal is restored with `theorem-name : theorem-prop` added(which is a proof of the proposition `theorem-prop`)

### example
```
have a : 2=2
```
will change the goal to `2=2`, which after proving would restore the original goal with the theorem `a : 2=2` added and ready to be used.
-/
TacticDoc «have»
/-
NNG
## Syntax

### without specifying the type
`have name := some-term `
where `name` is the new assumption that will appear which will have `some-type` where `some-term : some-type` and `some-type : Prop` i.e `some-term` is a proof of some proposition.

### with specifying the type
```
have name : some-proposition := by
  proof steps
  ...
  proof steps
```
You would need to use editor mode if there are multiple proof steps.

Inside the have block, you would have a new goal which is `some-proposition` say `x=2` , `A ∈ Knight` etc...

Not specifying the `type` when using `have` doesn't allow you to use tactics.

## Examples

Given the following assumptions from lemmas world, level 1:
```
Assumptions:
Aleft : A ∈ left 
Aright : A ∈ right 
h: left ∩ right = ∅
AinBothInter: A ∈ left ∧ A ∈ right → A ∈ left ∩ right
```

### without specifying the type
`have AinBoth := AinBothInter (And.intro Aleft Aright)` will add the following to the assumptions:
```
AinBoth : A ∈ left ∩ right
```

### specifying the type
`have  AinBoth : A ∈ left ∩ right := by AinBothInter (And.intro Aleft Aright)` will add the following to the assumptions in the proof state:
```
AinBoth : A ∈ left ∩ right
```
-/

/-
reference point: knights and knaves level 4
ones that are needed:
postponing the proof, have a : 2=2, the goal now is 2=2
giving a proof term without specifying type, have name := ...

way to handle have:
- have can be done in one step , so use have :=..
- have needs multiple steps so use have a : 2=2.
tell the user explicitly:
- prove .. which can be done in one step
- prove .. which is done in multiple steps
include this in doc so user can read left side and if confused read right side.
check how nng does it.
-------

## Standard Syntax
```
have theorem-name : theorem-prop 
```
where `theorem-name` can be anything you want, `theorem-prop` is what you want to prove.

The goal changes to:
```
theorem-prop
```
then (after proving it) to the original goal.

## Alternative Syntax
```
`have name-of-object : type := by proof` 
```
`name-of-object` can be whatever you want, leaving it empty would  give the theorem a name automatically. The `type` in this case is the statement we want to prove. 
-/

/--
The `contradiction` tactic works for the following proofs states:
```
h : False
```

```
hP : P
hnP : ¬P
```

and
```
hP : P
```
where Lean knows that `¬P` is true.

Example:
-- disjoint
You need to show that having two sets being disjoint (i.e sharing no common element) and having a common element is a contradiction.
-/
TacticDoc contradiction

/--
Rewrites all expression asserting being a  knight into the equivalent expression of not being knave

Changes all instances of `isKnight A` to `¬isKnave A`

# Goal
`knight_to_knave`

# Hypothesis
`knight_to_knave` at `hypothesis`

# Everything
`knight_to_knave` at *

The `*` is called the 'wildcard', and it matches anything.

# Under the hood
The tactic is simply a macro abbreviating:
```
simp [isKnight_notisKnaveIff]
```
where 
```
isKnight_notisKnaveIff {A : Islander} : A.isKnight ↔ ¬A.isKnave
```

`A.isKnight` and `¬A.isKnave` always have the same truth value regardless of what `A` is , so they can be interchanged
-/
TacticDoc knight_to_knave
