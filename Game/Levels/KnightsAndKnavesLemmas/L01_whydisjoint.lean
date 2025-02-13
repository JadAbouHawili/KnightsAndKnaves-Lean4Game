import Game.Metadata

World "KnightsAndKnavesLemmas" 
Level 1

Title "`disjoint` theorem"

Introduction
"
Before diving into an actual knights and knaves puzzle, lets explore basic results implied by the assumptions of this puzzle.

We will first look at the assumption that no one can be a knight and a knave at the same time.
It is represented as:
```
h : Knight ∩ Knave = ∅ 
```

The reasoning in this level applies to any two finite sets, so we use the two sets `left`,`right`.

In our problem, we have:
```
Aleft: A ∈ left
Aright: A ∈ right
h : left ∩ right = ∅
```
This means that `A` belongs to both `left` and `right` i.e `A ∈ left ∩ right`.

So, we do have someone who is both a knight and a knave. 
This would contradict `h` giving us `False` which is the goal.

To show `A ∈ left ∩ right`, we introduce the `have` tactic of the following syntax:
```
have [theorem-name] : [theorem-prop] 
```

We give the following concrete example:
```
have a : 2=2
```
This would change the goal to `2=2` and when proven, would then add `a` to the list of hypotheses with the original goal.

In other words, `have` allows you to add a theorem/hypothesis, which in this level we want it to be `A ∈ left ∩ right`.
"
/-
Heres an example:
`have twoEqualstwo : 2=2 := rfl` will add an object named `twoEqualstwo` of type `2=2` to the proof state which would look as follows:
```
Assumptions:
twoEqualstwo : 2=2
```

You can choose any name after `have` and any type after `:`.
-/
/-
Given the following proof state:
```
Assumptions:
four_pos : 0 < 4
h : 4 * y = 16
```
`have yEqFour := Nat.mul_left_cancel four_pos h` will result in the following proof state:
```
Assumptions:
four_pos : 0 < 4
h : 4 * y = 16
yEqFour : y = 4
```
-/

#check xor_iff_not_iff

/-
journey of formalization:
The two sets Knight and Knave must be disjoint. You can't tell the truth and lie at the same time because if that is true, then you would be asserting `p ∧ ¬p` which can be used to derive `False` i.e a contradiction.
-/

#check disjoint
#check Finset.not_mem_empty 
example (x : False) : False := by
  revert x
  exact id

Statement {inst : DecidableEq Inhabitant}{left : Finset Inhabitant } {right : Finset Inhabitant}
(Aleft : A ∈ left)
(Aright : A ∈ right)
(h : left ∩ right = ∅)
(A_not_in_Empty : A ∉ (∅ : Finset Inhabitant) )
: False := by{
  have AinInter : A ∈ left ∩ right 
  Hint
  "
Now you have to prove `A ∈ left ∩ right`, which you can do using the following:
```
Finset.mem_inter :
    a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂
```
"

  Hint (hidden := true)
  "
Specifically, the backward direction 
```
Finset.mem_inter.mpr :
    a ∈ s₁ ∧ a ∈ s₂ → a ∈ s₁ ∩ s₂
```
is needed here.
  "
  exact Finset.mem_inter.mpr (And.intro Aleft Aright)
  Hint
  "
Now, notice that {AinInter} has been added.
But,  `left ∩ right = ∅` so `A ∈ ∅` 

  We know that `left ∩ right = ∅`, so replace it with `∅` using `rw` getting `A ∈ ∅`.

`rw [h]` would apply on the goal, but we want it to apply at `{AinInter}`. And so `rw [h] at {AinInter}` will do.
  "
  rw [h] at AinInter
  Hint "
So now we have `A ∈ ∅` but the empty set is by defintion the set with no elements i.e `¬ (A ∈ ∅)` written as `A_not_in_empty : A ∉ ∅`. Therefore, `False`.
"
  Hint (hidden := true) " Remember `A ∉ ∅` is `A ∈ ∅ → False` , or use `contradiction`"
  contradiction
}

Conclusion
"
We have proved the following theorem which you can use in future levels:
```
theorem disjoint
(h : left ∩ right = ∅ )
(Aleft : A ∈ left)
(Aright : A ∈ right)
: False
```

Example:
For a goal `False`:
```
exact disjoint h Aleft Aright
```
would close the goal

The two assumptions `AinInter` and `AnotEmpty` are always true for any sets, and are available in Lean but where added explictly to this level for your convenience and to make things easier to explain. So, the `disjoint` theorem can just use them instead of having to take them as arguments.

The theorem `disjoint` can be used for any two disjoint sets, specifically the two sets `Knight`,`Knave`.
"
#check Finset.not_mem_empty

NewTheorem  disjoint Finset.mem_inter
NewDefinition Finset inter KnightsKnaves mem
--NewTactic «have» 
