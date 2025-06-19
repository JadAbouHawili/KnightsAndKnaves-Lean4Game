import Game.Metadata

/--
## Implication defintion
`¬P` is equivalent to `P → False`

Given
```
hnP : ¬P
```
`unfold Not at hnP` will result in:
```
hnP : P → False
```

## truth table
$
\begin{array}{|c c|}
\hline
P & ¬P \\
\hline
T & F \\
F & T \\
\hline
\end{array}
$

$
\begin{array}{|c|c|}
\hline
P & P → False \\
\hline
T & F  \\
F & T  \\
\hline
\end{array}
$

Notice that this definition is an implication and that the truth table with `¬P` and the truth table with `P → False` are identical.

## `¬P` as the goal
What this means is that to prove `¬P`, we assume `P` and derive a contradiction i.e. constructing an object of type `False`.
In other words, having `¬P` as a goal, you have to start the proof with `intro` because you are proving an implication.
-/
DefinitionDoc Not as "¬"

/--
Proving `False` means deriving a contradiction.

A contradiction is when `P` and `¬P` are both true. We say that `P` and `¬P` contradict each other.

# Principle of explosion, from `False` anything follows.
This principle asserts that if you have contradictory assumptions then you can prove anything.
```
hP: P
hnP: ¬P
```
Since `hnP : ¬P` is `P → False`, we can obtain `hnP hP : False`.

Moreover, we know that `False.elim : False → Q` for any `Q : Prop` and so `False.elim (hnP hP) : Q`. (using `contradiction` would close the goal as well, without having to use `False.elim`)
-/
DefinitionDoc False as "`False`"

/--
You can think of a proposition as a statement that is either true or false (obviously, it can't be both at the same time).

Moreover, these statements are denoted by a symbol like `P`,`Q`,`R`.

For an object of type `P` where `P` is of type Prop, i.e. `h : P` where `P : Prop`, `h` would be a proof or a witness that `P` is true.

# Constructing new propositions from old ones
The atomic propositions in the compound proposition `p ∧ q` are : `p`, `q`. Of course, `p ∧ q` can be used to construct more complicated propositions.

## Connecting Propositions With A Logical Connective
This truth value depends on the truth value of the propositions it was built out of and the rules of the logical connective. This is clearly illustrated in a truth table.

# Truth table
The truth table of a logical connective illustrates the rule for that logical connective, i.e. the truth value of the compound statement depending on the truth value of the propositions it connects.

-/
DefinitionDoc «Prop» as "Prop"

/--
Logical implication `P → Q` is made up of two components:
- The premise, which in this case is `P`
- The conclusion, which in this case is `Q`

`P → Q` is read as 'If P is true, then Q is true.

# truth table
$
\begin{array}{|c c|c|}
\hline
P & Q & P → Q \\
\hline
T & T & T \\
\hline
T & F & F \\
\hline
F & T & T \\
\hline
F & F & T \\
\hline
\end{array}
$

A statement `P → Q` is false when `P` is true and `Q` false, it's true otherwise.

# Implication as a function
What logical implication does is that it takes evidence or proof for `P` and transforms it returning a proof of `Q`.
The truth of `P` IMPLIES the truth of `Q`. A proof of `P` IMPLIES a proof of `Q`.

In other words, it acts like a function. If you give `P → Q` a proof of `P`, you get a proof of `Q`.
-/
DefinitionDoc imp as "→"

/--
`∧` read as 'and'
Truth table:

$
\begin{array}{|c c|c|}
\hline
P & Q & \text{P and Q} \\
\hline
T & T & T \\
\hline
T & F & F \\
\hline
F & T & T \\
\hline
F & F & T \\
\hline
\end{array}
$

# Truth table
The truth table of a logical connective illustrates the rule for that logical connective, i.e. the truth value of the compound statement depending on the truth value of the propositions it connects.
The following truth table illustrates this for the previously discussed `∧` connective.
`T` stands for true
`F` stands for false

$
\begin{array}{|c c|c|}
\hline
P & Q & \text{P and Q} \\
\hline
T & T & T \\
T & F & F \\
F & T & F \\
F & F & F \\
\hline
\end{array}
$

Notice that `P and Q` is true when both `P` is true and `Q` is true, being false otherwise.


-/
DefinitionDoc logic_and as "and"

/--
`∨`

# Truth Table
$
\begin{array}{|c c|c|}
\hline
P & Q & \text{P or Q} \\
\hline
T & T & T \\
\hline
T & F & T \\
\hline
F & T & T \\
\hline
F & F & F \\
\hline
\end{array}
$

From the truth table, we can see that if one of `P`,`Q` is true then `P ∨ Q` is true.

Therefore, if we have `P or Q` as our goal, it is enough to prove `P` or to prove `Q`.

Having `P or Q` as the goal, you can tell Lean that you want to prove the left side by simply typing `left` or the right side by simply typing `right`.
-/
DefinitionDoc logic_or as "or"

/--
`∩` is an operator on sets.

Applying it to two sets `A`,`B`:
```
A ∩ B
```

`A ∩ B` is itself another set, containing elements that are in both `A` and `B`.
In other words, `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`.

`A ∩ B = ∅` means that `A` and `B` have no common element i.e. no element of `A` belongs to both and no element of `B` belongs to both.
In other words, `x ∈ A → x ∉ B`, `x ∈ B → x ∉ A` which are `inleft_notinright` and `inright_notinleft` respectively.
-/
DefinitionDoc inter as "∩"

/--
The theorem `And.intro` takes a proof of `P`, a proof of `Q`, and gives a proof of `P ∧ Q` where `P Q : Prop`.

Given,
```
hP : P
hQ : Q
```
we have `And.intro hP hQ : P ∧ Q`

## Alternative Notation
Typed as `\<hP,hQ\>`,
```
⟨hP,hQ⟩ : P ∧ Q
```
instead of
```
And.intro hP hQ : P ∧ Q
```

-/
TheoremDoc And.intro as "And.intro" in "And"

/--
False.elim : False → C says that from False, any desired proposition C holds.

## Intuitively

Let's check the `→` truth table:
$$
\\begin{array}{|c|c|c|}
\\hline
P & Q & P → Q \\\\
\\hline
T & T & T \\\\
\\hline
T & F & F \\\\
\\hline
F & T & T \\\\
\\hline
F & F & T \\\\
\\hline
\\end{array}
$$

Let's focus on part of the truth table where `P` is `False`, because we want to see what `False` implies.
$$
\\begin{array}{|c|c|c|}
\\hline
Q & False → Q \\\\
\\hline
T & T \\\\
\\hline
F & T \\\\
\\hline
\\end{array}
$$

We have that the implication `False → Q` is true regardless what `Q` represents and regardless whether `Q` is true or is false.

So `False` implies any proposition. This principle is known as: 'From `False` anything follows'.
-/
TheoremDoc False.elim as "False.elim" in "False"

/--

-/
TheoremDoc eq_false as "eq_false" in "Logic"

/--

-/
TheoremDoc eq_true as "eq_true" in "Logic"

/--

-/
TheoremDoc false_implies as "false_implies" in "Logic"

/--

-/
TheoremDoc false_or_iff as "false_or_iff" in "Logic"

/--

-/
TheoremDoc iff_not_comm as "iff_not_comm" in "Logic"

/--
If two propositions are false, then they have the same truth value.

If we know `¬P,¬Q`  then we can conclude that `P,Q` have the same truth value i.e. `P ↔ Q`
-/
TheoremDoc iff_of_false as "iff_of_false" in "Logic"

/--
If two propositions are true, then they have the same truth value.

If we know `P,Q`  then we can conclude that `P,Q` have the same truth value i.e. `P ↔ Q`
-/
TheoremDoc iff_of_true as "iff_of_true" in "Logic"

/--

-/
TheoremDoc iff_true_iff as "iff_true_iff" in "Logic"

/--

-/
TheoremDoc iff_true_right as "iff_true_right" in "Logic"

/--
If we know that `¬P`,`¬Q` have the same truth value then `P`,`Q` have the same truth value.
-/
TheoremDoc not_iff_not as "not_iff_not" in "Logic"

/--

-/
TheoremDoc not_iff_self as "not_iff_self" in "Logic"

/--
Notice that `¬(P or Q)`,
$
\begin{array}{|c | c|c|}
\hline
P & Q & \text{¬(P or Q)} \\
\hline
T & T & F \\
\hline
T & F & F \\
\hline
F & T & F \\
\hline
F & F & T \\
\hline
\end{array}
$

has the same truth table as `¬P and ¬Q`
$
\begin{array}{|c | c|c|}
\hline
P & Q & \text{¬P and ¬Q} \\
\hline
T & T & F \\
\hline
T & F & F \\
\hline
F & T & F \\
\hline
F & F & T \\
\hline
\end{array}
$

Therefore, they are equivalent and can be interchanged.
-/
TheoremDoc not_or as "not_or" in "Logic"

/--
Notice that `¬(P and Q)`,
$
\begin{array}{|c | c|c|}
\hline
P & Q & \text{¬(P and Q)} \\
\hline
T & T & F \\
\hline
T & F & T \\
\hline
F & T & T \\
\hline
F & F & T \\
\hline
\end{array}
$

has the same truth table as `¬P or ¬Q`
$
\begin{array}{|c | c|c|}
\hline
P & Q & \text{¬P or ¬Q} \\
\hline
T & T & F \\
\hline
T & F & T \\
\hline
F & T & T \\
\hline
F & F & T \\
\hline
\end{array}
$

Therefore, they are equivalent and can be interchanged.
-/
TheoremDoc not_and_or as "not_and_or" in "Logic"

/--

-/
TheoremDoc not_true as "not_true" in "Logic"

/--

-/
TheoremDoc not_false as "not_false" in "Logic"

/--

-/
TheoremDoc Classical.not_not as "not_not" in "Logic"

/--

-/
TheoremDoc or_false as "or_false" in "Logic"

/--

-/
TheoremDoc or_false_iff as "or_false_iff" in "Logic"

/--

-/
TheoremDoc true_or as "true_or" in "Logic"

/--

-/
TheoremDoc true_or_iff as "true_or_iff" in "Logic"

/--

-/
TheoremDoc true_implies as "true_implies" in "Logic"

/--
`¬(P ↔ Q)` means that `P` ,`Q` don't have the same truth value i.e. one of them is true and the other is false.

Here are the values for `P`,`Q` where `¬(P ↔ Q)` is satisfied:
$
\\begin{array}{|c | c|c|}
\\hline
P & Q & \\text{¬(P ↔ Q)} \\\\
\\hline
T & F & T \\\\
\\hline
F & T & T \\\\
\\hline
\\end{array}
$

We can conclude that `¬P`,`Q` have the same truth value (`¬P ↔ Q`).
-/
TheoremDoc not_iff as "not_iff" in "Logic"

/--

-/
TheoremDoc not_iff' as "not_iff'" in "Logic"

/--

-/
TheoremDoc notleft_right as "notleft_right" in "Logic"

/--

-/
TheoremDoc four_pos as "four_pos" in "*"

/--
A summary of all the terminology presented throughout the game, in order of appearance.

Theorems represent an implication say:
```
thm : P → Q
```

They work for `P`,`Q` of any type. What `thm` means is the following, give me an object of type `P` and i will return an object of type `Q`.

Therefore, theorems expect arguments given in a specific order after which the obtained expression is an object which has the conclusion as its type.

For
```
thm : P → Q
hP : P
```
`(thm hP) : Q`

For the special case where `P : Prop`, `Q : Prop`, the interpretation of `thm` is what implication in logic means.

What `thm` means is the following, give me an object of type `P` which in this case is a proof of `P` and i will return an object of type `Q` which in this case is a proof of `Q`.

In other words, `thm` means 'If P is true, then Q is true'.
-/
DefinitionDoc Terminology as "Terminology"

/--
## Objects

The objects involved are:
- of type inhabitant indicated by a capital letter
- the two finite sets `Knight`, `Knaves`.

As a proof state:
```
Objects
A : Inhabitant
B : Inhabitant
C : Inhabitant
Knight : Finset Inhabitant
Knave : Finset Inhabitant
```
There will be at most three inhabitants in the puzzles for simplicity, but you can ofcourse have more.

## Assumptions
Knights tell the true and knaves lie. So no one can be both at the same time i.e. `Knight ∩ Knave = ∅`

Moreover, every inhabitant is either a knight or a knave i.e. `A ∈ Knight ∨ A ∈ Knave` for any `A : Inhabitant`.

As a proof state:
```
Assumptions:
h : Knight ∩ Knave = ∅
Or : A ∈ Knight ∨ A ∈ Knave
```

## Summary
Putting every together:
```
Objects
A : Inhabitant
B : Inhabitant
C : Inhabitant
Knight : Finset Inhabitant
Knave : Finset Inhabitant

Assumptions
h : Knight ∩ Knave = ∅
Or : A ∈ Knight ∨ A ∈ Knave
```

## Translating statements to formal notation
Given an inhabitant `A`,

The translation we use is based on the following:
- If `A` is a knight, then `A`'s statement is true.
- If `A`'s statement is true, then `A` is telling the truth i.e. is a knight.

Formally:
```
A ∈ Knight → statement-of-A
statement-of-A → A ∈ Knight
```
where `statement-of-A : Prop` represents `A`'s statement.

Combining them we get,
```
stA : A ∈ Knight ↔ statement-of-A
```

### Quick Example
If,
```
A says B is a knave
```

then,
```
A ∈ Knight → B ∈ Knave
B ∈ Knave → A ∈ Knight
```

Combining them using `↔`:
```
stA : A ∈ Knight ↔ B ∈ Knave
```

### equivalent translations, using knaves
Given inhabitant `A`,

The translation we use is based on the following:
- If `A` is a knave, then `A`'s statement is false, i.e. its negation is true.
- If `A`'s statement is false, then `A` is lying i.e. is a knave.

Formally:
```
A ∈ Knave → ¬statement-of-A
¬statement-of-A → A ∈ Knave
```
where `statement-of-A : Prop` represents `A`'s statement.

Combining them we get,
```
stAn : A ∈ Knave ↔ ¬statement-of-A
```

### Quick Example
If,
```
A says B is a knave
```

then,
```
A ∈ Knave → ¬(B ∈ Knave)
¬(B ∈ Knave) → A ∈ Knave
```

Combining them using `↔`:
```
stAn : A ∈ Knave ↔ ¬(B ∈ Knave)
```
-/
DefinitionDoc KnightsKnaves as "Knights and Knaves"

/-
We have the following correspondence:
$
\\begin{array}{|c|c|c|}
\\hline
\\text{Old way} & \\text{New way} \\\\
\\hline
h : A ∈ Knight & h : A \\\\
\\hline
h : A ∉ Knight & h : ¬A \\\\
\\hline
h : A ∈ Knave  & h : ¬A \\\\
\\hline
h : A ∉ Knave  & h : ¬¬A \\\\
\\hline
\\end{array}
$


The translation of statements made by each inhabitant into a propositional formula remains the same, using `↔` but of course instead of `A ∈ Knight` we just have `A` and instead of `A ∈ Knave` we just have `¬A`.

Notice that there are no explicit assumptions in this representation, but that doesn't mean that this representation is less faithful.

We know that any proposition is either true or false, in our context this would translate to every inhabitant is either a knight or a knave.
```
A ∈ Knight ∨ A ∈ Knave
```
translates to
```
A ∨ ¬A
```

Moreoever, we know that `A ∧ ¬A` is false, which would translate to the fact that no inhabitant can be both a knight or a knave.
```
A ∈ Knight ∧ A ∈ Knave
```
which within the previous representation of finite sets would mean that the set knight and the set knave are disjoint.
```
Knight ∩ Knave = ∅
```

Correspondence:
$
\\begin{array}{|c|c|c|}
\\hline
\\text{Old way} & \\text{New way} \\\\
\\hline
h : A ∈ Knight ∨ A ∈ Knave & h : A ∨ ¬A \\\\
\\hline
h : Knight ∩ Knave = ∅ & h: ¬(A ∧ ¬A)  \\\\
\\hline
\\end{array}
$
-/

/--
The setting is an island.
Every islander will make a statement. There are two types of islanders, 'knights' that always tell the truth, and 'knaves' that always lie.

We give english statements and their corresponding translation to lean.

Given an islander `A`

`A` is a knight
```
A.isKnight
```

`A` is a knave
```
A.isKnave
```

`A` is either a knight or a knave
```
isKnight_or_isKnave (A : Islander)
: A.isKnight or A.isKnave
```

Knights always tell the truth.
```
knight_said
: (A said P) → A.isKnight → P
said_knight
: (A said P) →  P → A.isKnight
```

Knaves always lie.
```
knave_said
: (A said P) →  A.isKnave → ¬P
said_knave
: (A said P) →  ¬P → A.isKnave
```

Since knights always tell the truth and knaves always lie, no islander can be both a knight and a knave. `A` is not a knight and a knave at the same time. This is represented as:
```
not_isKnight_and_isKnave (A : Islander)
: ¬ (A.isKnight ∧ A.isKnave)
```

The objective is to conclude who is a knight and who is a knave, based on the statements of several inhabitants. This will be done using logical reasoning.
-/
DefinitionDoc DSLKnightsKnaves as "DSL Knights and Knaves"

/--
Say we have an islander `A` who could be a knight or a knave.

`A` is represented as
```
A : Prop
```
where having the proposition `A` being true means the islander `A` is a knight and having the proposition `A` being false means the islander `A` is a knave.

Now, we intrepret having a proof of `A` as `A` being a knight, and having a proof of `¬A` as `A` being a knave.

From this, every islander being a knight or a knave is represented as follows:
```
A or ¬A
```

Knights always tell the truth, so if `A` makes some statement `P` we have that `A` being a knight implies that the statement `P` is true
```
A → P
```
Moreover, the statement `P` being true means that `A` is telling the truth i.e. is a knight
```
P → A
```
which can be combined as
```
A ↔ P
```

Similarly for `A` being a knave which implies that the statement `P` is false
```
¬A → ¬P
```
Moreover, the statement `P` being false means that `A` is lying i.e. is a knave
```
¬P → ¬A
```
which are combined as
```
¬A ↔ ¬P
```

No islander can be a knight and a knave at the same time because
```
A ∧ ¬A
```
is false.

This representation captures the rules of the knights and knaves puzzle which are:
- Every islander is either a knight or a knave
- No islander is both a knight and a knave at the same time
- Knights always tell the truth, knaves always lie.
-/
DefinitionDoc PropositionalKnightsKnaves as "Propositional Knights and Knaves"
/--

-/
DefinitionDoc Nat as "ℕ"

/--
### **Logic Constants & Operators**
| $Name~~~$ | $Ascii~~~$ | $Unicode~~~$ | $Unicode Cmd$ |
| --- | :---: | :---: | --- |
| True | `True` |  |  |
| False | `False` |  |  |
| Not | `Not` | ¬ |  `\not` `\neg`  |
| And | `/\` | ∧ | `\and`  |
| Or | `\/` | ∨ |  `\or`  |
| Implies | `->` | → |  `\imp` |
| Iff | `<->` | ↔ | `\iff` |

### **Other Unicode**
| $Name$ | $Unicode~~~$ | $Unicode Cmd$ |
| --- | :---: | --- |
| Angle brackets | ⟨⟩ | `\<>` |
| Left Arrow | ← | `\l` `\leftarrow` `\gets` `\<-` |

-/
DefinitionDoc UnicodeSymbols as "Unicode Symbols"

/--
## Truth Table
`P ↔ Q`  is defined as `(P → Q) ∧ (Q → P)`.

Its truth table looks like the folowing:
$
\begin{array}{|c c|c c|c|}
\hline
P & Q & P → Q & Q → P & P ↔ Q \\
\hline
T & T & T & T & T \\
\hline
T & F & F & T & F \\
\hline
F & T & T & F & F \\
\hline
F & F & T & T & T \\
\hline
\end{array}
$

So, `P ↔ Q` is true when `P,Q` are true or `P,Q` are false, i.e. when `P` and `Q` have the same truth value. Therefore, `P` and `Q` are equivalent from a truth value perspective regardless what the statement of `P` and of `Q` is.

## Extracting Each Implication
```
h : P ↔ Q
h.mp : P → Q
h.mpr : Q → P
```
`h.mp` is the forward direction and `h.mpr` is the backward direction.

## `P ↔ Q` is `P = Q`
Since `P`, `Q` have the same truth value, they can be used interchangeably.
You can think of `P ↔ Q` as `P = Q` and use `rw` in the same way you would if there was an actual `=` in the expression.

For example:
```
h : P ↔ Q
hP : P
```
Doing `rw [h] at hP` results in:
```
h : P ↔ Q
hP : Q
```
-/
DefinitionDoc Iff as "↔"

/--

-/
TheoremDoc Nat.mul_left_cancel as "Nat.mul_left_cancel" in "*"

/--
A is a knight, so whatever A said is true
-/
TheoremDoc Islander.knight_said as "knight_said" in "DSL"

/--
A said something true, so A is a knight.
-/
TheoremDoc Islander.said_knight as "said_knight" in "DSL"
/--
A is a knave, so whatever A said is false
-/
TheoremDoc Islander.knave_said as "knave_said" in "DSL"

/--
A said something that is false (i.e. a lie), so A is a knave
-/
TheoremDoc Islander.said_knave as "said_knave" in "DSL"

/--
For an Islander `A`,
```
isKnight A : Prop
```
or
```
A.isKnight : Prop
```
is the proposition that `A` is a knight.
-/
TheoremDoc Islander.isKnight as "isKnight" in "DSL"

/--
For an Islander `A`,
```
isKnave A : Prop
```
or
```
A.isKnave : Prop
```
is the proposition that `A` is a knave.
-/
TheoremDoc Islander.isKnave as "isKnave" in "DSL"

/--
You can't be a knight and a knave at the same time.

You can't lie and tell the truth at the same time.
-/
TheoremDoc Islander.not_isKnight_and_isKnave as "not_isKnight_and_isKnave" in "DSL"

/--
Similar to `knave_said`.
-/
TheoremDoc Islander.notknight_said as "notknight_said" in "DSL"

/--
A : I am a knave

This implies a contradiction, `False`
-/
TheoremDoc Islander.dsl_iamknave as "dsl_iamknave" in "DSL"
