import Game.Levels.SetTheory_Knights_Knaves.L01_IamKnave

import Game.Levels.SetTheory_Knights_Knaves.L02_2plus2
import Game.Levels.SetTheory_Knights_Knaves.L03_prob26
import Game.Levels.SetTheory_Knights_Knaves.L04_IKnaveOrKnave
import Game.Levels.SetTheory_Knights_Knaves.L05_prob29
import Game.Levels.SetTheory_Knights_Knaves.L06_prob33
import Game.Levels.SetTheory_Knights_Knaves.L07_difftype
import Game.Levels.SetTheory_Knights_Knaves.L08_sametype
import Game.Levels.SetTheory_Knights_Knaves.L09_same
import Game.Levels.SetTheory_Knights_Knaves.L10_allofus
import Game.Levels.SetTheory_Knights_Knaves.L11_prob32
import Game.Levels.SetTheory_Knights_Knaves.L12_31
import Game.Levels.SetTheory_Knights_Knaves.L13_prob27

World "SetTheory_Knights_Knaves"
Title "SetTheory Knights and Knaves"
Introduction
"
In this world , we use set theory instead of a `DSL` to represent and solve knights and knaves
puzzles.

Here's a table with a correspondence
| Set Theory       | DSL           |
| ------------- |:-------------:|
| `h : A ∈ Knight`  | `h : A.isKnight` |
| `h : A ∉ Knight` | `h : ¬A.isKnight` |
| `h : A ∈ Knave`  | `h : A.isKnave` |
| `h : A ∉ Knave`  | `h : ¬A.isKnave` |
| `h : A ∈ Knight ∨ A ∈ Knave` | `h : A.isKnight or A.isKnave` |
| `h : Knight ∩ Knave = ∅` | `h : not (A.isKnight and A.isKnave)` |


You will not have to use `h : A ∈ Knight ∨ A ∈ Knave` directly but you will use the tactic
`knight_or_knave A with AKnight AKnave` to take cases

Moreover , if you know that `A ∈ Knight` and `A ∈ Knave` then this would contradict `h : Knight ∩
Knave = ∅` which says that the sets `Knight` `Knave` have an empty intersection i.e no common
element. You will not have to use `h` directly , you can just use `contradiction` and the goal will
be closed
"
