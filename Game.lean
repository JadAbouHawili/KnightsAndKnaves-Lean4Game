import Game.Levels.EquationalReasoning
import Game.Levels.Logic
import Game.Levels.Simp_World
import Game.Levels.DSL_Knights_Knaves
import Game.Levels.KnightsAndKnaves2

Title "Knights And Knaves Game"
Introduction
"
This is a gamification of mathematical proofs. Every level has a `Goal`, which is what you are trying to prove. Closing the `Goal` means you have proven the theorem and there is nothing else to do.

You will use the `Lean` theorem prover, and its mathematical library `mathlib`.

# Right Side Pane(Docs Pane)
Let's explain what's going on in the right side pane.

This is where you can find the tactics, definitions, and theorems at your disposal which were introduced in previous levels.

Clicking on one will display an overview and some examples. This will be available to you at all times when working on the levels. Refer back to it whenever you need to.

Any new tactic, theorem, or definition introduced in a level will be highlighted in a yellow color.


We now discuss each section in the right side pane.
## Tactics
In this puzzle game, you will use tactics to manipulate the `Goal` and close it, essentially proving the `Goal`. Tactics will be incrementally introduced, and tactics that haven't been introduced yet will have a lock icon which means you can't use them yet.

## Definitions
The point of this game is not just to showcase `Lean`, but also to learn some mathematics. Relevant definitions will be displayed here.

## Theorems
Here is listed theorems to use throughout the levels. Some you would have proven in previous levels and others are presented for you to use but without having proven them. An intuitive explanation of why the theorem makes sense will be presented as well when it is introduced.

# Official Documentation
The Docs in the right side pane are custom written to provide only what you need to progress through the game.

You can of course go deeper by searching through the [official docs](https://leanprover-community.github.io/mathlib4_docs/)

## Editor Mode

You can view them inside a level by entering editor mode and hovering over the term.

You can enter editor mode by clicking the icon next to the hamburger menu that is in the top right hand corner when you are in a level

# Level Structure

Within every level, you have the `Objects` (if any), `Assumptions` (if any), and `Goal` for the current level. This is called the initial proof state.

There will also be a text input to execute tactics accordingly.

`Lean` tracks the proof state as you execute tactics and makes sure you made no mistakes.
You will execute tactics one by one until `Lean` tells you that you have closed the goal.

# More info
You can click the hamburger menu in the top right then 'Game Info' for more information:
- Sources Of Puzzles
etc...
"

Info
"
Many technical details have been skipped for the sake of not getting bogged down with `Lean` and its mathematical library `mathlib`, but focus on the aspects of reasoning and proof. You can search https://leanprover-community.github.io/mathlib4_docs/ for more information about any tactic or theorem used.

# Editor Mode
Editor mode mimics the `Lean` experience in vscode which is the most common way to use `Lean`.

To access editor mode, click on the icon next to the hamburger menu in the top right when in a level.

## vscode-like environment
Hovering over tactics/theorems will give you the official documentation.

# Links
## Documentation
https://leanprover-community.github.io/mathlib4_docs/

https://lean-lang.org/documentation/

https://leanprover-community.github.io/

https://lean-lang.org/

https://github.com/leanprover-community/mathlib4


## Zulip, ask questions
Zulip chat for `Lean` has been a very useful resource to resolve issues when formalizing the exercises, you can visit it and ask questions in the '#new members' stream. You can also view messages without signing up. There are other streams dedicated to various topics you can check out as well.

https://leanprover.zulipchat.com/

https://zulip.com/case-studies/lean/

## Knights and Knaves

### Sources for the puzzles:

Some puzzles were taken as is, other were modified or inspired variations.

- Wolfram Cloud [Puzzle
Generator](https://www.wolframcloud.com/objects/demonstrations/KnightsAndKnavesPuzzleGenerator-source.nb)

- [382 Puzzles](https://philosophy.hku.hk/think/logic/knights.php)

- [What Is The Name Of This Book](https://raymondsmullyan.com/books/what-is-the-name-of-this-book/) by Raymond Smullyan

### Insightful:

- Knights and Knaves in a logic programming language (prolog):
https://www.youtube.com/watch?v=oEAa2pQKqQU

- Blog post series, includes introduction, representation and formalization, automated solutions using other provers, and creating your own puzzles.
https://summerofgodel.blogspot.com/2019/04/table-of-contents-for-series-of-posts.html?

# Rules
You can relax the rules and skip levels.

This is not recommended for if you have never used `Lean` before because every level depends on
introduced tactics/theorems/ideas in previous levels. Moreover, relaxing the rules would ruin the
structured/guided experience this game is supposed to offer. If that is what you are looking for, then don't relax the rules.

# Github, Level Solutions
[Github Repository](https://github.com/JadAbouHawili/KnightsAndKnaves-Lean4Game)

You can view the `Lean` code for every level there (and the solution if you are really stuck).

# Other Knights and Knaves Educational Games
[Timer Game](https://en.oiler.education/bul)

[Terminal-Like](https://christopherphelps.trinket.io/sites/knight_knave_puzzler)
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "From the basics to Knights And Knaves"
CaptionLong "A guided experience that teaches you everything you need to know to understand and solve knights and knaves logic puzzles, including the basics of lean and logic.

Based on statements made, you will deductively conclude who is a knight (truthful) and who is a knave (liar)."
CoverImage "images/knights-and-knaves.jpg"

Dependency Logic → Simp_World
Dependency Simp_World → KnightsAndKnaves2
Dependency Simp_World → DSL_Knights_Knaves
/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
