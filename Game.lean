import Game.Levels.EquationalReasoning
import Game.Levels.Logic
import Game.Levels.Simp_World
import Game.Levels.DSL_Knights_Knaves
import Game.Levels.KnightsAndKnaves2
import Game.Levels.SetTheory_Knights_Knaves

Title "Knights And Knaves Game"
Introduction
"
This is a gamification of mathematical proofs. Every level has a `Goal`, which is what you are trying to prove. You will use tactics and theorems provided by the `Lean` theorem prover and its mathematical library `mathlib` to close the `Goal`.

# Helpful Links
You can click the hamburger menu in the top right then 'Game Info' for more information:
- Official Documentation
- Community Chat
- Sources Of Puzzles
"

Info
"
# Official Documentation

Many technical details have been skipped for the sake of not getting bogged down with `Lean` and its mathematical library `mathlib`, but focus on the aspects of reasoning and proof.

Moreover, the Docs in the right side pane are custom written to provide only what you need to progress through the game.

You can of course go deeper by searching through the [official docs](https://leanprover-community.github.io/mathlib4_docs/)

# Zulip Community Chat

Zulip chat for `Lean` has been a very useful resource to resolve issues when formalizing the exercises, you can visit it and ask questions in the '#new members' stream. You can also view messages without signing up. There are other streams dedicated to various topics you can check out as well.

https://leanprover.zulipchat.com/

https://zulip.com/case-studies/lean/

# Sources for Puzzles:

Some puzzles were taken as is, others were modified or inspired variations.

- Wolfram Cloud [Puzzle
Generator](https://www.wolframcloud.com/objects/demonstrations/KnightsAndKnavesPuzzleGenerator-source.nb)

- [382 Puzzles](https://philosophy.hku.hk/think/logic/knights.php)

- [What Is The Name Of This Book](https://raymondsmullyan.com/books/what-is-the-name-of-this-book/) by Raymond Smullyan

- Knights and Knaves in a logic programming language (prolog):
https://www.youtube.com/watch?v=oEAa2pQKqQU

- Blog post series, includes introduction, representation and formalization, automated solutions using other provers, and creating your own puzzles.
https://summerofgodel.blogspot.com/2019/04/table-of-contents-for-series-of-posts.html?


# Editor Mode

Editor mode mimics the `Lean` experience in vscode which is the most common way to use `Lean`.

To access editor mode, click on the icon next to the hamburger menu in the top right when in a level.

# Links
## Documentation
https://leanprover-community.github.io/mathlib4_docs/

https://lean-lang.org/documentation/

https://leanprover-community.github.io/

https://lean-lang.org/

https://github.com/leanprover-community/mathlib4

# Rules
You can relax the rules and skip levels.

This is not recommended for if you have never used `Lean` before because every level depends on
introduced tactics/theorems/ideas in previous levels. Moreover, relaxing the rules would ruin the
structured/guided experience this game is supposed to offer. If that is what you are looking for, then don't relax the rules.

# Solutions
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
Dependency DSL_Knights_Knaves → SetTheory_Knights_Knaves
/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
