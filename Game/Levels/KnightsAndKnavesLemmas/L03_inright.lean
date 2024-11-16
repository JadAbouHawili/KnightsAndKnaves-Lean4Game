import Game.Metadata


World "KnightsAndKnavesLemmas" 
Level 4

Title "" 

Introduction 
"
This has a very similar reasoning to inleft.

The reasoning goes as follows:
Assume `A ∈ left`.
Then `A ∈ left ∩ right` 
But `left ∩ right = ∅ `, so `A ∈ ∅`. 
This is a contradiction
"

Statement inright_notinleft
  --sets
  {left : Set K} {right : Set K}
(h : left ∩ right = ∅ )
(h' : A ∈ right) : A ∉ left := by
  intro a 
  have := Set.mem_inter h' a
  rw [Set.inter_comm] at h
  rw [h] at this
  contradiction

Conclusion 
"
"
