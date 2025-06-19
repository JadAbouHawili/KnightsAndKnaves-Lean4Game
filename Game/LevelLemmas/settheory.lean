import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Game.LevelLemmas.Logical

-- experiment with simp_rw

#check not_iff_not
#check not_iff_self
theorem inleft_notinright
  [inst : DecidableEq K]
  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(Aleft : A ∈ left) : A ∉ right := by
  intro a
  #check Finset.mem_inter_of_mem
  have := Finset.mem_inter_of_mem Aleft a
  rw [h] at this
  contradiction

theorem inright_notinleft
  [inst : DecidableEq K]
  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(Aright : A ∈ right) : A ∉ left := by
  intro a
  have := Finset.mem_inter_of_mem Aright a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

theorem inleft_notinrightIff
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
: A ∈ left ↔  A ∉ right := by
  constructor
  · exact inleft_notinright h
  · exact notright_left LeftorRight

theorem notinleft_inrightIff
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
: A ∉ left ↔  A ∈ right := by
  constructor
  · exact notleft_right LeftorRight
  · exact inright_notinleft h

theorem inright_notinleftIff
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
: A ∈ right ↔  A ∉ left := by
  constructor
  · exact inright_notinleft h
  · exact notleft_right LeftorRight

theorem notinright_inleftIff
  {inst : DecidableEq K}
  {A : K}
  {left : Finset K} {right : Finset K}
  (LeftorRight : A ∈ left ∨ A ∈ right)
  (h : left ∩ right = ∅)
 : A ∉ right ↔  A ∈ left := by
  constructor
  · exact notright_left LeftorRight
  · exact inleft_notinright  h

theorem disjoint {inst : DecidableEq K}  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(Aleft : A ∈ left)
(Aright : A ∈ right)  : False := by
  have := Finset.mem_inter_of_mem Aleft Aright
  rw [h] at this
  contradiction

theorem XorToOr {inst : DecidableEq Inhabitant}{Knight : Finset Inhabitant } {Knave : Finset Inhabitant} (A : Inhabitant)
(h : Knight ∩ Knave = ∅ ) : Xor' (A ∈ Knight) (A ∈ Knave) ↔ A ∈ Knight ∨ A ∈ Knave := by
  constructor
  unfold Xor' at *
  · intro h'
    cases h'
    · exact Or.inl (h_1.left)
    · exact Or.inr (h_1.left)

  · intro h'
    unfold Xor'
    cases h'
    · left
      constructor
      assumption
      exact inleft_notinright h h_1
    · right
      constructor
      assumption
      exact inright_notinleft h h_1

