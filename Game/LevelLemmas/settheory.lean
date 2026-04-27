import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Game.LevelLemmas.Logical

variable {K : Type} {A : K}
[DecidableEq K]

theorem disjoint_finset
{left right : Finset K}
(h : left ∩ right = ∅ )
(hk : A ∈ left)
(hkn : A ∈ right)  : False := by
  have := Finset.mem_inter_of_mem hk hkn
  rw [h] at this
  contradiction

theorem inleft_notinright_finset
{S S' : Finset K}
{A : K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S) : A ∉ S' := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [h] at this
  contradiction
#print inleft_notinright_finset

omit [DecidableEq K] in
theorem notinleft_inright
{S S' : Finset K}
{A : K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S) : A ∈ S' := by
  exact notleft_right SorS' h'

theorem inright_notinleft_finset
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(h' : A ∈ S') : A ∉ S := by
  intro a
  have := Finset.mem_inter_of_mem h' a
  rw [Finset.inter_comm] at h
  rw [h] at this
  contradiction

omit [DecidableEq K] in
theorem notinright_inleft
{S S' : Finset K}
(SorS' : A ∈ S ∨ A ∈ S')
(h' : A ∉ S') : A ∈ S := by
  exact notright_left SorS' h'

-------------------
theorem inleft_notinrightIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S ↔  ¬(A ∈ S') := by
  constructor
  · exact inleft_notinright_finset h
  · exact notinright_inleft SorS'

theorem notinleft_inrightIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∉ S ↔  A ∈ S' := by
  constructor
  · exact notinleft_inright SorS'
  · exact inright_notinleft_finset h

theorem inright_notinleftIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
: A ∈ S' ↔  A ∉ S := by
  constructor
  · exact inright_notinleft_finset h
  · exact notleft_right SorS'

theorem notinright_inleftIff
{S S' : Finset K}
(h : S ∩ S' = ∅ )
(SorS' : A ∈ S ∨ A ∈ S')
 : A ∉ S' ↔  A ∈ S := by
  constructor
  · exact notinright_inleft SorS'
  · exact inleft_notinright_finset h

theorem set_subset_univ2
{A B : K}
 {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B )
: S ⊆ ({A,B} : Finset K) := by
  intro x h ; simp ;  exact all x

theorem set_subset_univ3
{A B C : K}
 {S : Finset K}
(all : ∀ (x : K), x = A ∨ x = B ∨ x = C)
: S ⊆ ({A,B,C} : Finset K) := by
  intro x h ; simp ;  exact all x

theorem inleft_notinright
{K : Type}
{A : K}
  [inst : DecidableEq K]
  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(Aleft : A ∈ left) : A ∉ right := by
  intro a
  apply @disjoint_finset K
  repeat assumption

theorem inright_notinleft
  {left : Finset K} {right : Finset K}
(h : left ∩ right = ∅ )
(Aright : A ∈ right) : A ∉ left := by
  exact inright_notinleft_finset h Aright
