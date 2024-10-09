import Game.Metadata


World "KnightsAndKnaves" 
Level 5

Title "" 

Introduction 
"
Again we have three people, A, B, C, each of whom is either 
a knight or a knave. A and B make the following statements: 
A: All of us are knaves. 
B: Exactly one of us is a knight. 
What are A, B, C?
"



inductive Solution (Knight : Finset Inhabitant) (Knave : Finset Inhabitant)
| submit (h : A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knave) : Solution (Knight) (Knave)
-- i could obfuscate this by making a type that when given the correct argument solves the exercise.
-- all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C
-- {stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }




#check Set.mem_setOf
example (S : Set K) : S = {x | x ∈ S} := by exact rfl
  
  ----
  --exact (Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 => all a).symm


-- try using Set.univ as an axiom instead and see if there are any advantages
#check Finset.univ
example {A B C : K} {inst : Fintype K} {inst2 : DecidableEq K}  : Finset.univ = ({A,B,C} : Finset K) ↔  ∀ (x : K), x = A ∨ x = B ∨ x = C:= by 
--  #check Finset.univ
--  #check Finset.toSet Finset.univ
--  #check Finset.coe_inj
--  #check ↑(Finset.univ)
--  rw [Finset.coe_inj.symm]
--  #check Finset.coe_inj
--  #check Finset.toSet
--  have : Finset.univ = {A,B,C} ↔ Set.univ = {A,B,C} := by 
--    constructor
--    · intro Fu
--      rw [Fu]
--    · sorry


    --apply?

  constructor
  · intro U
    intro x
    #check Finset.mem_univ
    have : x ∈ Finset.univ := Finset.mem_univ x 
    rw [U] at this
    #check instDecidableEqBool
    #check Finset.mem_insert_of_mem
    #check Finset.mem_insert
    rw [Finset.mem_insert] at this
    rw [Finset.mem_insert] at this
    rw [Finset.mem_singleton] at this
    assumption
  · intro U
    apply Finset.ext
    intro a
    constructor
    · intro aU
      cases U a
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · cases h
        · rw [h_1]  
          #check Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_1]
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl

    · exact fun a_1 => Finset.mem_univ a




example {inst : DecidableEq K} {Knave : Finset K} {A B C : K} (all : ∀ (x : K), x = A ∨ x = B ∨ x = C) : (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) ↔ (Knave = ({A,B,C} : Finset K) ) := by 
  constructor
  · intro allknaves
    #check Finset.ext
    apply Finset.ext
    intro a
    constructor
    · intro aKn
      cases all a
      · rw [h]
        exact Finset.mem_insert_self A {B, C}
      · cases h
        · rw [h_1]
          #check Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_insert_self B {C}
        · rw [h_1]  
          apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          exact Finset.mem_singleton.mpr rfl

    · intro aIn
      -- dont need aIn
      cases all a
      · rw [h]  
        exact allknaves.left
      · cases h
        · rw [h_1]
          exact allknaves.right.left
        · rw [h_1]
          exact allknaves.right.right

  · intro KnaveEveryone
    rw [KnaveEveryone]  

    -- set theoretic
    constructor
    · exact Finset.mem_insert_self A {B, C}
    · constructor

      · apply Finset.mem_insert_of_mem
        exact Finset.mem_insert_self B {C}

      · apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        exact Finset.mem_singleton.mpr rfl


-- using Finset.univ instead of all
-- another formalization using cardinalities instead of A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave
example
  {inst : DecidableEq Inhabitant}
  {inst2 : Fintype Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {all : Finset.univ = {A,B,C}}
  --{all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  { AneB : A ≠ B}
  { BneC : B ≠ C}
  { AneC : A ≠ C}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution Knight Knave:= by
  have AKnave : A ∈ Knave := by {
      #check iff_iff_implies_and_implies
      have := (iff_iff_implies_and_implies _ _).mp stA
      by_contra AKnight
      rw [notinright_inleftIff h1 h] at AKnight
      have AKnave := stA.mp AKnight
      exact IamKnave h h1 (by simp[AKnight,AKnave.left] )
      --exact disjoint h AKnight AKnave.left 
    }
  have BKnight : B ∈ Knight := by 
    by_contra BKnave
    have notallKnaves := stAn.mp AKnave
    rw [notinleft_inrightIff h2 h] at BKnave
    simp [AKnave,BKnave] at notallKnaves
    -- stB is equivalent to Knight.card = 1
    -- have a theorem which says given the universe, Knight.card = 1, and the first element in not in knight and the second as well then the third has to be. this idea of a universe need to be explicitly explained.
    have : Knight ⊆ Finset.univ := by exact Finset.subset_univ Knight
    rw [all] at this 
    rw [inright_notinleftIff h1 h] at AKnave
    rw [inright_notinleftIff h2 h] at BKnave

  -- Set.subset_insert_iff_of_not_mem.{u} {α : Type u} {a : α} {s t : Set α} (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t

    #check Finset.subset_insert_iff_of_not_mem
    #check Finset.subset_insert_iff_of_not_mem AKnave
--    simp [AKnave,BKnave] at this
    #check (Finset.subset_insert_iff_of_not_mem AKnave).mp this
--    have smaller :=      (Finset.subset_insert_iff_of_not_mem AKnave).mp this

    have helper: {A,B,C} = insert A ({B,C} : Finset Inhabitant) := by rfl
    rw [helper] at this
    -- name is too long? or make the user understand the naming convention
    rw [(Finset.subset_insert_iff_of_not_mem AKnave)] at this
    rw [(Finset.subset_insert_iff_of_not_mem BKnave)] at this
    have Csubset : {C} ⊆ Knight := by
    -- make this into a theorem, C ∈ Knight so the singleton subset of knight. mem_singleton_subset
      intro x
      intro xC
      #check mem_of_eq_singleton
      #check mem_of_eq_singleton
      #check Finset.mem_singleton
      #check Finset.mem_singleton_self
      rw[Finset.mem_singleton] at xC
      rw [xC]
      exact (notright_left h3 notallKnaves )
      
    have : Knight = {C} := by exact Finset.Subset.antisymm this Csubset

    have BKnight := stB.mpr (by right ; right ; assumption)
    contradiction

  sorry
example {S : Set K} (h : S ⊆ {A} ∪ S') (h' : A ∉ S) : S ⊆ S' := by exact (Set.subset_insert_iff_of_not_mem h').mp h

-- make this into a theorem because the name is too complicated??? or just prepare the user more to handle and understand the naming convention
example {S : Set K} {AinS : A ∈ S} : {A} ⊆ S := by exact Set.singleton_subset_iff.mpr AinS


Statement
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
  {all : ∀(x : Inhabitant), x = A ∨ x = B ∨ x = C}
  { AneB : A ≠ B}
  { BneC : B ≠ C}
  { AneC : A ≠ C}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB: B ∈ Knight ↔ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
{stBn: B ∈ Knave ↔ ¬ (Knight = {A} ∨ Knight = {B} ∨ Knight = {C}) }
  : Solution Knight Knave:= by

  {
    -- this is similar to i am a knave
    have AKnave : A ∈ Knave := by {
      #check iff_iff_implies_and_implies
      have := (iff_iff_implies_and_implies _ _).mp stA
      by_contra AKnight
      rw [notinright_inleftIff h1 h] at AKnight
      have AKnave := stA.mp AKnight
      exact IamKnave h h1 (by simp[AKnight,AKnave.left] )
      --exact disjoint h AKnight AKnave.left 
    }

    have BKnight : B ∈ Knight := by {
      by_contra BKnave
      rw [notinleft_inrightIff h2 h] at BKnave

      --push_neg at stBn 
      --rw [not_and_or] at stAn
      --rw [not_and_or] at stAn
      -- 
      --simp[AKnave] at stAn 
      --simp[BKnave] at stAn 
       
      --have := stBn.mp BKnave
      -- last one left theorem, its own level?
      have CKnight : C ∈ Knight := by 
        have Knaves := stAn.mp AKnave
        repeat rw [not_and_or] at Knaves
        --push_neg at Knaves
        simp [AKnave,BKnave] at Knaves
        exact notright_left h3 Knaves 

       
      have KnighteqC : Knight = {C} := by
        #check Set.eq_of_subset_of_subset   
        rw [Finset.eq_singleton_iff_unique_mem] 
        constructor
        · assumption
        -- make a theorem of this and for all the cases
        · intro x
          intro xK
          cases all x
          · rw [h_1] at xK
            exfalso 
            exact disjoint h xK AKnave
          · cases h_1
            · rw [h_2] at xK
              exfalso
              exact disjoint h xK BKnave
            · assumption
      ---
      have BKnight:= stB.mpr (by right; right; assumption)
      exact disjoint h BKnight BKnave  
    }

    have CKnave : C ∈ Knave := by {
      have OneKnight := stB.mp BKnight
      by_contra CKnight 
      #check notright_left
      have CKnight := notright_left h3 CKnight
      -- now theorem
      #check full_singleton
      cases OneKnight 
      · 
        #check Finset.singleton_subset_iff
        #check Finset.subset_of_eq
        have AKnight := mem_of_eq_singleton h_1
        exact disjoint h AKnight AKnave
        
        --rw [Finset.singleton_subset_iff] at h_1
      · cases h_1
        · 
          -- teach this
          exact full_singleton h_2 CKnight (by symm ;exact BneC)
        · exact full_singleton h_2 BKnight BneC

      --cases OneKnight 
      --· rw [h_1] at BKnight
      --  have := Finset.mem_singleton.mp BKnight
      --  symm at this
      --  contradiction
      --· cases h_1 
      --  · rw [h_2] at CKnight
      --    have := Finset.mem_singleton.mp CKnight
      --    symm at this
      --    contradiction
      --  · rw [h_2] at BKnight
      --    have := Finset.mem_singleton.mp BKnight
      --    -- make a full version but for this, i can turn Knight={C} into card one and use full
      --    #check full
      --    contradiction
    }
    #check Finset.mem_singleton

    -- now submit
    sorry

  }
#check Finset.mem_singleton
    --  #check Set.eq_singleton_iff_unique_mem

example (S : Set K) (h : S ⊆ {A,B,C}) (h': A ∉ S) : S ⊆ {B,C} := by   
  exact (Set.subset_insert_iff_of_not_mem h').mp h

   
#check Set.mem_singleton_iff
#check Set.subset_insert_iff_of_not_mem




Conclusion 
"
"

