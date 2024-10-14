import Game.Metadata


World "KnightsAndKnaves" 
Level 6

Title "" 

-- adapat to problems with only 2 inhabitants
Introduction 
"
Suppose instead, A and B say the following: 
A: All of us are knaves. 
B: Exactly one of us is a knave. 
Can it be determined what B is? Can it be determined what 
C is?
"


Statement
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
-- exactly one of us is a knave
-- this can be represented as Knave = {A} ∨ Knave = {B} ∨ Knave = {C}
{stB: B ∈ Knight ↔ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) }
{stBn: B ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight ∨ A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) }
  : A ∈ Knave ∧ C ∈ Knight := by

  {
 -- constructor
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [notinright_inleftIff h1 h] at AKnight
    have knaves := stA.mp AKnight
    exact disjoint h AKnight knaves.left

  constructor
  exact AKnave
  rcases h2 with BKnight|BKnave
  ·  
    rw [not_or] at stBn
    rw [not_or] at stBn
    by_contra CKnave 
    have first : ¬(A ∈ Knave ∧ B ∈ Knight ∧ C ∈ Knight) := by 
      intro ands
      exact CKnave ands.right.right
    have second : ¬(A ∈ Knight ∧ B ∈ Knave ∧ C ∈ Knight) := by 
      intro ands 
      exact CKnave ands.right.right
    have third : ¬( A ∈ Knight ∧ B ∈ Knight ∧ C ∈ Knave) := by 
      intro ands
      rw [inright_notinleftIff h1 h] at AKnave
      exact AKnave ands.left 
    have BKnave := stBn.mpr (And.intro first 
    (And.intro second third)) 
    exact disjoint h BKnight BKnave
  · have notallknaves := stAn.mp AKnave
    rw [not_and_or] at notallknaves 
    have : ¬(A ∉ Knave) := by exact not_not.mpr AKnave
    have BC := notleft_right notallknaves this 

    rw [not_and_or] at BC 
    have : ¬(B ∉ Knave) := by exact not_not.mpr BKnave
    have CKnight := notleft_right BC this
    rw [inleft_notinrightIff h3 h] 
    assumption


  }




example
  --sets
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{AneB : A≠ B}
{BneC : B≠ C}
{AneC : A≠ C}
-- Knave = {A,B,C} ???
-- similar to previous problem
{stA : A ∈ Knight  ↔ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stAn : A ∈ Knave ↔ ¬ (A ∈ Knave ∧ B ∈ Knave ∧ C ∈ Knave) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
  : A ∈ Knave ∧ C ∈ Knight := by
--  A: All of us are knaves. 
--  B: Exactly one of us is a knave.
    have AKnave : A ∈ Knave := by 
      by_contra AKnight
      have AKnight :=notright_left h1 AKnight
      have := stA.mp AKnight
      exact disjoint h AKnight this.left

    constructor
    assumption
    rcases h2 with BKnight|BKnave
    · have knavesingle := stB.mp BKnight
      cases knavesingle
      · by_contra CKnave
        have CKnave:= notleft_right h3 CKnave
        #check full_singleton 
        exact full_singleton h_1 CKnave AneC.symm
      · cases h_1
        · have := not_in_of_singleton h_2 BneC.symm
          exact notright_left h3 this
        · #check not_in_of_singleton
          have := not_in_of_singleton h_2 AneC
          contradiction
    · by_contra CnKnight
      have CKnave := notleft_right h3 CnKnight
      have AKnight := stA.mpr (by constructor ; assumption ; constructor ; assumption ; assumption)
      exact disjoint h AKnight AKnave

example
  {inst2 : Fintype Inhabitant}
  {inst : DecidableEq Inhabitant}
  {Knight : Finset Inhabitant} {Knave : Finset Inhabitant}
{h : Knight ∩ Knave = ∅ }
{h1 : A ∈ Knight ∨ A ∈ Knave }
{h2: B ∈ Knight ∨ B ∈ Knave }
{h3: C ∈ Knight ∨ C ∈ Knave }
{AneB : A≠ B}
{BneC : B≠ C}
{AneC : A≠ C}
{all : ∀ (x : Inhabitant), x = A ∨ x = B ∨ x = C}
-- Knave = {A,B,C} ???
-- similar to previous problem
{stA : A ∈ Knight  ↔ (Knave= {A,B,C}) }
{stAn : A ∈ Knave ↔ ¬ (Knave = {A,B,C}) }
{stB : B ∈ Knight ↔ Knave = {A} ∨ Knave = {B} ∨ Knave = {C}}
  : A ∈ Knave ∧ C ∈ Knight := by
      
  -- same argument as prob 31
  -- try different approach, Knave={A,B,C} then A ∈ Knave . so we have the implication A ∈ Knight → A ∈ Knave
  have AKnave : A ∈ Knave := by
    by_contra AKnight
    rw [notinright_inleftIff h1 h] at AKnight
    have everyoneknave := stA.mp AKnight  
    have AKnave: A ∈ Knave := by rw [everyoneknave] ; apply Finset.mem_insert_self
    exact disjoint h AKnight AKnave
--   Suppose instead, A and B say the following: 
--A: All of us are knaves. 
--B: Exactly one of us is a knave. 
-- saying there is one knight among us has the effect that everyone else is a knave, sounds like a nice level
--Can it be determined what B is? Can it be determined what 
--C is? 
  cases h2
  · have oneknave := stB.mp h_1 
    -- knave already full so from oneknave and AKnave we can conclude Knave = {A}
    
    -- think about cardinality
    #check eq_singleton_card_one 
    #check Finset.card_eq_one
    -- make a theorem that with all and Knave={A} ∨ Knave={B} ∨ Knave={C} ↔ ∃ a:Inhabitant , Knave ={a}
    -- can be made into a theorem
    have : ∃a , Knave ={a} := by
      cases oneknave  
      use A
      cases h_2
      use B
      use C
    have exista := this
    rw [Finset.card_eq_one.symm] at this 
    -- card=1, already full?
    #check already_full

    have CKnight: C ∉ Knave := by 
      intro CKnave
      #check Finset.eq_singleton_iff_unique_mem
      have ⟨a,aKnave⟩:= exista 
      rw [Finset.eq_singleton_iff_unique_mem] at aKnave
      have Aa := aKnave.right A AKnave
      have Ca := aKnave.right C CKnave
      rw [←Ca] at Aa 
      contradiction
    rw [notinright_inleftIff h3 h] at CKnight
    exact And.intro AKnave CKnight
      --rw [Finset.eq_singleton_iff_unique_mem] at this 
    --rw [eq_singleton_card_one] at oneknave
    --#check not_eq_singleton_of_not_mem
    ---- could also do not_eq_singleton_of_not_mem
    --have : Knave ≠ {B} := by 
    --  intro BKnave 
    --  rw [Finset.eq_singleton_iff_unique_mem] at BKnave
    --  exact disjoint h h_1 BKnave.left
    --simp [this] at oneknave
  · 
    -- need full2 where A ∈ S, B ∈ S, S.card=2 , A ≠ B , B ≠ C, C ≠ A then C ∉ S. can be used here because of ¬Knave={A,B,C}
    #check full2
    -- card equal two part, well knave ≠ {A} etc.. and we have all, so knave.card is not equal to one. its not equal to 3 either because ¬Knave={A,B,C}. its bounded above by 3, so the only options left are 2 or 0... this is tedious
    -- another way for card equal two part, Knave.card ≤ 3 , not equal three so ≤ 2. has two elements in it i.e ≥ 2 so its two.
    -- make a general theorem where
    #check Finset.ssubset_iff
    #check Finset.ssubset_iff_subset_ne
    #check Finset.card_lt_card
    #check univ_iff_all

    #check Finset.card_insert_le
    have U: Finset.univ = {A, B, C} := univ_iff_all.mpr all 
    have knavesubU : Knave ⊆ {A,B,C} := by 
      rw [←U]
      apply Finset.subset_univ
    have knavenotall := stAn.mp AKnave
    have knavessub := Finset.ssubset_iff_subset_ne.mpr ⟨knavesubU,knavenotall⟩ 
    have knavecardlt3 :=  Finset.card_lt_card knavessub
    #check Nat.le_of_lt_succ
    have : 1≤2 := by norm_num
    unfold Nat.le at this
    #check Nat.lt_iff_le_pred
    simp at knavecardlt3
    have : ({A,B,C}: Finset Inhabitant).card=3 := by{
      rw [Finset.card_eq_three]
      use A
      use B
      use C
    }
    rw [this] at knavecardlt3

    have knavele2: Knave.card ≤ 2 := by 
      #check Nat.lt_iff_le_pred
      exact (Nat.lt_iff_le_pred three_pos).mp knavecardlt3
     
    have card_ge_2 :Knave.card ≥ 2 := by

      have ABsub: {A,B} ⊆ Knave := by
        intro x
        intro xAB
        #check mem2_iff_or_finset
        rw [mem2_iff_or_finset] at xAB
        cases xAB
        rw [h_2] 
        assumption
        rw [h_2] 
        assumption
      #check Finset.card_le_of_subset
      have : ({A,B}: Finset Inhabitant).card =2 := by 
        rw [Finset.card_eq_two]
        use A
        use B
      have conc := Finset.card_le_of_subset ABsub
      rw [this] at conc
      assumption
    #check Nat.le_antisymm
    #check full
    have : C ∉ Knave := @full2 Inhabitant _ _ _ Knave inst inst2 AKnave h_1 (Nat.le_antisymm knavele2 card_ge_2) AneB BneC AneC all
    
    --have : C ∉ Knave := full2 Knave AKnave h_1 (Nat.le_antisymm knavele2 card_ge_2) AneB BneC AneC all

    -- and done............
    rw [notinright_inleftIff h3 h] at this
    exact And.intro AKnave this 

Conclusion 
"
"

