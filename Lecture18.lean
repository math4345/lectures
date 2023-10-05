import Mathlib.Tactic

-- Math 4345: Lecture 18
--  _              _                    _  ___  
-- | |    ___  ___| |_ _   _ _ __ ___  / |( _ ) 
-- | |   / _ \/ __| __| | | | '__/ _ \ | |/ _ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|\___/ 
--                                              
-- 

#check { x : ℤ | x * x > 2 }

example : 3 ∈ {x : ℤ | x * x > 2} := by
  dsimp
  norm_num

example : 1 ∉ {x : ℤ | x * x > 2} := by
  dsimp
  norm_num

-- ⊆ amounts to a conditional statement
example : {x : ℤ | x * x > 3} ⊆ {x : ℤ | x * x > 2} := by
  intro y
  intro hy
  dsimp at *
  linarith

-- new tactic: ext
example : {x : ℤ | Odd x} = {x : ℤ | ∃ k, x = 2 * k + 1 } := by
  ext y
  constructor
  
  intro hy
  dsimp at *
  unfold Odd at hy
  assumption

  intro hy
  dsimp at *
  unfold Odd
  assumption

example (P : Prop) : P ↔ P := by rfl

example : {x : ℤ | Odd x} = {x : ℤ | ∃ k, x = 2 * k + 1 } := by rfl

lemma lemma1 : {x : ℝ | 1 < x ∧ x < 3} ∩ {x : ℝ | 0 < x ∧ x < 2} = 
  {x : ℝ | 1 < x ∧ x < 2} := by
  ext y
  norm_num
  constructor
  repeat
    intro h
    repeat constructor
    repeat linarith
    repeat constructor
    repeat linarith
  
#check (Set.Ioo 1 2 : Set ℝ)

example : (Set.Ioo 1 3 : Set ℝ) ∩ (Set.Ioo 0 2 : Set ℝ) = (Set.Ioo 1 2 : Set ℝ) := lemma1 

variable (z : ℝ)
#check z ∈ Set.Ioo 1 3
#check Set.Ioo 1 3

example : (Set.Ioo 1 3 : Set ℝ) ∪ (Set.Ioo 0 2 : Set ℝ) = (Set.Ioo 0 3 : Set ℝ) := by
  ext y
  norm_num
  constructor
  intro h
  constructor

  repeat 
    rcases h with h1|h2
    repeat linarith
  
  intro h
  by_cases h1 : 1 < y
  
  left
  constructor
  repeat linarith
  
  right
  constructor
  repeat linarith

section

#check (Set.univ : Set ℤ)

example : 3 ∈ (Set.univ : Set ℤ) := trivial

example : 3 ∈ { x : ℤ | True } := by
  trivial

-- an unnecessarily long proof
example (A : Set ℤ) : A ∩ Set.univ = A := by
  ext x -- "let x be an element..."
  constructor
  intro h
  rcases h with ⟨ h1, _ ⟩ 
  exact h1

  intro h
  constructor
  assumption
  trivial

example : True := trivial
example : True := by trivial

variable (A B C : Set ℤ)

example : A ∩ (B ∪ C) ⊆ A := by
  intro x
  rintro ⟨ h1, _ ⟩ 
  assumption

example : A ∩ (B ∪ C) ⊆ A := by
  intros x hx
  exact hx.left

example : A ∩ (B ∪ C) ⊆ A := fun _ hx => hx.left

example : A ∩ (B ∪ C) ⊆ A := fun _ ⟨h, _⟩ => h

end section

section

variable (α : Type)
variable (A B C : Set α)

example : (A ∩ B) ∩ C = A ∩ (B ∩ C) := Set.inter_assoc A B C

example : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  constructor

  rintro ⟨ ⟨ h1, h2 ⟩, h3 ⟩
  constructor
  assumption
  constructor
  assumption
  assumption

  sorry

end section

  