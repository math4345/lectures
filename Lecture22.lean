import Mathlib.Tactic
open Function -- for injective and surjective
open Set

-- Math 4345: Lecture 22
--  _              _                    ____  ____  
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \|___ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | __) |
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ / __/ 
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|_____|
--                                                  
-- 

variable {α β : Type*}
variable (f : α → β)
variable (u v : Set α)

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

def square : ℤ → ℤ := fun x => x * x

example : ∃ (γ : Type) (g : γ → γ) (A : Set γ), ¬ (g ⁻¹' (g '' A) ⊆ A) := by
  use ℤ
  use square
  use Set.singleton 1
   
  have h' : square '' Set.singleton 1 = Set.singleton 1
  exact Iff.mp Set.toFinset_inj rfl
  rw [h']
  push_neg
  
  rw [Set.subset_def]
  simp
  use -1
  
  constructor

  unfold square
  simp
  exact rfl
  
  tauto
