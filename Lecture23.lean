import Mathlib.Tactic
open Function -- for injective and surjective
open Set

-- Math 4345: Lecture 23
--  _              _                    ____  _____ 
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \|___ / 
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | |_ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ ___) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|____/ 
--                                                  
-- 

lemma subset_image_preimage' (r : Set β) (h : Surjective f) : r ⊆ f '' (f ⁻¹' r) := by
  intros x h'
  simp only [mem_image, mem_preimage]
  rcases h x with ⟨ a, ha ⟩  
  use a  
  rw [ha]
  tauto

lemma subset_preimage_image' (r : Set β) (h : Surjective f) : f '' (f ⁻¹' r) ⊆ r := by
  intros x h'
  simp only [mem_image, mem_preimage] at h'
  rcases h' with ⟨ a, h1, h2 ⟩  
  dsimp [Surjective] at h
  rw [← h2]
  assumption

example (r : Set β) (h : Surjective f) : f '' (f ⁻¹' r) = r := image_preimage_eq r h

example (r : Set β) (h : Surjective f) : f '' (f ⁻¹' r) = r := by
  ext x
  constructor
  apply subset_preimage_image'
  exact h
  apply subset_image_preimage'
  exact h

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

---