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
variable (s t : Set α)
variable (u v : Set α)

-- In "mathematics" if A were a subset of the domain of f,
-- we would write f(A) for the direct image, meaning
-- f(A) := { y ∈ codom f | ∃ x ∈ A, f(x) = y }

#check f s -- lean is angry because s is not an α 

example (h : s ⊆ t) : f '' s ⊆ f '' t := image_subset f h

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intros x h'  
  simp -- I am :sad: to be using `simp` instead of `simp?`
  simp at h'
  -- since the goal is ∃ something, we want to `use` something
  dsimp [Set.subset_def] at h
    
  rcases h' with ⟨ x1, h1, h2 ⟩ 
  specialize h x1
  use x1
  -- `tauto` would close the goal
  -- or by hand: `exact ⟨ h h1, h2 ⟩`
  exact ⟨ h (by assumption), by assumption ⟩ 

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intros x 
  simp only [mem_image]
  tauto -- also works!

-- in "mathematics",
-- B is a subset of codom f,
-- recall f⁻¹(B) := { x ∈ dom f | f(x) ∈ B }

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intros x h'
  simp only [mem_preimage, mem_image] at h' 
  rcases h' with ⟨ _, h1, h2 ⟩
  rw [h h2] at h1
  assumption


