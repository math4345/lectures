import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt

-- Math 4345: Lecture 19
--  _              _                    _  ___  
-- | |    ___  ___| |_ _   _ _ __ ___  / |/ _ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | (_) |
-- | |__|  __/ (__| |_| |_| | | |  __/ | |\__, |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|  /_/ 
--                                              
-- 

example : ¬ (∃ x : ℤ, x ∈ ∅) := by
  
variable (α : Type)
variable (A B C : Set α)

example : A ⊆ B := by
  rw [Set.subset_def]
  sorry

example : { x : ℤ | Even (x * x) } ⊆ { x : ℤ | Even x } := by
  rw [Set.subset_def]
  simp [Set.mem_setOf] -- why simp?
  sorry

example : (A ∩ B) ∪ A = A := by
  sorry

example : (A ∪ B) ∩ A = A := by
  sorry

def f (x : ℕ) : ℕ := x * x

#eval f 3

#check (f '' (Set.univ : Set ℕ))

example : (f '' (Set.univ : Set ℕ)) = { x : ℕ | ∃ y, y * y = x } := by
  unfold f
  ext x
  rw [Set.mem_setOf]
  simp -- wow!

-- Indexed families
example : ⋃ (n : ℕ), { x : ℕ | x < n } = (Set.univ : Set ℕ) := by
  ext n
  rw [Set.mem_iUnion]
  simp [Set.mem_setOf]
  use n + 1
  exact Nat.lt.base n  

example : ⋂ (r > 0), (Set.Ioo (-r) r : Set ℝ) = Set.singleton 0 := by
  ext x
  simp
  constructor
  
  intro h
  apply Set.mem_singleton_iff.mpr

  by_cases k : x > 0 
  specialize h (x / 2) (by linarith)
  exfalso
  linarith

  by_cases k' : x < 0
  specialize h (-x / 2) (by linarith)
  exfalso
  linarith
  
  linarith

  intro h
  have h := Set.mem_singleton_iff.mp h
  intro i
  intro hi
  constructor

  linarith
  linarith  

-- the square root of two is not rational
lemma sqrt2 : { x : ℚ | x ≥ 0 ∧ x * x = 2 } = ∅ := by
  ext x
  rw [Set.mem_setOf]
  simp
  intro h
  intro h5
  have hpos : 0 ≤ (x : ℝ)
  norm_cast
  have h' : (0 : ℝ) ≤ 2 := by linarith
  have h1 := (Real.sqrt_eq_iff_sq_eq h' hpos).mpr
  have h2 : (x : ℝ)^2 = 2
  ring_nf at h5
  norm_cast
  rw [h5]
  norm_num    

  have h3 : Real.sqrt 2 = (x : ℝ) := h1 h2
  have h4 := irrational_sqrt_two   
  unfold Irrational at h4
  apply h4
  simp [Set.mem_setOf]
  use x
  simp [h3]
  
lemma sqrt2' : { x : ℚ | x * x = 2 } = ∅ := by
  ext x
  rw [Set.mem_setOf]
  by_cases x ≥ 0

  have s := sqrt2
  have s' := Set.eq_empty_iff_forall_not_mem.mp s
  specialize s' x
  rw [Set.mem_setOf] at s'
  push_neg at s'
  specialize s' h
  constructor

  intro h
  exact s' h

  tauto

  have s := sqrt2
  have s' := Set.eq_empty_iff_forall_not_mem.mp s
  specialize s' (-x)
  rw [Set.mem_setOf] at s'
  push_neg at s'
  specialize s' (by linarith)
  constructor
  ring_nf at s'
  intro h
  ring_nf at h
  exact s' h

  tauto
    
