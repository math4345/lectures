import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt

-- Math 4345: Lecture 21
--  _              _                    ____  _ 
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \/ |
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | |
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/| |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|_|
--                                              

section

variable (α : Type)
variable (A B C : Set α)

#check True
#check trivial
example : True := trivial

variable (x : α)
#check (x ∈ Set.univ)

example (x : α) : x ∈ Set.univ := by trivial
example (x : α) : x ∈ Set.univ := by simp only [Set.mem_univ]
example (x : α) : x ∈ Set.univ := trivial

example : (∅ : Set α)ᶜ = Set.univ := by simp

example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by exact Set.compl_union A B
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, imp_self]  

example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by simp

example : 𝒫 (∅ : Set α) = { ∅ } := by
  exact Set.powerset_empty

end section

-- last time we discussed direct image f ''
-- there is also a preimage operation

def f (x : ℕ) : ℕ := x * x

#eval f 2 

#check ({ 2 } : Set ℕ)

#check f ⁻¹' { 2 }

-- the preimage of the singleton { 4 } is { 2 }
example : f ⁻¹' { 4 } = { 2 } := by
  unfold f
  sorry

example : Set.singleton 0 = { 0 } := by rfl

example : ⋃ (n : ℕ), { x : ℕ | x < n } = (Set.univ : Set ℕ) := by
  ext m
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  use m + 1
  exact Nat.lt.base m

example : ⋂ (n : ℕ), { x : ℕ | x > n } = (∅ : Set ℕ) := by
  ext m
  rw [Set.mem_empty_iff_false]
  simp only [iff_false]
  rw [Set.mem_iInter]
  simp only [Set.mem_setOf]
  push_neg
  use m

example : ⋂ (n : ℕ), { x : ℕ | x > n } = (∅ : Set ℕ) := by
  ext m
  simp -- should be simp only since I'm not closing a goal
  use m

-- intersect (-r,r) for all reals r > 0,
-- and you get { 0 }.
example : ⋂ (r > 0), (Set.Ioo (-r) r : Set ℝ) = Set.singleton 0 := by
  ext x
  simp
  constructor
  
  intro h
  apply Set.mem_singleton_iff.mpr

  by_cases k : x > 0 
  specialize h (x / 2) (by linarith)
  linarith

  by_cases k' : x < 0
  specialize h (-x / 2) (by linarith)
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
    
