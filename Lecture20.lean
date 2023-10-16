import Mathlib.Tactic

-- Math 4345: Lecture 20
--  _              _                    ____   ___  
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \ / _ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | | | |
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/| |_| |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|\___/ 
--                                                  
-- 

-- This week is Ohio State's Fall Break,
-- which means no homework, or
-- a chance to catch up.

example : ¬ (∃ x, x ∈ (∅ : Set ℤ)) := by simp

variable (α : Type)
variable (A B C : Set α)

example : (A ⊆ B) = ∀ (x : α), x ∈ A → x ∈ B := Set.subset_def

#check Set.mem_setOf

example : { x : ℤ | ∃ y, Even y ∧ (y * y = x) } ⊆ { x : ℤ | Even x } := by
  rw [Set.subset_def]
  simp [Set.mem_setOf] -- why simp?  works under binder ∀
  intro a
  simp [Even]
  intro x
  intro h
  use x*a
  rw [h]
  ring

lemma inter_union' : (A ∩ B) ∪ A = A := by
  ext x
  constructor
  
  intro h
  rw [Set.inter_def] at h
  rw [Set.union_def] at h
  rw [Set.mem_setOf] at h
  
  rcases h with hp|hq
  
  rw [Set.mem_setOf] at hp
  exact hp.left

  exact hq

  intro h
  
  rw [Set.union_def]
  rw [Set.mem_setOf]

  right -- or I could use `exact Or.inr h`
  exact h

lemma inter_union : (A ∩ B) ∪ A = A := by
  simp

#print inter_union'

#print inter_union

example : (A ∪ B) ∩ A = A := Set.union_inter_cancel_left

def f (x : ℕ) : ℕ := x * x

def g : ℕ → ℕ := fun (x : ℕ) => x * x

#eval f 12

#check (f '' (Set.univ : Set ℕ)) -- this is "f(ℕ)", the image of f

#check (f '' { x : ℕ | x < 10}) -- this is "f({0,...,9})"

lemma squares : (f '' (Set.univ : Set ℕ)) = { x : ℕ | ∃ y, y * y = x } := by
  unfold f
  ext z
  rw [Set.mem_setOf]
  simp -- wow!

example : (f '' (∅ : Set ℕ)) = ∅ := by simp

example : (f '' { 2 }) = { 4 } := by simp

def less_than (n : ℕ) : Set ℕ := { x : ℕ | x < n }

@[simp]
def less_than_def (n : ℕ) : less_than n = { x : ℕ | x < n } := by rfl

example : less_than 0 = ∅ := by 
  unfold less_than
  simp

example : less_than 0 = ∅ := by simp

-- Indexed families
example : ⋃ (n : ℕ), less_than n = (Set.univ : Set ℕ) := by
  sorry

example : ⋃ (n : ℕ), { x : ℕ | x < n } = (Set.univ : Set ℕ) := by
  ext m
  rw [Set.mem_iUnion]
  simp [Set.mem_setOf]
  use m + 1
  exact Nat.lt.base m

example : Set.singleton 0 = { 0 } := by rfl
