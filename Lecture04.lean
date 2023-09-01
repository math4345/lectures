import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

-- Math 4345: Lecture 4
--  _              _                     ___  _  _   
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \| || |  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | || |_ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |__   _|
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/   |_|  
--                                                   

  -- New tactics:
  --   - use
  --   - rcases
  --   - rintro
  --   - intros
  --   - right
  --   - left
  --   - induction'
  --   - apply
  --   - exact

-- def Even (n : ℕ) : Prop := ∃ k, n = k + k
-- def Odd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

example : Odd 17 := by
  use 8
  norm_num

#check 12
#check (12 : ℤ)
#check (12 : ℕ)

example : Even 20 := by
  use 10

example : Odd 5 := by
  use 2
  norm_num

-- If n is odd, then n + 1 is even.
lemma odd_then_even : Odd (n : ℕ) → Even (n + 1) := by
  --intro h
  --rcases h with ⟨ k, p ⟩
  rintro ⟨ k, p ⟩
  use k + 1
  rw [p]
  ring

lemma even_then_odd : Even (n : ℕ) → Odd (n + 1) := by
  intro h
  rcases h with ⟨ k, p ⟩
  use k
  rw [p]
  ring

example (h : Even (n : ℕ)) : Even (n * n) := 
  Even.mul_left h n

-- If n is even, then n^2 is even.
example : Even (n : ℕ) → Even (n * n) := by
  intro h
  rcases h with ⟨ k, p ⟩
  -- n = k + k
  -- n^2 = 4 k^2 = 2 * (2k^2)
  use 2*k*k -- this is where the proof really happens!
  rw [p]
  ring

-- If n is even and m is even then n + m is even.
-- If n is even, then if m is even, then n + m is even.
example : Even (n : ℕ) → Even (m : ℕ) → Even (n + m) := by
  intros hn hm
  rcases hn with ⟨ kn, pn ⟩ -- n = kn + kn
  rcases hm with ⟨ km, pm ⟩ -- m = km + km
  use kn + km              -- n + m = (kn + kn) + (km + km)
  rw [pn, pm]
  ring

example : Even (n : ℕ) → Odd (m : ℕ) → Odd (n + m) := by
  sorry

example : Odd (n : ℕ) → Odd (m : ℕ) → Even (n + m) := by
  sorry

open Nat

-- ∧ ∨ are and "∧ND" or, respectively

example : (Even 17) ∨ (Odd 17) := by
  right
  use 8
  norm_num

example : (Even 16) ∨ (Odd 16) := by
  left
  use 8

theorem even_or_odd (n : ℕ) : (Even n) ∨ (Odd n) := by
  induction' n with n ih
  left
  use zero
  rcases ih with h | h
  right
  apply even_then_odd
  exact h
  left
  apply odd_then_even
  exact h

