import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

-- Math 4345: Lecture 4
--  _              _                     ___  _  _   
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \| || |  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | || |_ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |__   _|
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/   |_|  
--                                                   

-- def Even (n : ℕ) : Prop := ∃ k, n = 2 * k
-- def Odd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

example : Odd (17 : ℕ) := by
  use 8
  norm_num

lemma odd_then_even : Odd (n : ℕ) → Even (n + 1) := by
  intro h
  rcases h with ⟨ k, p ⟩
  use k + 1
  rw [p]
  ring

lemma even_then_odd : Even (n : ℕ) → Odd (n + 1) := by
  intro h
  rcases h with ⟨ k, p ⟩
  use k
  rw [p]
  ring

example : Even (n : ℕ) → Even (m : ℕ) → Even (n + m) := by
  intro hn
  intro hm
  rcases hn with ⟨ kn, pn ⟩
  rcases hm with ⟨ km, pm ⟩ -- or rintro ?
  use kn + km
  rw [pn, pm]
  ring

example : Even (n : ℕ) → Odd (m : ℕ) → Odd (n + m) := by
  sorry

example : Odd (n : ℕ) → Odd (m : ℕ) → Even (n + m) := by
  sorry

open Nat

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
  