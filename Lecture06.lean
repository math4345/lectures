import Mathlib.Tactic
import Mathlib.Data.Nat.Prime

-- Math 4345: Lecture 6
--  _              _                     ___   __   
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \ / /_  
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | '_ \ 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/ \___/ 
--                                                  

-- The theme for this short week is "divisiblity"

-- what does " ∣ " mean ?

example : (-2 : ℤ) ∣ 6 := by
  use -3
  norm_num

example : ¬ (5 ∣ 4) := by sorry

example : 4 ≠ 5 := by
  norm_num

example : 0 ≠ 1 := by 
  exact Nat.zero_ne_one

#check Nat.succ_injective

example : 1 ≠ 2 := by
  intro h
  have : 0 = 1
  exact Nat.succ_injective h 
  exact Nat.zero_ne_one this

def five : ℤ := 5
def four : ℤ := 4

example : ¬ (five ∣ four) := by
  intro h
  have : five ≤ four
  apply Int.le_of_dvd
  norm_num
  exact h 
  norm_num at this

example : ¬(3 : ℤ) ∣ 1 := by
  intro h
  have h' : (3 : ℤ) ≤ 1
  apply Int.le_of_dvd
  norm_num
  exact h
  norm_num at h'

lemma nibzo : ¬ ∃ (a : ℤ), a > 0 ∧ a < 1 := by
  rintro ⟨ n, h1, h2 ⟩
  have h3 : n ≥ 1 := by linarith
  linarith

example (n : ℤ) : (3 ∣ n) → (9 ∣ n * n) := by
  intro h
  rcases h with ⟨ k, h' ⟩
  use k * k
  rw [h']
  ring

example (n : ℕ) : (2 ∣ n) → (3 ∣ n) → (2 * 3 ∣ n) := by
  intro h2
  intro h3
  apply Nat.Prime.dvd_mul_of_dvd_ne
  norm_num
  norm_num
  norm_num
  exact h2
  exact h3
