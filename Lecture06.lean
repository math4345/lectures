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

-- what does " ∣ " mean ?  I typed that in using \mid.

example : (-2 : ℤ) ∣ 6 := by
  -- this means ∃ k, -2 * k = 6
  use -3
  norm_num

example : ¬ (5 ∣ 4) := by sorry

example : 4 ≠ 5 := by norm_num

example : ¬ (4 = 5) := by
  norm_num

example : (0 = 1) → False := by 
  exact Nat.zero_ne_one

#check Nat.succ_injective

-- recall what "injective" means
-- for inputs x, y, if x ≠ y, then f(x) ≠ f(y)
-- if f(x) = f(y), then x = y.

-- what Nat.succ_injectie proves is that
-- if succ x = succ y, then x = y.

example : 1 ≠ 2 := by norm_num

example : 1 ≠ 2 := by
 -- 1 ≠ 2 means ¬ (1 = 2) whcih means (1 = 2) → False 
  intro h
  have h' : 0 = 1
  exact Nat.succ_injective h 
  exact Nat.zero_ne_one h'

def five : ℤ := 5
def four : ℤ := 4

example : ¬ (five ∣ four) := by
  intro h
  have h' : five ≤ four := Int.le_of_dvd (by norm_num) h
  norm_num at h'

example : ¬(3 : ℤ) ∣ 1 := by
  intro h
  have h' : (3 : ℤ) ≤ 1
  apply Int.le_of_dvd
  norm_num
  exact h
  norm_num at h'

example (n : ℤ) : (3 ∣ n) → (9 ∣ n * n) := by
  rintro ⟨ k, h' ⟩
  -- 9 ∣ n^2 means ∃ k' such that 9 * k' = n^2
  -- I already know that n = 3k, so n^2 = 3k * 3k 
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
