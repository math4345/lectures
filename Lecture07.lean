import Mathlib.Tactic

-- Math 4345: Lecture 7
--  _              _                     ___ _____ 
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \___  |
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | / / 
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |/ /  
-- |_____\___|\___|\__|\__,_|_|  \___|  \___//_/   
--                                                 
-- 

-- tactic: dsimp
-- another new tactic: change

lemma two_not_dvd_one : ¬ ((2 : ℤ) ∣ 1) := by
  intro h
  have h' : (2 : ℤ) ≤ 1
  apply Int.le_of_dvd
  norm_num
  exact h
  norm_num at h'

example : ¬ ((2 : ℤ) ∣ 3) := by
  rintro ⟨ d, h ⟩
  have k : (2 : ℤ) ∣ 1
  use d - 1
  linarith
  exact two_not_dvd_one k

example : ¬ ((2 : ℤ) ∣ 9) := by
  rintro ⟨ d, h ⟩
  have k : (2 : ℤ) ∣ 1
  use d - 4
  linarith
  exact two_not_dvd_one k

example : ¬ (Even 9) := by sorry

example : (3 : ℤ) ∣ 12 := by
  dsimp [(· ∣ ·)]
  use 4
  norm_num
  
-- NNBZO means "no natural number between zero and one"
lemma nnbzo : ¬ ∃ (a : ℕ), a > 0 ∧ a < 1 := by
  rintro ⟨ n, h1, h2 ⟩
  exact Nat.le_lt_antisymm h1 h2

variable (a b c : ℤ)

example (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨ kab, hab ⟩
  rcases hbc with ⟨ kbc, hbc ⟩
  dsimp [(· ∣ ·)]
  rw [hbc]
  rw [hab]
  use kab * kbc
  rw [mul_assoc]

example (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  exact dvd_trans hab hbc

example : a ∣ 0 := by
  use 0
  norm_num

example : a ∣ 0 := by
  exact Int.dvd_zero a

example (h : a * b ∣ c) : a ∣ c := by
  change ∃ n, c = a * n 
  rcases h with ⟨ k, h ⟩
  use b * k
  rw [← mul_assoc]
  exact h

example (h : a * b ∣ c) : a ∣ c := by
  exact dvd_of_mul_right_dvd h

variable (n : ℕ)

lemma two_divides_n_or_succ_n : (2 ∣ n) ∨ (2 ∣ n + 1) := by
  have h := Nat.even_or_odd n
  rcases h with h|h
  left
  dsimp [Even] at h
  rcases h with ⟨ r, h ⟩
  rw [h]
  use r
  ring
  right
  dsimp [Odd] at h
  rcases h with ⟨ k, h ⟩
  rw [h]
  use k + 1
  ring

lemma two_divides_it : 2 ∣ n * (n+1) := by
  rcases two_divides_n_or_succ_n n with h|h
  have h1 : 2 ∣ (n+1) * n
  apply dvd_mul_of_dvd_right
  exact h
  have : (n+1) * n = n * (n+1) := by ring
  rw [this] at h1
  exact h1

  have : 2 ∣ n * (n+1)
  apply dvd_mul_of_dvd_right
  exact h
  exact this

lemma choose_3 : (n) * (n+1) * (n+2) = 6 * ((n + 2).choose 3) := by
  have : (n+2).descFactorial 3 = (Nat.factorial 3) * ((n+2).choose 3)
  exact Nat.descFactorial_eq_factorial_mul_choose (n + 2) 3
  norm_num at this
  ring_nf at this
  ring_nf
  exact this

lemma three_divides_it : 3 ∣ n * (n+1) * (n+2) := by
  have h := choose_3 n
  use 2 * Nat.choose (n+2) 3
  rw [h]
  ring

lemma two_and_three_divide {n : ℕ} (h2 : 2 ∣ n) (h3 : 3 ∣ n) : (2 * 3 ∣ n) := by
  apply Nat.Prime.dvd_mul_of_dvd_ne
  norm_num
  norm_num
  norm_num
  exact h2
  exact h3

theorem six_divides_it : 6 ∣ n * (n+1) * (n+2) := by
  apply two_and_three_divide
  have h : 2 ∣ (n+2) * (n * (n+1))
  apply dvd_mul_of_dvd_right
  exact two_divides_it n
  have h2 : n * (n+1) * (n+2) = (n+2) * (n * (n+1)) := by ring
  rw [h2]
  exact h    
  exact three_divides_it n
