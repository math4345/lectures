import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

-- Math 4345: Lecture 28
--  _              _                   ____  ___
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \( _ )
-- | |   / _ \/ __| __| | | | '__/ _ \   __) / _ \
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____\___/
--

-- This week's theme is Number Theory!
-- meaning facts about the integers (and natural numbers)

def Coprime (m n : Nat) : Prop := gcd m n = 1

example : gcd 3 2 = 1 := by norm_num

example : Coprime 3 2 := by
  unfold Coprime
  norm_num

example : Nat.Prime 17 := by norm_num

example : Nat.Prime 2 := by norm_num

-- "Bezout"
#check Int.gcd_eq_gcd_ab 5 7

#eval Int.gcdA 5 7
#eval Int.gcdB 5 7
#eval 3 * 5 + (-2) * 7 == 1

example : ∃ (x y : ℤ), 5 * x + 7 * y = 1 := by
  use Int.gcdA 5 7
  use Int.gcdB 5 7
  rw [← Int.gcd_eq_gcd_ab 5 7]
  norm_num

lemma bezout (a b : ℤ) (h : gcd a b = 1) :
  ∃ (x y : ℤ), a * x + b * y = 1 := by
  use Int.gcdA a b
  use Int.gcdB a b
  rw [← Int.gcd_eq_gcd_ab a b]
  exact h

lemma euclid (a b c : ℤ) (h : gcd a b = 1) (hd : a ∣ (b * c)) :
  a ∣ c := by
  have k := bezout a b h
  clear h

  rcases k with ⟨ x, y, k ⟩
  rcases hd with ⟨ d, hd ⟩

  have k' : c * (a * x + b * y) = c * 1
  congr
  ring_nf at k'
  rw [mul_comm] at hd
  rw [hd] at k'

  rw [(by ring : c * a * x + a * d * y = a * (c * x + d * y))] at k'
  use c*x + d*y
  exact k'.symm

lemma euclid' (a b c : ℕ) (h : gcd a b = 1) (hd : a ∣ (b * c)) :
  a ∣ c := by
  induction' a using Nat.strong_induction_on with a ih

  by_cases heq : a = b
  rw [← heq] at h
  simp at h
  rw [h]
  norm_num

  by_cases heq : a < b
  specialize ih (b - a)
  sorry
