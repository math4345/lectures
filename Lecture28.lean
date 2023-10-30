import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

-- Math 4345: Lecture 28
--  _              _                    ____  ___
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \( _ )
-- | |   / _ \/ __| __| | | | '__/ _ \   __) / _ \
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____\___/
--

def Coprime (m n : Nat) : Prop := gcd m n = 1

example (m n : ℕ) (h : Coprime m n) : m.gcd n = 1 := h

example : Nat.Prime 17 := by norm_num

lemma euclid (a b c : ℤ) (h : Int.gcd a b = 1) (hd : a ∣ (b * c)) : a ∣ c := by
  let x := Int.gcdA a b
  have hx : Int.gcdA a b = x := by rfl
  let y := Int.gcdB a b
  have hy : Int.gcdB a b = y := by rfl
  have h' := Int.gcd_eq_gcd_ab a b
  rw [h, hx, hy] at h'
  have hc : c * (↑1) = c * (a * x + b * y)
  congr
  simp at hc
  rcases hd with ⟨ d, hd ⟩
  ring_nf at hc
  have hd' : c * b = a * d := by linarith
  rw [hd'] at hc
  rw [hx, hy] at hc
  use (c*x + d*y)
  linarith

-- From Mathematics in Lean:
lemma two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

theorem exists_prime_factor {n : ℕ} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ (p ∣ n) := by
  by_cases np : n.Prime
  use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨ m, mltn, mdvdn, mne1 ⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  use m, mp
  rcases ih m mltn mgt2 mp with ⟨ p, pp, pdvd ⟩
  use p, pp
  apply pdvd.trans mdvdn
