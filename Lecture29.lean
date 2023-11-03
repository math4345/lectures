import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Associated

-- Math 4345: Lecture 29
--  _              _                    ____   ___
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \ / _ \
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | (_) |
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ \__, |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|  /_/
--

-- 25 = 5 ^ 2
-- (factorization 25) 5 = 2
-- (factorization 25) 3 = 0
-- (factorization 25) 2 = 0
-- (factorization 25) 7 = 0

-- 105 = 5^1 * 3^1 * 7^1
-- (factorization 105) 5 = 1
-- (factorization 105) 2 = 0
-- (factorization 105) 7 = 1

#eval padicValNat 5 375
#eval padicValNat 2 192

example : (Nat.factorization 3) 3 = 1 :=
  Nat.Prime.factorization_self (by norm_num)

example (a : ℕ) (ha : Nat.Prime a) : (Nat.factorization a) a = 1 := by
  exact Nat.Prime.factorization_self ha

example (a : ℕ) (hp : Nat.Prime a) (h : a ∣ 4) : a = 2 := by
  have hz : 4 ≠ 0 := by norm_num
  let h' := Nat.mem_divisors.mpr ⟨ h, hz ⟩
  have h4 := Nat.divisors (2 ^ 2)
  rw [(by rfl : 4 = 2 ^ 2)] at h'
  have h2 : Nat.Prime 2 := by norm_num
  have h5 := (@Nat.mem_divisors_prime_pow 2 h2 2 a).mp h'
  rcases h5 with ⟨ j, x, h ⟩

  interval_cases j

  rw [h] at hp
  have hn : ¬ Nat.Prime 1 := Nat.not_prime_one
  exfalso
  exact hn hp

  assumption

  rw [h] at hp
  have hn : ¬ Nat.Prime 4 := of_decide_eq_false rfl
  exfalso
  exact hn hp

example (a : ℕ) (hp : Nat.Prime a) (h : a ∣ 4) : a = 2 := by
  have k := (Nat.factorization_le_iff_dvd
    (Nat.Prime.ne_zero hp)
    (by norm_num)).mpr h
  rw [Finsupp.le_def] at k
  simp at k
  rw [(by norm_num : 4 = 2 ^ 2)] at k
  specialize k a
  simp at k

  by_cases hc : (a ≠ 2)
  let h'' : (Finsupp.single 2 2) a = 0 := Finsupp.single_eq_of_ne hc.symm
  rw [h''] at k
  rw [Nat.Prime.factorization_self hp] at k
  linarith

  push_neg at hc
  assumption

---

example : ∀ (n : ℕ), ∃ (p : ℕ), (p ≥ n) ∧ (Nat.Prime p) := by
  intro n
  exact Nat.exists_infinite_primes n

---

example (a n : ℕ) (hp : Nat.Prime a) (h : a ∣ 2 ^ n) : a = 2 := by
  have k := (Nat.factorization_le_iff_dvd
    (by exact Nat.Prime.ne_zero hp)
    (by exact NeZero.ne (2 ^ n))).mpr h
  rw [Finsupp.le_def] at k
  simp at k
  specialize k a

  by_cases hc : (a ≠ 2)
  let h'' : (Finsupp.single 2 n) a = 0 := by
    apply Finsupp.single_eq_of_ne
    exact hc.symm
  rw [h''] at k

  rw [Nat.Prime.factorization_self] at k
  linarith
  exact hp

  push_neg at hc
  exact hc

---

#eval Int.gcdA 17 5 == -2
#eval Int.gcdB 17 5 == 7

#eval (17 * -2) + (5 * 7) == 1

lemma bezout (a b : ℤ) (h : gcd a b = 1) :
  ∃ (x y : ℤ), a * x + b * y = 1 := by
  use Int.gcdA a b
  use Int.gcdB a b
  rw [← Int.gcd_eq_gcd_ab a b]
  exact h

lemma euclid {a b c : ℤ} (h : gcd a b = 1) (hd : a ∣ (b * c)) :
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

lemma dvd_square (x : ℤ) (h : 3 ∣ x ^ 2) : 3 ∣ x := by
  exact Prime.dvd_of_dvd_pow (Int.prime_three) h

lemma dvd_square_p {p : ℤ} (hp : Prime p) (x : ℤ) (h : p ∣ x ^ 2) : p ∣ x := by
  exact Prime.dvd_of_dvd_pow hp h

lemma mul_cancel {a b c : ℤ} (hz : c ≠ 0) (h : c*a = c*b) : a = b := by
  have h' : c * a / c = c * b / c := by congr
  simp at h'
  rcases h' with h'|h'
  assumption
  exfalso
  exact hz h'

example (a b c : ℤ) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (gcd a b) := by
  exact dvd_gcd ha hb

-- suppose exists integers x, y so that x / y = sqrt(3)
-- then (x/y) * (x/y) = 3
-- x * x = 3 * y * y
lemma no_square_root {x y : ℤ} (h : 3 * y * y = x * x) : (gcd x y ≠ 1) := by
  have hx : 3 ∣ x * x := by
    use y * y
    rw [← h]
    ring
  rw [(by ring : x * x = x ^ 2)] at hx
  rcases (dvd_square x hx) with ⟨ z, hz ⟩
  rw [hz] at h
  have h' : 3 * (y ^ 2) = 3 * (3 * z^2) := by linarith
  have h'' := mul_cancel (by norm_num : (3 : ℤ) ≠ 0) h'
  have hy : 3 ∣ y^2 := by use z ^ 2
  have hy' := dvd_square y hy
  have : 3 ∣ gcd x y := dvd_gcd (⟨ z, hz ⟩ : 3 ∣ x) hy'
  rcases this with ⟨ d, hd ⟩

  intro ho
  rw [ho] at hd

  have h3 : 1 % 3 = 3 * d % 3 := by congr
  simp at h3

lemma no_square_root_p {x y p : ℤ} (hp : Prime p)
  (h : p * y * y = x * x) : (gcd x y ≠ 1) := by
  have hx : p ∣ x * x := by
    use y * y
    rw [← h]
    ring
  rw [(by ring : x * x = x ^ 2)] at hx
  rcases (Prime.dvd_of_dvd_pow hp hx) with ⟨ z, hz ⟩
  rw [hz] at h
  have h' : p * (y ^ 2) = p * (p * z^2) := by linarith
  have h'' := mul_cancel (Prime.ne_zero hp : p ≠ 0) h'
  have hy : p ∣ y^2 := by use z ^ 2
  have hy' := Prime.dvd_of_dvd_pow hp hy
  have : p ∣ gcd x y := dvd_gcd (⟨ z, hz ⟩ : p ∣ x) hy'
  rcases this with ⟨ d, hd ⟩

  intro ho
  rw [ho] at hd

  have h3 : 1 % p = p * d % p := by congr
  simp at h3
  sorry

example (P Q : Prop) (nq : ¬ Q) (h : P ∨ Q) : P := by
  rcases h with h|h
  exact h
  exfalso
  exact nq h

example : ¬ ∃ (r : ℚ), r * r = (3 : ℚ) := by
  intro h
  rcases h with ⟨ r, h ⟩
  let a := r.num
  let b := r.den
  -- r.reduced
  have hab : r = r.num / r.den := (Rat.num_div_den r).symm
  rw [hab] at h
  ring_nf at h
  simp at h
  have h' : ↑r.num ^ 2 = 3 * (↑r.den ^ 2) := by
    linarith
  have hs := no_square_root h'

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




example (a : ℕ) (hp : Nat.Prime a) (h : a ∣ 2 ^ n) : a = 2 := by
  let fa := factorization a
  let f2 := factorization (2 ^ n)
  have a0 : a ≠ 0 := by sorry
  have t0 : 2 ^ n ≠ 0 := by exact NeZero.ne (2 ^ n)
  have k := (Nat.factorization_le_iff_dvd a0 t0).mpr h
  simp at k
  rw [Finsupp.le_def] at k

  specialize k a

  simp at k


  rw [Finsupp.single_eq_of_ne hc] at k



  sorry


  push_neg at hc
  assumption
  -- Nat.dvd_of_factorization_pos f2

theorem Nat.{d : ℕ} {n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
Nat.factorization d ≤ Nat.factorization n ↔ d ∣ n

-- From Mathematics in Lean:


def same_sign (a b : ℤ) : Prop := Int.sign a = Int.sign b

example : same_sign 3 4 := by
  unfold same_sign
  norm_num

example : ¬ same_sign 3 (-3) := by
  unfold same_sign
  norm_num

#check (Setoid.ker same_sign).iseqv.symm

example : same_parity 3 5 := by
  use -1
  norm_num

example : same_parity 2 10 := by
  use -4
  norm_num

example : ¬ same_parity 5 2 := by
  unfold same_parity
  push_neg
  intro k
  intro h
  have not_even : ¬ Even (3 : ℤ) := Int.not_even_iff.mpr rfl
  have even : Even (3 : ℤ) := by
    use k
    linarith
  contradiction


theorem parity_refl : Reflexive same_parity :=
  fun _ => ⟨ 0, by ring ⟩

theorem parity_symm : Symmetric same_parity :=
  fun _ _ ⟨ k, _ ⟩ => ⟨ -k, by linarith ⟩

theorem parity_trans : Transitive same_parity :=
  fun _ _ _ ⟨ kxy, _ ⟩ ⟨ kyz, _ ⟩ => ⟨ kxy + kyz, by linarith ⟩

--
