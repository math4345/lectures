import Mathlib.Tactic

-- Math 4345: Lecture 30
--  _              _                    _____  ___
-- | |    ___  ___| |_ _   _ _ __ ___  |___ / / _ \
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \| | | |
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) | |_| |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/ \___/
--

-- More number theory

lemma dvd_square (x : ℤ) (h : 3 ∣ x ^ 2) : 3 ∣ x := by
  exact Prime.dvd_of_dvd_pow (Int.prime_three) h

lemma mul_cancel {a b c : ℤ} (hz : c ≠ 0) (h : c*a = c*b) : a = b := by
  have h' : c * a / c = c * b / c := by congr
  simp at h'
  rcases h' with h'|h'
  assumption
  exfalso
  exact hz h'

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

lemma mul_z {a b : ℚ} (hb : b ≠ 0) (h : a * (b)⁻¹ = 3) : (a = 3 * b) := by
  have h' : a * (b)⁻¹ * b = 3 * b := by congr
  ring_nf at h'
  exact (div_eq_iff hb).mp h

example (a : ℤ) : @Int.cast ℝ _ ( a + a ) = (a : ℝ) + a := by
  push_cast
  rfl

example (a : ℤ) : (((1 + a) * (1 + a)) : ℝ) = (1 + (a : ℝ)) ^ 2 := by
  sorry

example (a : ℝ) (h : 5 + a ^ 2 > 5) : a ≠ 0 := by
  have k : a ^ 2 > 0 := pos_of_lt_add_right h
  exact (sq_pos_iff a).mp k

example (a : ℝ) (h : a ^ 2 - 1 = 0) : a = 1 := by
  polyrith

example (a : ℝ) (h : 5 + a ^ 2 > 5) : a ≠ 0 :=
  (sq_pos_iff a).mp $ pos_of_lt_add_right h

example (a : ℕ) (b : ℤ) (h : (b : ℚ) = (a : ℤ)) : a = b := by
  push_cast at h
  norm_cast at h
  exact h.symm

-- sqrt 3 is irrational
example : ¬ ∃ (r : ℚ), r * r = 3 := by
  intro h
  rcases h with ⟨ r, h ⟩

  have hab : r = r.num / r.den := (Rat.num_div_den r).symm
  rw [hab] at h
  ring_nf at h
  simp at h
  have h' := mul_z ?hb h
  have h2 : (r.num : ℚ) * (r.num : ℚ) = 3 * r.den * r.den
  ring_nf
  ring_nf at h'
  rw [← h']
  have h3 : (r.num : ℤ) * (r.num : ℤ) = 3 * (r.den : ℤ) * (r.den : ℤ)
  norm_cast
  norm_cast at h2
  ring_nf at h2
  clear h2
  clear h'
  clear h
  clear hab

  have h'' := no_square_root h3.symm

  have k := r.reduced
  have k' : Nat.gcd (Int.natAbs r.num) r.den ≠ 1
  zify
  tauto
  exact k' k

  norm_cast
  intro hz'
  have hz'' : r.den = 0 := sq_eq_zero_iff.mp hz'
  exact (r.den_nz) hz''

--

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  induction m with
  | zero => tauto
  | succ m => induction m with
    | zero => tauto
    | succ m => exact Nat.AtLeastTwo.prop

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) :
  ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  . rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn



example (a : ℕ) (h : a ∣ 1) : (a = 1) := by
  exact Iff.mp Nat.dvd_one h

-- for any natural number, there is a prime larger than that number
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n

  -- there is a prime p dividing (n+1)! + 1 which is bigger than n
  have : 2 ≤ Nat.factorial (n + 1) + 1 :=
    Nat.le_add_of_sub_le (Nat.factorial_pos (n + 1))
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine' ⟨p, _, pp⟩

  by_contra ple
  push_neg  at ple

  have : p ∣ Nat.factorial (n + 1) :=
    Nat.dvd_factorial (Nat.Prime.pos pp) (by linarith)

  have : p ∣ 1 := (Nat.dvd_add_right this).mp pdvd

  rw [Nat.dvd_one.mp this] at pp
  exact Nat.not_prime_one pp

-- There are some extensions available...
-- prove that there are infinitely many primes of the form 3 mod 4
