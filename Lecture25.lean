import Mathlib.Tactic

-- Math 4345: Lecture 25
--  _              _                    ____  ____
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \| ___|
-- | |   / _ \/ __| __| | | | '__/ _ \   __) |___ \
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ ___) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|____/
--

-- a "relation" is a proposition that depends on two inputs
def same_parity (a b : ℤ) : Prop := ∃ (k : ℤ), a - b = 2 * k

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

-- "having the same parity" is an equivalence relation

-- an equivalence relation is a relation which is...
-- reflexive   x ∼ x
-- symmetric   x ∼ y → y ∼ x
-- transitive  x ∼ y ∧ y ∼ z → x ∼ z

theorem parity_refl : Reflexive same_parity :=
  fun _ => ⟨ 0, by ring ⟩

theorem parity_symm : Symmetric same_parity :=
  fun _ _ ⟨ k, _ ⟩ => ⟨ -k, by linarith ⟩

theorem parity_trans : Transitive same_parity :=
  fun _ _ _ ⟨ kxy, _ ⟩ ⟨ kyz, _ ⟩ => ⟨ kxy + kyz, by linarith ⟩

--

def same_sign (a b : ℤ) : Prop := ((a = 0) ∧ (b = 0)) ∨ (a * b > 0)

example : same_sign 3 2 := Or.inr (by norm_num)

example : same_sign 0 0 := Or.inl ⟨ rfl, rfl ⟩

theorem sign_refl : Reflexive same_sign := by
  intro x
  by_cases x = 0
  exact Or.inl ⟨ h, h ⟩
  exact Or.inr (mul_self_pos.mpr h)

theorem sign_symm : Symmetric same_sign := by
  intros x y
  intro h
  rcases h with h|h
  tauto
  right
  linarith

theorem sign_trans : Transitive same_sign := by
  intros x y z
  intro hxy
  intro hyz
  rcases hxy with hxy|hxy

  rcases hyz with hyz|hyz
  tauto
  have hy : y = 0 := hxy.2
  rw [hy] at hyz
  ring_nf at hyz
  contradiction

  rcases hyz with hyz|hyz
  have hy : y = 0 := hyz.1
  rw [hy] at hxy
  ring_nf at hxy
  contradiction

  right
  have h : (x * y) * (y * z) > 0 := Int.mul_pos hxy hyz
  have h' : (x * y) * (y * z) = (x * z) * (y * y) := by ring_nf
  rw [h'] at h
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hxy
    norm_num at hxy
  have hy' : y * y > 0 := mul_self_pos.mpr hy
  exact (zero_lt_mul_right hy').mp h

--
