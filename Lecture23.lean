import Mathlib.Tactic
open Function -- for injective and surjective
open Set

-- Math 4345: Lecture 23
--  _              _                    ____  _____
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \|___ /
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | |_ \
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ ___) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|____/
--
--

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u : Set α)
variable (w v wv : Set β)

lemma subset_image_preimage' (r : Set β) (h : Surjective f) :
  r ⊆ f '' (f ⁻¹' r) := by
  intros x h'
  simp only [mem_image, mem_preimage]
  rcases h x with ⟨ a, ha ⟩
  use a
  rw [ha]
  tauto

lemma subset_preimage_image' (r : Set β) (h : Surjective f) :
  f '' (f ⁻¹' r) ⊆ r := by
  intros x h'
  simp only [mem_image, mem_preimage] at h'
  rcases h' with ⟨ a, h1, h2 ⟩
  rw [← h2]
  exact h1

example (r : Set β) (h : Surjective f) : f '' (f ⁻¹' r) = r := image_preimage_eq r h

example (r : Set β) (h : Surjective f) : f '' (f ⁻¹' r) = r := by
  ext x
  constructor
  apply subset_preimage_image'
  exact h
  apply subset_image_preimage'
  exact h

def square : ℤ → ℤ := fun x => x * x

example : ¬ (Injective square) := by
  dsimp [Not]
  unfold Injective
  intro h
  have k : square (2 : ℤ) = square (-2 : ℤ)
  rfl
  specialize h k
  tauto

example : ¬ (Surjective square) := by
  intro h
  specialize h (-1)

  have k : ∀ (x : ℤ), square x ≥ 0
  intro x
  exact mul_self_nonneg x

  rcases h with ⟨ a, h ⟩
  specialize k a
  rw [h] at k
  have nk : ¬(-1 ≥ 0) := by norm_num
  exact nk k

def square' (x : ℕ) : ℕ := x * x

lemma monotone_square' : Monotone square' := by
  unfold Monotone
  intros a b
  intro h
  unfold square'
  exact Nat.mul_le_mul h h

example : ¬ ∃ (n : ℕ), square' n = 2 := by
  push_neg
  intro n
  unfold square'

  by_cases h0 : n = 0
  rw [h0]
  norm_num
  by_cases h1 : n = 1
  rw [h1]
  norm_num
  by_cases h2 : n = 2
  rw [h2]
  norm_num

  have k : n > 2 := Nat.two_lt_of_ne h0 h1 h2
  have k' := monotone_square' (by linarith : n ≥ 2)
  unfold square' at k'
  linarith

example (P : Prop) : P → (¬ (¬ P)) := fun p => fun np => np p

example : ∃ (γ : Type) (g : γ → γ) (A : Set γ), ¬ (g ⁻¹' (g '' A) ⊆ A) := by
  use ℤ
  use square
  use Set.singleton 1

  have h' : square '' Set.singleton 1 = Set.singleton 1
  exact Iff.mp Set.toFinset_inj rfl
  rw [h']
  push_neg

  rw [Set.subset_def]
  simp
  use -1

  constructor

  unfold square
  simp
  exact rfl

  tauto

---

example : f '' (f ⁻¹' w) ⊆ w := by
  intro x
  intro h
  rcases h with ⟨ y, h1, h2 ⟩
  simp at h1
  rw [h2] at h1
  assumption

example (h : v ⊆ w) : f ⁻¹' v ⊆ f ⁻¹' w := preimage_mono h

example (h : v ⊆ w) : f ⁻¹' v ⊆ f ⁻¹' w := by
  simp only [subset_def]
  intros x h'
  simp only [mem_preimage]
  simp only [mem_preimage] at h'
  -- `exact h h'` will already work!
  simp only [subset_def] at h
  specialize h (f x)
  exact h h'

example (h : v ⊆ w) (hh : w ⊆ wv) : v ⊆ wv := by
  simp only [subset_def] at h
  simp only [subset_def] at hh
  simp only [subset_def]
  intros x h'
  exact (hh x) ((h x) h')
