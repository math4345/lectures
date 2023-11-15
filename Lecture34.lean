import Mathlib.Tactic
open Set

-- Math 4345: Lecture 34
--  _              _                    _____ _  _
-- | |    ___  ___| |_ _   _ _ __ ___  |___ /| || |
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \| || |_
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) |__   _|
-- |_____\___|\___|\__|\__,_|_|  \___| |____/   |_|
--
--

variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y]
variable (f : X → Y)

example : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

def g : ℝ → ℝ := fun x => 2 * x

lemma preimage_interval (a b : ℝ) : g ⁻¹' (Set.Ioo a b) = Set.Ioo (a / 2) (b / 2) := by
  ext x
  simp
  unfold g
  constructor
  rintro ⟨ h1, h2 ⟩
  constructor
  <;> linarith

  rintro ⟨ h1, h2 ⟩
  constructor
  <;> linarith


def open_intervals : Set (Set ℝ) := { S | ∃ a b : ℝ , S = Set.Ioo a b }

lemma is_basis : TopologicalSpace.IsTopologicalBasis open_intervals := by
  refine TopologicalSpace.isTopologicalBasis_of_open_of_nhds ?h_open ?h_nhds
  unfold open_intervals
  simp
  intros u x1 x2 h
  rw [h]
  exact isOpen_Ioo

  intros a u ha hu
  unfold open_intervals
  simp
  sorry


example : Continuous g := by
  apply TopologicalSpace.IsTopologicalBasis.continuous (is_basis)
  unfold open_intervals
  simp
  intro s x1 x2 hs
  rw [hs]
  rw [preimage_interval x1 x2]
  exact isOpen_Ioo
