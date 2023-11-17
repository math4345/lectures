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

def double (x : ℝ) : ℝ := x + x
def double' : ℝ → ℝ := fun x => x + x

#check (Set.Ioo (0 : ℝ) 1 : Set ℝ)

-- variable (p : Set.Ioo (0 : ℝ) 1)
-- #check ((Set.Ioo (0: ℝ) 1) : Type)
-- #check (Elem (Set.Ioo (0: ℝ) 1) : Type)

-- recall Set.Ioo 0 1 is (0,1)
--    and Set.Ioo 0 2 is (0,2)
def double'' : Set.Ioo (0 : ℝ) 1 → Set.Ioo (0 : ℝ) 2 := by
  rintro ⟨ x, hx ⟩
  simp at hx
  rcases hx with ⟨ h0, h1 ⟩
  refine ⟨ x + x, ?h ⟩
  simp
  apply And.intro
  <;> linarith

def double''' : Set.Ioo (0 : ℝ) 1 → ℝ := by
  rintro ⟨ x, _ ⟩
  exact x + x

-- (0,2) ∪ (1,3) = (0,3)
example : Ioo (0 : ℝ) 2 ∪ Ioo (1 : ℝ) 3 = Ioo (0 : ℝ) 3 := by
  ext x
  simp
  constructor
  intro h
  constructor
  rcases h with h|h
  linarith
  linarith
  rcases h with h|h
  linarith
  linarith

  intro h
  by_cases h' : x < 2
  constructor
  constructor
  linarith
  linarith
  right
  constructor
  linarith
  linarith

variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y]
variable (f : X → Y)

example : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

def g : ℝ → ℝ := fun x => 2 * x

-- Calculate g⁻¹( open interval )
lemma preimage_interval (a b : ℝ) : g ⁻¹' (Set.Ioo a b) = Set.Ioo (a / 2) (b / 2) := by
  ext x
  simp only [mem_preimage]
  simp only [gt_iff_lt, not_lt, ge_iff_le, mem_Ioo]
  apply Iff.intro

  intro h
  rcases h with ⟨ ha, hb ⟩
  unfold g at *

  apply And.intro
  <;> linarith

  intro h
  unfold g
  exact And.intro (by linarith) (by linarith)

-- `open_intervals` consists of all intervals (a,b) for a, b ∈ ℝ
def open_intervals : Set (Set ℝ) := { S : Set ℝ | ∃ a b : ℝ , S = Ioo a b }

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

section

variable {U V : Type*}
variable (A B : Set V)
variable (f : U → V)

example : (f ⁻¹' A) ∪ (f ⁻¹' B) = f ⁻¹' (A ∪ B) := rfl

example : (f ⁻¹' A) ∪ (f ⁻¹' B) = f ⁻¹' (A ∪ B) := by
  ext x
  constructor <;> simp only [preimage_union, mem_union, mem_preimage, imp_self]

end section
