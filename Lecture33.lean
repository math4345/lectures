import Mathlib.Tactic
open Set

-- Math 4345: Lecture 33
--  _              _                    __________
-- | |    ___  ___| |_ _   _ _ __ ___  |___ /___ /
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \ |_ \
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) |__) |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/____/
--
--

variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y]
variable (f : X → Y)

-- Recall `univ`  means the whole of X, regarded as a subset of X.
example : IsOpen (univ : Set X) := isOpen_univ
example : IsOpen (∅ : Set X) := isOpen_empty
example : IsOpen (univ : Set Y) := isOpen_univ
example : IsOpen (∅ : Set Y) := isOpen_empty

example {ι : Type*} {A : ι → Set X} (ho : ∀ i : ι, IsOpen (A i)) :
  IsOpen (⋃ i, A i) := isOpen_iUnion ho

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) := isOpen_iInter hs

example (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∪ B) :=
  IsOpen.union hA hB

-- You might also enjoy https://loogle.lean-lang.org/

/-- A set is closed if its complement is open -/
example (A : Set X) (h : IsClosed A) : IsOpen Aᶜ := isOpen_compl_iff.mpr h

example : IsOpen (∅ : Set X) := isOpen_empty
example : IsClosed (∅ : Set X) := isClosed_empty
example : IsOpen (univ : Set X) := isOpen_univ

example (A : Set X) (h : IsClosed A) : IsOpen Aᶜ := isOpen_compl_iff.mpr h

example (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ∪ B) := by
  have h : IsOpen (Aᶜ ∩ Bᶜ)
  apply IsOpen.inter
  exact isOpen_compl_iff.mpr hA
  exact isOpen_compl_iff.mpr hB
  have h' : IsOpen (A ∪ B)ᶜ
  have h'' : (A ∪ B)ᶜ = (Aᶜ ∩ Bᶜ) := compl_union A B
  rw [h'']
  assumption
  exact isOpen_compl_iff.mp h'

example (A B : Set X) : IsClosed A → IsClosed B → IsClosed (A ∪ B) := by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter

example (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ∪ B) :=
  IsClosed.union hA hB

example {ι : Type*} [Fintype ι] {A : ι → Set X} (hc : ∀ i : ι, IsClosed (A i)) :
  IsClosed (⋃ i, A i) := isClosed_iUnion hc

example {ι : Type*} {A : ι → Set X} (hc : ∀ i : ι, IsClosed (A i)) :
  IsClosed (⋂ i, A i) := isClosed_iInter hc

example : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
