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

example : IsOpen (univ : Set X) :=
  isOpen_univ

example : IsOpen (∅ : Set X) :=
  isOpen_empty

example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) := isOpen_iInter hs

example : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
