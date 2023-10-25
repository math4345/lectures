import Mathlib.Tactic

-- Math 4345: Lecture 26
--  _              _                    ____   __
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \ / /_
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | '_ \
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/| (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |_____|\___/
--
--

section

variable {α : Type*}
-- should we include [Inhabited α] ?

-- Recall our notion of "subset"
variable (P : α → Prop)
#check { x : α | P x }

-- a "relation" is a proposition that depends on two inputs
variable (R : α → α → Prop)

variable (x y : α)
#check R x y

def the_same (x : ℕ) (y : ℕ) : Prop := x = y

example : the_same 3 3 := by rfl

example : ¬ the_same 3 4 := by
  unfold the_same
  norm_num

variable (ht : Transitive R)
variable (hs : Symmetric R)

example (a b c : α) (h : R a b ∧ R b c) : R a c := by
  unfold Transitive at ht
  rcases h with ⟨ hab, hbc ⟩
  exact ht hab hbc

example (a b : α) (h : R a b) : R b a := by
  unfold Symmetric at hs
  exact hs h

-- A "proof" that Symmetry and Transitivity imply Reflexivity
example (a : α) : R a a := by
  -- suppose I knew R a b
  have h : ∃ (b : α), R a b := by
    sorry
  rcases h with ⟨ b, h ⟩
  -- then by symmetry, I'd know R b a
  have hba : R b a := hs h
  -- then by transitivity, R a b and R b a imply R a a
  exact ht h hba

end section

-- The above is impossible!

-- In fact, there is a relation,
-- which is symmetric
-- and transitive
-- but NOT reflexive.

def weird_relation : ℕ → ℕ → Prop := fun
| _, _ => False

example : ¬ Reflexive weird_relation := by
  unfold weird_relation
  unfold Reflexive
  simp only [forall_const, not_false_eq_true]

example : Symmetric weird_relation := by
  intros _ _ h
  exfalso
  exact h

example : Transitive weird_relation := by
  intros _ _ _ hxy _
  exfalso
  exact hxy

--

def less_than (x y : ℤ) : Prop := (x < y)

example : Transitive less_than := by
  intros x y z hxy hyz
  unfold less_than at *
  exact Int.lt_trans hxy hyz

example : ¬ Reflexive less_than := by
  unfold Reflexive
  unfold less_than
  push_neg
  use 0

example : ¬ Symmetric less_than := by
  unfold Symmetric
  unfold less_than
  simp only [not_forall, not_lt]
  use 0
  use 1
  norm_num

def same_parity (a b : ℤ) : Prop := ∃ (k : ℤ), a - b = 2 * k

def same_parity' (a b : ℤ) : Prop := (a % 2) = (b % 2)

example : same_parity' 3 5 := by
  unfold same_parity'
  norm_num

example : same_parity 3 5 := by
  unfold same_parity
  use -1
  norm_num

def same_sign (a b : ℤ) : Prop := Int.sign a = Int.sign b

example : same_sign 3 4 := by
  unfold same_sign
  norm_num

example : ¬ same_sign 3 (-3) := by
  unfold same_sign
  norm_num

#check (Setoid.ker same_sign).iseqv.symm

--
