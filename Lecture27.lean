import Mathlib.Tactic

-- Math 4345: Lecture 27
--  _              _                    ____ _____
-- | |    ___  ___| |_ _   _ _ __ ___  |___ \___  |
-- | |   / _ \/ __| __| | | | '__/ _ \   __) | / /
-- | |__|  __/ (__| |_| |_| | | |  __/  / __/ / /
-- |_____\___|\___|\__|\__,_|_|  \___| |_____/_/
--
--

-- Please turn in your projects

-- I'll share these anonymously so you will have a chance to provide feedback

section

#check False

variable (α : Type*)
variable (Rₐ : α → α → Prop) -- Rₐ is a relation on α

variable (R : False → False → Prop) -- R is a relation on False

example : Reflexive R := by
  unfold Reflexive
  intro x
  exfalso
  exact x

end section

section

variable (α : Type*) [Inhabited α]
#check (default : α)

example : ∃ (R : α → α → Prop), (Symmetric R ∧ Transitive R ∧ ¬ Reflexive R) := by
  let weird_relation : α → α → Prop := fun
    | _, _ => False
  use weird_relation
  constructor

  intros _ _ h
  exfalso
  exact h

  constructor
  intros _ _ _ hxy _
  exfalso
  exact hxy

  unfold Reflexive
  intro h
  specialize h default
  exact h

end section

--

-- Let's talk about Quotients!

section

-- I can make subsets

#check ({ x : ℕ | ∃ y, x = y + y } : Set ℕ)

def m (x : ℤ) : ℤ := x % 2

#eval m 5
#eval m 4

#check (Setoid.ker m)

def S := Setoid.ker m
def Zmod2 := Quotient S

#check Zmod2

-- ℤ → ℤ/2ℤ
def mod2 (x : ℤ) : Zmod2 := Quotient.mk'' x

#check mod2 4  -- 4 ↦ ⟦0⟧

#check mod2 5  -- 5 ↦ ⟦1⟧

example : mod2 4 = mod2 6 := Quotient.sound (by rfl : m 4 = m 6)

def f (x : ℤ) (y : ℤ) : Zmod2 := mod2 (x + y)

#check f 5 3

example : f 5 3 = f 3 7 := Quotient.sound (by rfl : m 8 = m 10)

lemma s (x y : ℤ) (h : @Setoid.r ℤ (Setoid.ker m) x y) : m x = m y := by
  exact h

def add_mod (x y : ℤ) : (x + y) % 2 = ( (x % 2) + (y % 2) ) % 2 := by
  exact Int.add_emod x y 2

-- ⟦1⟧ + ⟦0⟧ = ⟦1⟧
-- ⟦1⟧ + ⟦1⟧ = ⟦0⟧

def add (a : Zmod2) (b : Zmod2) : Zmod2 :=
  Quotient.lift₂ f (fun a1 b1 a2 b2 ha hb => by
    unfold f
    have ha' : a1 % 2 = a2 % 2 := ha
    have hb' : b1 % 2 = b2 % 2 := hb
    have h : (a1 + b1) % 2 = (a2 + b2) % 2 := by
      have hs : (a1 % 2) + (b1 % 2) = (a2 % 2) + (b2 % 2) := by linarith
      have hs' : ((a1 % 2) + (b1 % 2)) % 2 = ((a2 % 2) + (b2 % 2)) % 2 := by congr
      rw [add_mod, add_mod] at hs'
      simp at hs'
      exact hs'
    exact Quotient.sound h
    ) a b

example : add (mod2 1) (mod2 1) = mod2 0 := by
  unfold add
  sorry
