import Mathlib.Tactic

-- Math 4345: Lecture 11
--  _              _                    _ _ 
-- | |    ___  ___| |_ _   _ _ __ ___  / / |
-- | |   / _ \/ __| __| | | | '__/ _ \ | | |
-- | |__|  __/ (__| |_| |_| | | |  __/ | | |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|_|
--                                          
-- 

-- This week's goal is to think through "term mode" and how this
-- differs from the "tactics" we have been using.

def f (x : ℝ) : ℝ := 2 * x

#check f
#eval f 4

def g (n : ℕ) : ℕ := n + 1

#check g
#eval g 4

def h := fun (n : ℕ) => n + n

#eval h 8


example : Monotone (fun (x : ℝ) => 2 * x) := by
  dsimp [Monotone]
  intro a b
  intro h
  linarith

example {f g : ℝ → ℝ} : Monotone f → Monotone g → Monotone ( fun x => f x + g x ) := by
  intro hf
  intro hg
  -- dsimp [Monotone]
  intro a b
  intro h
  have hf' : f a ≤ f b
  apply hf
  exact h
  have hg' : g a ≤ g b := hg h
  exact add_le_add hf' hg'

example {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) :
  Monotone ( fun x => f x + g x ) := by
    intro a b
    intro h
    exact add_le_add (hf h) (hg h)

example {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) :
  Monotone ( fun x => f x + g x ) := 
    fun a b h => by exact add_le_add (hf h) (hg h)
      
example {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) :
  Monotone ( fun x => f x + g x ) := 
    fun _ _ h => add_le_add (hf h) (hg h)

-- this is a "term mode" proof
example {f g : ℝ → ℝ} : Monotone f → Monotone g →
  Monotone ( fun x => f x + g x ) := 
    fun hf hg _ _ h => add_le_add (hf h) (hg h)


def s04p09 (m : ℝ) (b : ℝ) : (m ≥ 0) → Monotone (fun x ↦ m * x + b) := by
  sorry

example (b : ℝ) : Function.Surjective (fun x ↦ x + b) := by
  intro y
  use y - b
  norm_num

example (b : ℝ) : Function.Surjective (fun x ↦ x + b) := by
  dsimp [Function.Surjective]
  intro y
  use y - b
  exact sub_add_cancel y b

example (b : ℝ) : Function.Surjective (fun x ↦ x + b) :=
  fun y => ⟨ y - b, by norm_num ⟩

example (b : ℝ) : Function.Surjective (fun x ↦ x + b) :=
  fun y => ⟨ y - b, sub_add_cancel y b ⟩

example : (c : ℝ) → Function.Surjective (fun x ↦ x + c) := by
  intro b
  dsimp [Function.Surjective]
  intro y
  use y - b
  exact sub_add_cancel y b

section

variable (P Q R : Prop)

example : (P ∧ Q) → P := by
  intro h
  let k := h.left
  exact k

example : (P ∧ Q) → P := by
  intro h
  let ⟨ hp, _ ⟩ := h
  exact hp

example : (P ∧ Q) → P := by
  intro h
  exact h.left

example : (P ∧ Q) → P := by
  intro h
  rcases h with ⟨ hp, _ ⟩
  exact hp

example : ℝ → ℝ := fun x => 2 * x

-- "Curry-Howard isomorphism" is a fancy name for this

example : (P ∧ Q) → P := fun h => h.left

example : (P ∧ Q) → P := fun ⟨ hp, _ ⟩ => hp

example : P → P := fun h => h

example : P → (P ∧ P) := fun h => And.intro h h

example : P → (P ∧ P) := fun h => ⟨ h, h ⟩

example : P → (P ∧ P) := fun h => { left := h, right := h }

example : P → (P → Q) → (Q → R) → R := by
  intro hp
  intro hpq
  intro hqr
  apply hqr
  apply hpq
  exact hp

example : P → (P → Q) → (Q → R) → R := by
  intro hp
  intro hpq
  intro hqr
  let k := hpq hp
  exact hqr k

example : P → (P → Q) → (Q → R) → R := by
  intro hp
  intro hpq
  intro hqr
  exact hqr (hpq hp)

example : (P → Q) → (Q → R) → (P → R) := by
  intro hpq
  intro hqr
  intro hp
  exact hqr (hpq hp)

example : (P → Q) → (Q → R) → (P → R) := 
  fun hpq hqr hp => hqr (hpq hp)

example : (P → Q) → (Q → R) → (P → R) := 
  fun hpq hqr => hqr ∘ hpq

end section

section

variable (P Q R : Type*)

example : (P → Q) → (Q → R) → (P → R) := 
  fun hpq hqr => hqr ∘ hpq

end section

section

variable (P Q R : Prop)

example : P → (P ∨ Q) := by
  intro h
  left
  exact h

example : P → (P ∨ Q) := fun h => Or.inl h

example : Q → (P ∨ Q) := fun h => Or.inr h

-- this is the "left injection" from P to P ∨ Q
example : P → (P ∨ Q) := Or.inl

-- this is the "right injection" from Q to P ∨ Q
example : Q → (P ∨ Q) := Or.inr

example : (P ∨ Q) → (P ∨ Q) := fun h => h

example : (P ∨ Q) → (Q ∨ P) := by
  intro h
  rcases h with hp|hq
  exact Or.inr hp
  exact Or.inl hq

example : (P ∨ Q) → (Q ∨ P) := sorry

end section

