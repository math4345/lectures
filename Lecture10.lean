import Mathlib.Tactic

-- Math 4345: Lecture 10
--  _              _                    _  ___  
-- | |    ___  ___| |_ _   _ _ __ ___  / |/ _ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | |
-- | |__|  __/ (__| |_| |_| | | |  __/ | | |_| |
-- |_____\___|\___|\__|\__,_|_|  \___| |_|\___/ 
--                                              

section

variable {α : Type} (P Q : α → Prop)

example (h : ∀ x, P x ∧ Q x) : (∀ x, P x) ∧ (∀ x, Q x) := 
  Iff.mp forall_and h

example (h : ∀ x, P x ∧ Q x) : (∀ x, P x) ∧ (∀ x, Q x) := 
  ⟨ fun x => (h x).1, fun x => (h x).2 ⟩  

def s04p02 (h : ∀ x, P x ∧ Q x) : (∀ x, P x) ∧ (∀ x, Q x) := by
  -- Our goal is to prove something AND something else,
  -- so we `apply And.intro` to separate that into two goals.
  apply And.intro

  -- First goal: ∀ x, P x
  intro x -- "Suppose x ∈ α.  My goal is to show that P(x)."
  -- rcases h x with ⟨ px, _ ⟩ -- "But our hypothesis applied to x, P(x) ∧ Q(x)."
  let px := (h x).1
  exact px  

  -- Second goal: ∀ x, Q x
  intro x
  rcases h x with ⟨ _, qx ⟩
  exact qx

-- new tactic: specialize
example (h : ∀ x, P x ∧ Q x) : (∀ x, P x) ∧ (∀ x, Q x) := by
  -- Our goal is to prove something AND something else,
  -- so we `apply And.intro` to separate that into two goals.
  apply And.intro

  -- "First, I'll prove that, if x ∈ α, then P(x)."
  intro y -- "Suppose y ∈ α."
  specialize h y -- "I have the hypothesis that ∀ x, P(x) ∧ Q(x)"
                 -- "Specialize that hypothesis to y."
  rcases h with ⟨ px, _ ⟩
  exact px

  -- "Next, I'll prove that if x ∈ α, then Q(x)."
  intro y
  specialize h y
  exact h.right 

end section

-- The function f : ℝ → ℝ is _bounded_ means 
-- there exists b ∈ ℝ so that for all × ∈ ℝ we have f(x) ≤ b.    
def bounded (f : ℝ → ℝ) := ∃ b, ∀ x, f x ≤ b

-- Claim: if f : ℝ → ℝ is bounded,
-- then g : ℝ → ℝ defined by g(x) = 2 f(x) is bounded. 
example {f : ℝ → ℝ} : bounded f → bounded ( fun x => 2 * f x ) := by
  intro h -- "Suppose f : ℝ → ℝ is bounded."
  dsimp [bounded] at * -- "Recall that bounded means..."
  rcases h with ⟨ c, h' ⟩ -- "Since f is bounded, ∃ bound c such that ..."
  use 2 * c -- "The function g is bounded by 2*c."
  intro x -- "Suppose x ∈ ℝ"
  specialize h' x -- "Then f(x) ≤ c"
  linarith -- "So 2*f(x) ≤ 2*c."

-- Claim: if f : ℝ → ℝ and g : ℝ → ℝ are both bounded,
-- then their sum is also bounded.
example {f g : ℝ → ℝ} : bounded f → bounded g → bounded ( fun x => f x + g x ) := by
  intro hf
  intro hg
  rcases hf with ⟨ bf, hf ⟩
  rcases hg with ⟨ bg, hg ⟩
  use bf + bg -- this is the **key step**
  intro x
  exact add_le_add (hf x) (hg x)

example {f g : ℝ → ℝ} : bounded f → bounded g → bounded ( fun x => f x + g x ) := by
  rintro ⟨ bf, hf ⟩
  rintro ⟨ bg, hg ⟩
  exact ⟨ bf + bg, fun x => add_le_add (hf x) (hg x) ⟩ 

example {f g : ℝ → ℝ} (hf : bounded f) (hg : bounded g) : bounded ( fun x => f x + g x ) := by
  rcases hf with ⟨ bf, hf ⟩
  rcases hg with ⟨ bg, hg ⟩
  exact ⟨ bf + bg, fun x => add_le_add (hf x) (hg x) ⟩ 

-- the squaring function is continuous at zero
example : ∀ (ε : ℝ), (0 < ε) →
  ∃ (δ : ℝ), (0 < δ) ∧ ∀ (x : ℝ), abs x < δ → abs (x * x) < ε := by
  intro ε 
  intro hε
  use min ε 1 -- pick δ = min(ε,1)

  apply And.intro

  apply lt_min
  exact hε
  norm_num

  intro x
  intro hx
  
  --have h' : |x| < ε ∧ |x| < 1 := Iff.mp lt_min_iff hx
  --rcases h' with ⟨ h, h1 ⟩ 
  rcases Iff.mp lt_min_iff hx with ⟨ h, h1 ⟩
  clear hx  

  have h'' : |x| * |x| < ε * 1
  apply mul_lt_mul'
  linarith
  exact h1
  apply abs_nonneg
  exact hε

  rw [abs_mul]  
  ring_nf at h''
  ring_nf
  exact h''


