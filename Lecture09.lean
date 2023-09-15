import Mathlib.Tactic

-- Math 4345: Lecture 9
--  _              _                     ___   ___  
-- | |    ___  ___| |_ _   _ _ __ ___   / _ \ / _ \ 
-- | |   / _ \/ __| __| | | | '__/ _ \ | | | | (_) |
-- | |__|  __/ (__| |_| |_| | | |  __/ | |_| |\__, |
-- |_____\___|\___|\__|\__,_|_|  \___|  \___/   /_/ 
--                                                  
-- 

variable {α : Type} (P : α → Prop)

variable (Q R : Prop)

example : Q → ¬ Q → False := by
  intros q nq
  exact nq q

example : Q → R → Q ∧ R := by
  intro hq
  intro hr
  -- exact ⟨ hq, hr ⟩
  apply And.intro
  exact hq
  exact hr

lemma l1 : (∀ x, ¬ P x) → (¬ ∃ x, P x) := by
  rintro h ⟨ y, py ⟩
  exact h y py

lemma l2 : (¬ ∃ x, P x) → ∀ x, ¬ P x := by
  intro h
  dsimp [Not] at *
  intro x
  intro px
  apply h
  have h' : ∃ x, P x
  exact ⟨ x,  px ⟩
  exact h'

example : (∀ x, ¬ P x) ↔ (¬ ∃ x, P x) := by
  exact Iff.symm not_exists

example : (∀ x, ¬ P x) ↔ (¬ ∃ x, P x) := by
  constructor
  apply l1
  apply l2

example : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  contrapose! -- P => Q iff not Q => not P
  intro h
  exact h

example : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  by_contra h'
  push_neg at h'
  exact h h'

example : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  exact not_forall.mp

-- If it isn't the case that, for all x, P(x),
-- then there exists an x so that P(x) is false.
example : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro h -- Suppose the hypothesis: ¬ ∀ x, P x
  by_contra h' -- Assume, to the contrary,
               -- that there does NOT exist
               -- an x so that P(x) is false.
  apply h -- I will get a contradiction by
          -- proving ∀ x, P x
  intro x -- To prove ∀ x, P x, I pick an arbitrary
          -- x and prove P(x).
  by_contra np -- Suppose P(x) were false...
  apply h' -- but I assumed earlier there did NOT
           -- exist an x so that P(x) is false.
  exact ⟨ x, np ⟩ -- the arbitrary x provides
                 -- a contradiction.

