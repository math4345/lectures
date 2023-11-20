import Mathlib.Tactic

-- Math 4345: Lecture 36
--  _              _                    _____  __
-- | |    ___  ___| |_ _   _ _ __ ___  |___ / / /_
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \| '_ \
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) | (_) |
-- |_____\___|\___|\__|\__,_|_|  \___| |____/ \___/
--
--

-- We only meet Monday this week because of Thanksgiving.

-- There is no new homework assignment this week -- use this time to
-- catch up if you are behind.

-- The topic is "algebra" which is setting us up for success next
-- week, when our topic is "group theory."

-- To focus our discussion today, we'll work with monoids.

section

variable {M : Type*} [Monoid M]

#check Monoid ℕ

example (a b c : M) : (a*b)*c = a*(b*c) := by exact?
example (a b c : M) : a*(b*c) = (a*b)*c := by exact?

example (m : M) : 1*m = m := by exact?
example (m : M) : m*1 = m := by exact?
example (m : M) : m ^ 3 = m * m * m := by exact?

example (a b c d : M) : (a*b)*(c*d) = a*(b*c)*d := by sorry

example (e : M) : (∀ (m : M), e * m = m) → e = 1 := by
  intro h
  specialize h 1
  rwa [mul_one] at h

end section

section

variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable (f : M →* N)

#check f

example  (x y : M) (f : M →* N) : f (x * y) = (f x) * (f y) := by exact?

end section

section
-- M is a monoid; if an element m ∈ M is left invertible and right inverible,
-- then these inverses are the same.
end section

section
-- M is a monoid; is it possible for an element to have distinct inverses?
end section
