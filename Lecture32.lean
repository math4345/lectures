import Mathlib.Tactic

-- Math 4345: Lecture 32
--  _              _                    _________
-- | |    ___  ___| |_ _   _ _ __ ___  |___ /___ \
-- | |   / _ \/ __| __| | | | '__/ _ \   |_ \ __) |
-- | |__|  __/ (__| |_| |_| | | |  __/  ___) / __/
-- |_____\___|\___|\__|\__,_|_|  \___| |____/_____|

inductive Plant where
| root : Plant
| node : Plant → Plant → Plant
deriving Repr

open Plant

#eval root
#eval node root root
#eval node (node root root) root

def count_leaves (plant : Plant) : ℕ :=
  match plant with
    | root => 1
    | node p1 p2 => (count_leaves p1) + (count_leaves p2)

#eval count_leaves (node (node root root) root)

#eval count_leaves (node root root)

-- -- -- --

inductive NatStartingAtOne where
| one : NatStartingAtOne
| successor : NatStartingAtOne → NatStartingAtOne
deriving Repr

open NatStartingAtOne

#check one

def as_usual_nat (x : NatStartingAtOne) : ℕ :=
  match x with
  | one => 1
  | successor y => Nat.succ (as_usual_nat y)

#eval as_usual_nat (successor (successor one))

-- -- -- --

inductive Cities where
| chicago : Cities
| columbus : Cities
| nyc : Cities
deriving Repr

open Cities

#check (@dist ℝ)

#eval (@dist ℝ (by infer_instance) (2 : ℝ) (7 : ℝ))

instance : Dist Prop where
  dist (_ _ : Prop) := 17

example : Dist Prop := inferInstance

instance : Dist Cities where
  dist (x y : Cities) := match x with
    | chicago => match y with
                   | chicago => 0
                   | columbus => 10
                   | nyc => 40
    | columbus => match y with
                   | chicago => 10
                   | columbus => 0
                   | nyc => 30
    | nyc => match y with
                   | chicago => 40
                   | columbus => 30
                   | nyc => 0

instance : PseudoMetricSpace Cities where
  dist_self (x : Cities) := by rcases x <;> rfl
  dist_comm (x y : Cities) := by
    rcases x <;> rcases y <;> rfl
  dist_triangle (x y z : Cities) := by
    rcases x <;> rcases y <;> rcases z <;>
    dsimp [dist] <;> norm_num
  edist_dist (x y : Cities) := by exact?

instance : MetricSpace Cities where
  eq_of_dist_eq_zero := by
    intros x y
    intro h
    rcases x <;> rcases y
    <;> dsimp [dist] at h
    <;> norm_num at h
    <;> rfl

def ball (r : ℝ) (c : Cities) : Set Cities := { p : Cities | dist c p < r }

example : 0 ∉ Set.singleton 17 :=
  by apply?

example : ball 5 nyc = Set.singleton nyc := by
  ext x
  constructor

  intro h
  dsimp [ball] at h
  dsimp [dist] at h
  rcases x

  simp at h
  norm_num at h
  simp at h
  norm_num at h
  simp at h
  exact rfl

  intro h
  rcases x
  rw [Set.mem_singleto]

inductive Island where
| island : ℕ → Island
deriving Repr

open Island

instance : Dist Island where
  dist (x y : Island) :=
    match x with
      | (island x') => match y with
                       | (island y') =>
                         if x' == y' then 0 else 1

instance : PseudoMetricSpace Island where
  dist_self (x : Island) := by
    rcases x
    dsimp [dist]
    simp
  dist_comm (x y : Island) := by
    rcases x
    rcases y
    dsimp [dist]
    simp
    sorry
  dist_triangle (x y z : Cities) := by
    rcases x <;> rcases y <;> rcases z <;>
    dsimp [dist] <;> norm_num
  edist_dist (x y : Cities) := by exact?


#eval (dist (island 17) (island 200))

#check (dist x y : ℝ)
#check (dist_eq_zero : dist x y = 0 ↔ x = y)
#check (dist_nonneg : 0 ≤ dist x y)
#check (dist_comm _ _ : dist x y = dist y x)
#check (dist_triangle _ _ _ : dist x z ≤ dist x y + dist y z)
