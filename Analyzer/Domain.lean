import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice


namespace Analyzer

/- In concrete machine an Integer is a poitn
In an abstarct domain we need to define negInf and PosInf-/
inductive ExtendedInt where
  | neg_inf
  | fin : Int → ExtendedInt
  | pos_inf
deriving BEq, DecidableEq, Repr
/-
Abstract Domain intger is now a Interval
we define bot as the empty interval and Top as a range implicitly
-/

def ExtendedInt.max : ExtendedInt → ExtendedInt → ExtendedInt
  | .pos_inf, _ => .pos_inf
  | _, .pos_inf => .pos_inf
  | .neg_inf, a => a
  | a, .neg_inf => a
  | .fin x, .fin y => .fin (Max.max x y)

def ExtendedInt.min : ExtendedInt → ExtendedInt → ExtendedInt
  | .neg_inf, _ => .neg_inf
  | _, .neg_inf => .neg_inf
  | .pos_inf, a => a
  | a, .pos_inf => a
  | .fin x, .fin y => .fin (Min.min x y)

-- This tells Lean how to compare two individual bounds (-inf, fin x, +inf)
-- 1. Define computable Boolean functions FIRST
def ExtendedInt.leBool : ExtendedInt → ExtendedInt → Bool
  | .neg_inf, _ => true
  | _, .pos_inf => true
  | .fin x, .fin y => decide (x ≤ y) -- 'decide' turns the Int Prop into a Bool
  | _, _ => false

inductive Interval where
  | bot
  | range (low high : ExtendedInt )
deriving BEq, DecidableEq, Repr

-- This "Smart Constructor" ensures we only create valid ranges
def mkInterval (l u : ExtendedInt) : Interval :=
  if l.leBool u then .range l u else .bot

def Interval.top : Interval := .range .neg_inf .pos_inf
def Interval.leBool : Interval → Interval → Bool
  | .bot, _ => true
  | _, .bot => false
  | .range l1 h1, .range l2 h2 =>
      -- Use boolean && instead of logical ∧
      ExtendedInt.leBool l2 l1 && ExtendedInt.leBool h1 h2

/-In a WHILE language, 0 is typically False and non-zero is True.
  overlapsTrue checks if the interval contains ANY value besides 0.
-/
def Interval.overlapsTrue : Interval → Bool
  | .bot => false
  | .range low high =>
      -- If the range is NOT exactly [0, 0], it contains at least one 'True' value.
      !(low == .fin 0 && high == .fin 0)

/-overlapsFalse checks if the interval contains the value 0.
-/
def Interval.overlapsFalse : Interval → Bool
  | .bot => false
  | .range low high =>
      -- Standard containment check: is 0 ∈ [low, high]?
      ExtendedInt.leBool low (.fin 0) && ExtendedInt.leBool (.fin 0) high


-- 2. Link the math symbol `≤` to the Boolean functions.
-- Lean automatically coerces the Bool into a Prop, and natively
-- knows that Bools are Decidable! No manual tactic proofs needed.
instance : LE ExtendedInt where
  le a b := ExtendedInt.leBool a b

instance : LE Interval where
  le i1 i2 := Interval.leBool i1 i2

-- This tells the 'if' statement exactly how to turn '≤' into a 'Bool'
instance (a b : ExtendedInt) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (ExtendedInt.leBool a b = true))

instance (i1 i2 : Interval) : Decidable (i1 ≤ i2) :=
  inferInstanceAs (Decidable (Interval.leBool i1 i2 = true))

def Interval.is_wf : Interval → Prop
  | .bot => True
  | .range l h => l ≤ h


/- The Join operator-/

def Interval.join : Interval → Interval → Interval
-- logic ensure resulting interval wraps both inputs
  | .bot, i2 => i2
  | i1, .bot =>  i1
  | .range l1 h1, .range l2 h2 =>
      mkInterval (ExtendedInt.min l1 l2) (ExtendedInt.max h1 h2)
--end


def Interval.meet : Interval → Interval → Interval
  | .bot, _ => .bot
  | _, .bot => .bot
  | .range l1 h1, .range l2 h2 =>
      mkInterval (ExtendedInt.max l1 l2) (ExtendedInt.min h1 h2)



-- Addition In concrete and Abstract
def ExtendedInt.add : ExtendedInt → ExtendedInt → ExtendedInt
  | .pos_inf, .neg_inf => .pos_inf -- conservative upper-bound: +∞ + (-∞) widened to +∞
  | .neg_inf, .pos_inf => .neg_inf -- conservative lower-bound: -∞ + (+∞) widened to -∞
  | .pos_inf, _ => .pos_inf
  | _, .pos_inf => .pos_inf
  | .neg_inf, _ => .neg_inf
  | _, .neg_inf => .neg_inf
  | .fin x, .fin y => .fin (x + y)

instance : Add ExtendedInt where
  add := ExtendedInt.add

def Interval.add : Interval → Interval → Interval
  | .bot, _ => .bot -- addition of bottom with anything is unreachable
  | _, .bot => .bot
  | .range l1 h1, .range l2 h2 =>
      mkInterval (l1 + l2) (h1 + h2)

-- Subtraction in Concrete and Abstract
def ExtendedInt.sub : ExtendedInt → ExtendedInt → ExtendedInt
  | .pos_inf, .neg_inf => .pos_inf -- +∞ - (-∞) = +∞
  | .neg_inf, .pos_inf => .neg_inf -- -∞ - (+∞) = -∞  (was .pos_inf — soundness bug fix)
  | .pos_inf, _ => .pos_inf
  | _, .pos_inf => .neg_inf        -- a - (+∞) = -∞ for finite a
  | .neg_inf, _ => .neg_inf
  | _, .neg_inf => .pos_inf        -- a - (-∞) = +∞ for finite a
  | .fin x, .fin y => .fin (x - y)

def Interval.sub : Interval → Interval → Interval
  | .bot, _ => .bot -- sub of bottom with anything is unreachable
  | _, .bot => .bot
  | .range l1 h1, .range l2 h2 =>
    -- Formula: [l1, h1] - [l2, h2] = [l1 - h2, h1 - l2]
      mkInterval (l1.sub h2) (h1.sub l2)

-- Standard interval widening: drops bounds that decrease/increase. -/
def widen (i1 i2 : Interval) : Interval :=
  match i1, i2 with
  | .bot, _ => i2
  | _, .bot => i1
  | .range l1 h1, .range l2 h2 =>
    let l' := if l2.leBool l1 = false then .neg_inf else l2
    let h' := if h1.leBool h2 = false then .pos_inf else h2
    mkInterval l' h'

def test_failure : String :=
  let i1 := Interval.range (.fin 0) (.fin 5)
  let i2 := Interval.range (.fin 0) (.fin 10)
  -- This line will cause a "failed to synthesize Decidable" error
  -- because Lean knows the definition of ≤ but not how to compute it.
  if (i1 ≤ i2) then
    "i1 is contained in i2"
  else
    "i1 is NOT contained in i2"


-- PROOFS
@[simp] lemma ExtendedInt.leBool_pos_inf (x : ExtendedInt) : x.leBool .pos_inf = true := by
  cases x <;> rfl

@[simp] lemma neg_inf_leBool (x : ExtendedInt) : ExtendedInt.neg_inf.leBool x = true := by
  cases x <;> rfl

@[simp] lemma ExtendedInt.le_max_left (a b : ExtendedInt) : a.leBool (a.max b) = true := by
  cases a <;> cases b <;> simp [max, leBool]

@[simp] lemma ExtendedInt.le_max_right (a b : ExtendedInt) : b.leBool (a.max b) = true := by
  cases a <;> cases b <;> simp [max, leBool]

@[simp] lemma ExtendedInt.min_le_left (a b : ExtendedInt) : (a.min b).leBool a = true := by
  cases a <;> cases b <;> simp [min, leBool]

@[simp] lemma ExtendedInt.min_le_right (a b : ExtendedInt) : (a.min b).leBool b = true := by
  cases a <;> cases b <;> simp [min, leBool]

#eval test_failure

#eval Interval.overlapsTrue (Interval.range (.fin (-32)) (.fin 5))

-- Test Joining [0, 5] and [7, 10]
#eval Interval.join (Interval.range (.fin 0) (.fin 5)) (Interval.range (.fin 7) (.fin 10))
-- Result: range (fin 0) (fin 10)
#eval Interval.meet (Interval.range (.fin 0) (.fin 5)) (Interval.range (.fin 3) (.fin 10))
-- Test Bottom behavior: bot ⊔ [0, 5] = [0, 5]
#eval Interval.join .bot (Interval.range (.fin 0) (.fin 5))
-- Result: range (fin 0) (fin 5)

-- Test the Containment operator: [0, 5] ≤ [0, 10]
#eval (Interval.range (.fin 0) (.fin 5)) ≤ (Interval.range (.fin 0) (.fin 10))
-- Result: true

#eval Interval.add (Interval.range (.fin 1) (.fin 5))  (Interval.range (.fin 2) (.fin 10))
-- Result: true

#check (Interval.range .neg_inf .pos_inf) -- Verify it's an Interval
#check decide (Interval.bot ≤ Interval.top) -- Verify it's a Bool
end Analyzer
