import Analyzer.State
import Analyzer.Concrete
import Batteries.Data.RBMap.Lemmas
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Algebra.Order.Group.Int

namespace Analyzer

-- ============================================================
-- 1. Concretization  γ : Interval → Set Int
-- ============================================================

/-- γ maps an abstract interval to the set of concrete integers it represents. -/
def γ (i : Interval) : Set Int :=
  match i with
  | .bot       => ∅
  | .range l h => { n : Int | l ≤ .fin n ∧ .fin n ≤ h }

theorem γ_bot : γ .bot = ∅ := rfl

theorem γ_top : γ .top = Set.univ := by
  ext n
  simp [γ, Interval.top, LE.le, ExtendedInt.leBool]

theorem γ_singleton (z : Int) : (z : Int) ∈ γ (.range (.fin z) (.fin z)) := by
  simp! [γ, LE.le, ExtendedInt.leBool]
  apply Int.le_refl

lemma ExtendedInt.le_iff_bool (a b : ExtendedInt) : a ≤ b ↔ a.leBool b = true := Iff.rfl

instance : Preorder ExtendedInt where
  le := (· ≤ ·)
  le_refl a := by
    cases a <;> simp! [LE.le, ExtendedInt.leBool]
    apply Int.le_refl
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;>
    simp! [LE.le, ExtendedInt.leBool] at *
    · -- Only the (fin x, fin y, fin z) case is interesting:
      apply Int.le_trans hab hbc

instance : Preorder Interval where
  le := (· ≤ ·)
  le_refl i := by
    cases i with
    | bot => simp! [LE.le, Interval.leBool]
    | range l h =>
      simp! [LE.le, Interval.leBool]
      -- This changes 'l.leBool l = true' back into 'l ≤ l'
      change l ≤ l ∧ h ≤ h
      constructor <;> apply le_refl
  le_trans i1 i2 i3 h12 h23 := by
    cases i1 <;> cases i2 <;> cases i3 <;>
    simp! [LE.le, Interval.leBool] at *
    constructor
    · -- Goal 1: Lower bound transitivity
      rw [← ExtendedInt.le_iff_bool]
      apply le_trans
      · rw [ExtendedInt.le_iff_bool]; exact h23.1
      · rw [ExtendedInt.le_iff_bool]; exact h12.1
    · -- Goal 2: Upper bound transitivity
      rw [← ExtendedInt.le_iff_bool]
      apply le_trans
      · rw [ExtendedInt.le_iff_bool]; exact h12.2
      · rw [ExtendedInt.le_iff_bool]; exact h23.2

/-- γ is monotone: i1 ⊑ i2 implies γ(i1) ⊆ γ(i2). -/
theorem γ_monotone : Monotone γ := by
  intro i1 i2 h n hn
  cases i1 with
  | bot => simp [γ] at hn
  | range l1 hi1 =>
    cases i2 with
    | bot => simp [LE.le, Interval.leBool] at h
    | range l2 hi2 =>
      simp! [γ] at hn
      simp! [LE.le, Interval.leBool, Bool.and_eq_true] at h
      exact ⟨le_trans h.1 hn.1, le_trans hn.2 h.2⟩

theorem mkInterval_wf (l u : ExtendedInt) : (mkInterval l u).is_wf := by
  simp! [mkInterval, Interval.is_wf]
  split
  · -- Case: l.leBool u = true
    trivial
  · -- Case: l.leBool u = false
    simp [Interval.is_wf]


/-
We need le_join_left (i1 ≤ i1.join i2) and le_join_right (i2 ≤ i1.join i2)
because they are the mathematical requirements for a Least Upper Bound.In  Galois Connection,
these two lemmas serve as the bridge between  Join operator and  Monotonicity theorem.
-/
theorem le_join_left (i1 i2 : Interval) (h1_wf : i1.is_wf) : i1 ≤ i1.join i2 := by
  cases i1 with
  | bot =>
    -- Case: bot ≤ bot ⊔ i2
    simp! [Interval.join, LE.le, Interval.leBool]
  | range l1 h1 =>
    -- Since i1 is a range, our 'wf' hypothesis tells us l1 ≤ h1
    simp! [Interval.is_wf] at h1_wf
    cases i2 with
    | bot =>
      -- Case: [l1, h1] ≤ [l1, h1] ⊔ bot
      simp! [Interval.join, LE.le, Interval.leBool]
      constructor <;> { rw [← ExtendedInt.le_iff_bool]; }
    | range l2 h2 =>
      -- Case: [l1, h1] ≤ [l1, h1] ⊔ [l2, h2]
      simp! [Interval.join]
      rw [mkInterval]
      split
      case isTrue h_join_valid =>
        -- This is the normal path where the join succeeded
        simp! [LE.le, Interval.leBool]
      case isFalse h_not_valid =>
        -- This is the "impossible" path where Lean thinks the join might be bot
        -- We prove it's a contradiction because l1 ≤ h1
        have h_actually_valid : (l1.min l2).leBool (h1.max h2) = true := by
          rw [← ExtendedInt.le_iff_bool]
          apply le_trans (ExtendedInt.min_le_left l1 l2)
          apply le_trans h1_wf (ExtendedInt.le_max_left h1 h2)
        -- Contradict the 'isFalse' assumption
        rw [h_actually_valid] at h_not_valid
        contradiction


theorem le_join_right (i1 i2 : Interval) (h2_wf : i2.is_wf) : i2 ≤ i1.join i2 := by
  cases i2 with
  | bot =>
    -- Case: bot ≤ i1 ⊔ bot
    simp! [Interval.join, LE.le, Interval.leBool]
  | range l2 h2 =>
    -- Since i2 is a range, our 'wf' hypothesis tells us l2 ≤ h2
    simp! [Interval.is_wf] at h2_wf
    cases i1 with
    | bot =>
      -- Case: [l2, h2] ≤ bot ⊔ [l2, h2]
      simp! [Interval.join, LE.le, Interval.leBool]
      constructor <;> { rw [← ExtendedInt.le_iff_bool]; }
    | range l1 h1 =>
      -- Case: [l2, h2] ≤ [l1, h1] ⊔ [l2, h2]
      simp! [Interval.join]
      rw [mkInterval]
      split
      case isTrue h_join_valid =>
        -- The normal path: [l2, h2] is contained in [min(l1, l2), max(h1, h2)]
        simp! [LE.le, Interval.leBool]
      case isFalse h_not_valid =>
        -- The impossible path: prove l2 ≤ h2 implies the join cannot be bot
        have h_actually_valid : (l1.min l2).leBool (h1.max h2) = true := by
          rw [← ExtendedInt.le_iff_bool]
          -- Chain: min ≤ l2 ≤ h2 ≤ max
          apply le_trans (ExtendedInt.min_le_right l1 l2)
          apply le_trans h2_wf (ExtendedInt.le_max_right h1 h2)
        -- Contradiction between h_not_valid (false) and h_actually_valid (true)
        rw [h_actually_valid] at h_not_valid
        contradiction

/-- γ of a join covers both arguments. -/
theorem γ_join_covers (i1 i2 : Interval) (hwf1 : i1.is_wf) (hwf2 : i2.is_wf) :
  γ i1 ∪ γ i2 ⊆ γ (i1.join i2) := by
  -- 1. Take an arbitrary integer x and the fact it's in the union
  intro x hx
  cases hx with
  | inl h1 =>
    -- We need to show x ∈ γ (i1.join i2)
    -- We use γ_monotone with the proof: i1 ≤ i1.join i2
    apply γ_monotone (le_join_left i1 i2 hwf1)
    exact h1
  | inr h2 =>
    -- We use γ_monotone with the proof: i2 ≤ i1.join i2
    apply γ_monotone (le_join_right i1 i2 hwf2)
    exact h2


-- ============================================================
-- 2. Abstraction  α : Set Int → Interval  (noncomputable)
-- ============================================================

/-- α maps a set of integers to the smallest enclosing interval. -/
noncomputable def α (S : Set Int) : Interval :=
  open Classical in
  if S = ∅ then .bot
  else
    let lo : ExtendedInt := if BddBelow S then .fin (sInf S) else .neg_inf
    let hi : ExtendedInt := if BddAbove S then .fin (sSup S) else .pos_inf
    mkInterval lo hi

theorem α_empty : α ∅ = .bot := by simp [α]

theorem α_singleton (z : Int) : α {z} = .range (.fin z) (.fin z) := by
  simp [α, mkInterval, ExtendedInt.leBool, BddBelow, BddAbove,
        csInf_singleton, csSup_singleton]

-- ============================================================
-- 3. Helper lemmas bridging α, γ, csInf, csSup
-- ============================================================

/-- For nonempty S the lower bound lo of α S is ≤ the upper bound hi,
    so mkInterval never produces ⊥ for a nonempty set. -/
private lemma α_lo_le_hi {S : Set Int} (hne : S.Nonempty) : open Classical in
    ExtendedInt.leBool
      (if BddBelow S then (.fin (sInf S) : ExtendedInt) else .neg_inf)
      (if BddAbove S then (.fin (sSup S) : ExtendedInt) else .pos_inf) = true := by
  obtain ⟨x, hx⟩ := hne
  apply le_trans (b := ExtendedInt.fin x)
  · case a =>
    split_ifs with hB
    · simp! [LE.le, ExtendedInt.leBool]
      apply csInf_le hB hx
    · simp! [LE.le, ExtendedInt.leBool]
  · case a =>
  -- Goal: ExtendedInt.fin x ≤ hi
  split_ifs with hB
  · -- Case: BddAbove S is true
    -- Supremum property: x ≤ sSup S for any x ∈ S
    simp! [LE.le, ExtendedInt.leBool]
    apply le_csSup hB hx
  · -- Case: BddAbove S is false
    -- hi is pos_inf. By definition, everything is ≤ +inf.
    simp [LE.le, ExtendedInt.leBool]


/-- The lower bound of α S is ≤ fin n for every n ∈ S. -/
private lemma α_lo_le_fin {S : Set Int} {n : Int} (hn : n ∈ S) : open Classical in
    (if BddBelow S then (.fin (sInf S) : ExtendedInt) else .neg_inf) ≤ .fin n := by
  split_ifs with hB
  · -- Case: BddBelow S
    -- Convert the boolean representation to logical inequality
    -- Apply the property of the Infimum: sInf S ≤ n for any n ∈ S
    simp only [LE.le, ExtendedInt.leBool, decide_eq_true_eq]
    apply csInf_le hB hn
  · -- Case: ¬BddBelow S
    -- The lower bound is neg_inf, which is ≤ everything by definition
    simp [LE.le, ExtendedInt.leBool]

/-- fin n ≤ the upper bound of α S for every n ∈ S. -/
private lemma fin_le_α_hi {S : Set Int} {n : Int} (hn : n ∈ S) : open Classical in
    (.fin n : ExtendedInt) ≤ (if BddAbove S then .fin (sSup S) else .pos_inf) := by
  split_ifs with hB
  · -- Case: BddAbove S
    simp only [LE.le, ExtendedInt.leBool, decide_eq_true_eq]
    apply le_csSup hB hn
  · -- Case: ¬BddAbove S
    simp [LE.le, ExtendedInt.leBool]

/-- Unit of the Galois connection: every n ∈ S belongs to γ(α S). -/
lemma mem_γ_α {S : Set Int} {n : Int} (hn : n ∈ S) : n ∈ γ (α S) := by
  have hne : S.Nonempty := ⟨n, hn⟩
  simp only [α, hne.ne_empty, ↓reduceIte, γ, mkInterval,
             if_pos (α_lo_le_hi hne), Set.mem_setOf_eq]
  exact ⟨α_lo_le_fin hn, fin_le_α_hi hn⟩

/-- From ∀ n ∈ S, l ≤ fin n, deduce l ≤ fin(sInf S) (l is a lower bound ≤ the infimum). -/
private lemma le_fin_csInf {S : Set Int} {l : ExtendedInt}
    (hne : S.Nonempty) (hbdd : BddBelow S)
    (hle : ∀ n ∈ S, l ≤ .fin n) : l ≤ .fin (sInf S) := by
  cases l with
  | neg_inf => simp [LE.le, ExtendedInt.leBool]
  | pos_inf =>
    exact absurd (hle _ hne.some_mem) (by simp [LE.le, ExtendedInt.leBool])
  | fin x =>
    simp only [LE.le, ExtendedInt.leBool, decide_eq_true_eq]
    exact le_csInf hne (fun b hb => by
      have h := hle b hb
      simp! [LE.le, ExtendedInt.leBool, decide_eq_true_eq] at h; exact h)

/-- From ∀ n ∈ S, fin n ≤ h, deduce fin(sSup S) ≤ h (the supremum ≤ any upper bound). -/
private lemma fin_csSup_le {S : Set Int} {h : ExtendedInt}
    (hne : S.Nonempty) (hbdd : BddAbove S)
    (hle : ∀ n ∈ S, (.fin n : ExtendedInt) ≤ h) : .fin (sSup S) ≤ h := by
  cases h with
  | pos_inf => simp [LE.le, ExtendedInt.leBool]
  | neg_inf =>
    exact absurd (hle _ hne.some_mem) (by simp [LE.le, ExtendedInt.leBool])
  | fin x =>
    simp only [LE.le, ExtendedInt.leBool, decide_eq_true_eq]
    exact csSup_le hne (fun b hb => by
      have h := hle b hb
      simp! [LE.le, ExtendedInt.leBool, decide_eq_true_eq] at h; exact h)

-- ============================================================
-- 4. The Galois Connection  α ⊣ γ
-- ============================================================

/-- The Galois connection: α(S) ≤ i ↔ S ⊆ γ(i) -/
theorem galois_connection (S : Set Int) (i : Interval) :
    α S ≤ i ↔ S ⊆ γ i := by
  constructor
  · -- Direction 1: α S ≤ i → S ⊆ γ i (Soundness)
    intro h_le n hn
    -- We know n ∈ γ(α S) from our previous lemma
    have h_in_best : n ∈ γ (α S) := mem_γ_α hn
    -- Since γ is monotone, α S ≤ i implies γ(α S) ⊆ γ i
    have h_mono := γ_monotone h_le
    exact h_mono h_in_best
  · -- Direction 2: S ⊆ γ i → α S ≤ i (Optimality)
    intro h_sub
    -- Case split on whether S is empty
    by_cases hS : S = ∅
    · -- Case: S is empty
      simp only  [hS, α_empty]
      -- Interval.bot is ≤ everything
      cases i <;> simp! [LE.le, Interval.leBool]
    · -- Case: S is not empty
      have hne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
      simp only [α, hS, ↓reduceIte]
      -- We now need to show [lo, hi] ≤ i
      cases i with
      | bot =>
        -- If i is bot, γ i is empty. S ⊆ ∅ implies S is empty, contradiction.
        simp! [γ_bot] at h_sub
        exact absurd h_sub (Set.nonempty_iff_ne_empty.mp hne)
      | range l h =>
        -- Main goal: mkInterval lo hi ≤ range l h
        -- First, prove the join check in mkInterval is 'true'
        have h_wf := α_lo_le_hi hne
        simp! [mkInterval, h_wf, LE.le, Interval.leBool]
        -- Now we have two subgoals: lo ≥ l and hi ≤ h
        constructor
        · -- Subgoal: lo ≥ l (which is l ≤ lo in Boolean form)
          -- This is where we use the optimality of Infimum
          split_ifs with hB
          · -- S is bounded below
            apply le_fin_csInf hne hB
            intro n hnS
            specialize h_sub hnS
            simp only [γ] at h_sub; exact h_sub.1
          · -- S is not bounded below
            -- If S is not bounded, but it's contained in range l h,
            -- then l MUST be neg_inf.
            by_contra h_cont
            cases l with
            | neg_inf => contradiction -- neg_inf is always ≤ lo
            | pos_inf => -- S ⊆ ∅ contradiction
              specialize h_sub hne.some_mem
              simp only [γ] at h_sub; cases h_sub.1
            | fin z =>
              -- If l is finite but S is not bounded below, contradiction.
                have h_bdd : BddBelow S := by
                  use z
                  intro n nh
                  specialize h_sub nh
                  simp! [γ, LE.le, ExtendedInt.leBool] at h_sub
                  exact h_sub.1
                contradiction
        · -- Subgoal: hi ≤ h
          split_ifs with hB
          · -- S is bounded above
            apply fin_csSup_le hne hB
            intro n hnS
            specialize h_sub hnS
            simp only [γ] at h_sub; exact h_sub.2
          · -- S is not bounded above
            -- Similar logic: if hi is pos_inf, then h must be pos_inf.
            cases h with
            | pos_inf => simp [ExtendedInt.leBool]
            | neg_inf => -- S ⊆ ∅ contradiction
              specialize h_sub hne.some_mem
              simp only [γ] at h_sub; cases h_sub.2
            | fin z =>
              have : BddAbove S := ⟨z, fun n hn => by
                specialize h_sub hn
                simp! [γ, LE.le, ExtendedInt.leBool] at h_sub
                exact h_sub.2⟩
              contradiction

#check galois_connection

/-- α is monotone: S ⊆ T implies α S ≤ α T. -/
theorem α_monotone : Monotone α := by
  intro S T hST
  -- Use the right-to-left direction (optimality) of the Galois connection
  rw [galois_connection]
  -- We need to show S ⊆ γ (α T)
  -- 1. We know T ⊆ γ (α T) from our Soundness proof (mem_γ_α)
  have hT_sub_γ : T ⊆ γ (α T) := by
    intro x hx
    apply mem_γ_α hx
  -- 2. Since S ⊆ T and T ⊆ γ (α T), by transitivity S ⊆ γ (α T)
  exact Set.Subset.trans hST hT_sub_γ

-- ============================================================
-- 4. Store and Config simulation relations
-- ============================================================

/-- storeSim: every concrete int value is within the abstract interval at that address. -/
def storeSim (cs : Concrete.Store) (as_ : Store) : Prop :=
  ∀ addr v, cs.find? addr = some (.vInt v) →
    ∃ iv, as_.find? addr = some (.vInt iv) ∧ v ∈ γ iv

/-- Continuations are shared structurally between concrete and abstract configs. -/
structure ConfigSim (c : Concrete.Config) (a : Config) : Prop where
  sameStmt : c.stmt  = a.stmt
  sameEnv  : c.env   = a.env
  sameKptr : c.kptr  = a.kptr
  sim      : storeSim c.store a.store
  kontSim  : ∀ addr k, c.store.find? addr = some (.vKont k) ↔
                        a.store.find? addr = some (.vKont k)

-- ============================================================
-- 5. Abstract arithmetic soundness
-- ============================================================

theorem ExtendedInt.add_le_add {a b c d : ExtendedInt} (h1 : a ≤ b) (h2 : c ≤ d)
 : a.add c ≤ b.add d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
  simp! [LE.le, ExtendedInt.leBool, ExtendedInt.add] at *
  -- Most cases involving infinity resolve automatically via simp!
  -- because anything + pos_inf is pos_inf, etc.
  case fin.fin.fin.fin x1 x2 x3 x4 =>
    -- This is the core case for concrete integers
    apply Int.add_le_add h1 h2


theorem ExtendedInt.sub_le_sub {a b c d : ExtendedInt} (h1 : a ≤ b) (h2 : d ≤ c)
  : a.sub c ≤ b.sub d := by
  -- 1. Unfold the LE instance so Lean sees 'leBool'
  simp only [LE.le] at *
  -- 2. Use induction to check every combination of -inf, fin, +inf
  induction a <;> induction b <;> induction c <;> induction d
  -- 3. all_goals handles all 81 cases!
  -- Most are solved by the definitions of sub and leBool
  all_goals
    simp! [sub, leBool] at *
    try contradiction
  -- 4. Solve the remaining finite integer case
  case fin.fin.fin.fin x1 x2 y1 y2 =>
    -- Lean's 'decide' translates the Bool back to Int Prop
    linarith


/-- Abstract addition is sound: v1 ∈ γ(i1) ∧ v2 ∈ γ(i2) → v1+v2 ∈ γ(i1.add i2) -/
theorem add_sound (i1 i2 : Interval) (v1 v2 : Int)
    (h1 : v1 ∈ γ i1) (h2 : v2 ∈ γ i2) : v1 + v2 ∈ γ (i1.add i2) := by
  -- Step 1: Handle the .bot cases
  cases i1 with
  | bot =>
    simp [γ] at h1
  | range l1 hi1 =>
    cases i2 with
    | bot =>
      simp [γ] at h2
    | range l2 hi2 =>
      -- Step 2: Extract concrete bounds
      simp only [γ, Set.mem_setOf_eq] at h1 h2
      obtain ⟨hl1, hh1⟩ := h1
      obtain ⟨hl2, hh2⟩ := h2
      -- Step 3: Prove the condition for mkInterval
      have h_wf : (l1.add l2).leBool (hi1.add hi2) = true := by
        rw [← ExtendedInt.le_iff_bool]
        apply le_trans (ExtendedInt.add_le_add hl1 hl2) (ExtendedInt.add_le_add hh1 hh2)
      -- Step 4: Force the simplification of Interval.add and mkInterval
      -- We use 'unfold' to break the match, then 'simp' to use h_wf
      unfold Interval.add mkInterval
      split
      · -- This case handles the .bot branches (which are impossible here)
        contradiction
      · -- This case handles the range/range branch
        -- Use your h_wf to resolve the 'if' statement inside the match
        rename_i h_if
        aesop
      · rename_i l1_int h1_int l2_int h2_int heq1 heq2
        injection heq1 with hl1_eq hh1_eq
        injection heq2 with hl2_eq hh2_eq
        subst hl1_eq hh1_eq hl2_eq hh2_eq
        split
        · -- Branch where the if-condition is true
          simp only [γ, Set.mem_setOf_eq]
          constructor
          · exact ExtendedInt.add_le_add hl1 hl2
          · exact ExtendedInt.add_le_add hh1 hh2
        · -- Branch where the if-condition is false (Contradiction)
          rename_i h_if_false
          -- The goal shows (l1 + l2).leBool ... = true, but h_if_false says false
         -- We unify them using h_wf
          have h_true : (l1.add l2).leBool (hi1.add hi2) = true := h_wf
          contradiction

/-- Abstract subtraction is sound: v1 ∈ γ(i1) ∧ v2 ∈ γ(i2) → v1-v2 ∈ γ(i1.sub i2) -/
theorem sub_sound (i1 i2 : Interval) (v1 v2 : Int)
    (h1 : v1 ∈ γ i1) (h2 : v2 ∈ γ i2) : v1 - v2 ∈ γ (i1.sub i2) := by
  cases i1 <;> cases i2 <;> simp! [Interval.sub, γ] at *
  case range.range l1 hi1 l2 hi2 =>
    have h_is_wf : (l1.sub hi2).leBool (hi1.sub l2) = true := by
      rw [← ExtendedInt.le_iff_bool]
      exact le_trans (ExtendedInt.sub_le_sub h1.left h2.right)
                     (ExtendedInt.sub_le_sub h1.right h2.left)
    simp only [mkInterval, h_is_wf, ite_true]
    exact ⟨ExtendedInt.sub_le_sub h1.left h2.right,
           ExtendedInt.sub_le_sub h1.right h2.left⟩

-- ============================================================
-- 6. Abstract evalExpr soundness
-- ============================================================

/-- Abstract expression evaluation is sound w.r.t. concrete evaluation. -/
theorem evalExpr_sound (e : Expr)
    (cEnv : Concrete.Env) (cStore : Concrete.Store)
    (aEnv : Env) (aStore : Store)
    (hEnv : cEnv = aEnv)
    (hStore : storeSim cStore aStore)
    (v : Int) (hEval : Concrete.evalExpr e cEnv cStore = some v) :
    v ∈ γ (evalExpr e aEnv aStore) := by
  -- Revert so the IH quantifies over the result value
  revert v hEval
  induction e with
  | const n =>
    intro v hEval
    simp! [Concrete.evalExpr] at hEval
    subst hEval
    exact γ_singleton n
  | var x =>
    intro v hEval
    simp only [Concrete.evalExpr] at hEval
    rw [hEnv] at hEval
    simp only [evalExpr]
    cases haEnv : aEnv.find? x with
    | none => simp [haEnv] at hEval
    | some addr =>
      simp only [haEnv] at hEval ⊢
      cases hcStore : cStore.find? addr with
      | none => simp [hcStore] at hEval
      | some cv =>
        cases cv with
        | vKont k => simp [hcStore] at hEval
        | vInt n =>
          simp only [hcStore] at hEval
          obtain ⟨iv, hiv_find, hiv_mem⟩ := hStore addr n hcStore
          have hn : n = v := Option.some.inj hEval
          subst hn
          simp only [hiv_find]
          exact hiv_mem
  | add e1 e2 ih1 ih2 =>
    intro v hEval
    simp only [Concrete.evalExpr] at hEval
    change v ∈ γ ((evalExpr e1 aEnv aStore).add (evalExpr e2 aEnv aStore))
    cases h1 : Concrete.evalExpr e1 cEnv cStore with
    | none => simp [h1] at hEval
    | some v1 =>
      cases h2 : Concrete.evalExpr e2 cEnv cStore with
      | none => simp [h1, h2] at hEval
      | some v2 =>
        simp only [h1, h2] at hEval
        obtain rfl : v1 + v2 = v := Option.some.inj hEval
        exact add_sound _ _ _ _ (ih1 v1 h1) (ih2 v2 h2)
  | sub e1 e2 ih1 ih2 =>
    intro v hEval
    simp only [Concrete.evalExpr] at hEval
    change v ∈ γ ((evalExpr e1 aEnv aStore).sub (evalExpr e2 aEnv aStore))
    cases h1 : Concrete.evalExpr e1 cEnv cStore with
    | none => simp [h1] at hEval
    | some v1 =>
      cases h2 : Concrete.evalExpr e2 cEnv cStore with
      | none => simp [h1, h2] at hEval
      | some v2 =>
        simp only [h1, h2] at hEval
        obtain rfl : v1 - v2 = v := Option.some.inj hEval
        exact sub_sound _ _ _ _ (ih1 v1 h1) (ih2 v2 h2)

-- ============================================================
-- 7. Local Soundness Theorem
-- ============================================================


/-- storeSim is preserved when both stores get a consistent update at `addr`:
    concrete writes `v`, abstract joins in `iv_new`. -/
lemma storeSim_after_join
    (cs : Concrete.Store) (as_ : Store) (addr : Addr) (v : Int) (iv_new : Interval)
    (hv : v ∈ γ iv_new)
    (hSim : storeSim cs as_) :
    storeSim (cs.insert addr (.vInt v))
             (as_.insert addr (.vInt (iv_new.join
                (match as_.find? addr with | some (.vInt old) => old | _ => .bot)))) := by
  intro a w hw
  by_cases ha : a = addr
  · -- Same address: both inserts fire; the join contains iv_new ⊇ {v}.
    subst ha
    have h_eq : compare a a = .eq := Std.ReflCmp.compare_self
    rw [Batteries.RBMap.find?_insert_of_eq _ h_eq] at hw
    -- hw : some (.vInt v) = some (.vInt w)
    have hwv : w = v := by
      injection hw with h1
      injection h1
      aesop
    subst hwv
    have hiv_wf : iv_new.is_wf := by
      cases iv_new with
      | bot => simp [γ] at hv
      | range l h =>
        simp only [Interval.is_wf, γ, Set.mem_setOf_eq] at hv ⊢
        exact le_trans hv.left hv.right
    refine ⟨iv_new.join (match as_.find? a with | some (.vInt o) => o | _ => .bot), ?_, ?_⟩
    · exact Batteries.RBMap.find?_insert_of_eq _ h_eq
    · exact γ_monotone (le_join_left iv_new _ hiv_wf) hv
  · -- Different address: both inserts are invisible; fall through to hSim.
    have h_ne : compare a addr ≠ .eq :=
      fun heq => ha (Std.LawfulEqOrd.eq_of_compare heq)
    rw [Batteries.RBMap.find?_insert_of_ne _ h_ne] at hw
    obtain ⟨iv, hiv, hmem⟩ := hSim a w hw
    exact ⟨iv, by rw [Batteries.RBMap.find?_insert_of_ne _ h_ne]; exact hiv, hmem⟩

/-- Inserting a vInt in both stores at the same address preserves kontSim. -/
lemma kontSim_preserved_vint
    (cs : Concrete.Store) (as_ : Store) (addr : Addr)
    (v : Int) (iv : Interval)
    (hK : ∀ a k, cs.find? a = some (.vKont k) ↔ as_.find? a = some (.vKont k)) :
    ∀ a k, (cs.insert addr (.vInt v)).find? a = some (.vKont k) ↔
            (as_.insert addr (.vInt iv)).find? a = some (.vKont k) := by
  intro a k
  by_cases ha : a = addr
  · subst ha
    have h_eq : compare a a = .eq := Std.ReflCmp.compare_self
    simp [Batteries.RBMap.find?_insert_of_eq _ h_eq]
  · have h_ne : compare a addr ≠ .eq :=
      fun heq => ha (Std.LawfulEqOrd.eq_of_compare heq)
    rw [Batteries.RBMap.find?_insert_of_ne _ h_ne,
        Batteries.RBMap.find?_insert_of_ne _ h_ne]
    exact hK a k

/-- Inserting the same vKont k at the same address in both stores preserves kontSim. -/
lemma kontSim_after_kont_insert
    (cs : Concrete.Store) (as_ : Store) (addr : Addr) (k : Kont)
    (hK : ∀ a k', cs.find? a = some (.vKont k') ↔ as_.find? a = some (.vKont k')) :
    ∀ a k', (cs.insert addr (.vKont k)).find? a = some (.vKont k') ↔
             (as_.insert addr (.vKont k)).find? a = some (.vKont k') := by
  intro a k'
  by_cases ha : a = addr
  · subst ha
    have h_eq : compare a a = .eq := Std.ReflCmp.compare_self
    simp [Batteries.RBMap.find?_insert_of_eq _ h_eq]
  · have h_ne : compare a addr ≠ .eq :=
      fun heq => ha (Std.LawfulEqOrd.eq_of_compare heq)
    rw [Batteries.RBMap.find?_insert_of_ne _ h_ne,
        Batteries.RBMap.find?_insert_of_ne _ h_ne]
    exact hK a k'

/-- Inserting a vKont in both stores (same kont, same address) preserves storeSim. -/
lemma storeSim_preserved_kont
    (cs : Concrete.Store) (as_ : Store) (addr : Addr) (k : Kont)
    (hSim : storeSim cs as_) :
    storeSim (cs.insert addr (.vKont k)) (as_.insert addr (.vKont k)) := by
  intro a v hav
  by_cases ha : a = addr
  · subst ha
    have h_eq : compare a a = .eq := Std.ReflCmp.compare_self
    rw [Batteries.RBMap.find?_insert_of_eq _ h_eq] at hav
    simp at hav
  · have h_ne : compare a addr ≠ .eq :=
      fun heq => ha (Std.LawfulEqOrd.eq_of_compare heq)
    rw [Batteries.RBMap.find?_insert_of_ne _ h_ne] at hav
    obtain ⟨iv, hiv, hmem⟩ := hSim a v hav
    exact ⟨iv, by rw [Batteries.RBMap.find?_insert_of_ne _ h_ne]; exact hiv, hmem⟩

/-- If v ≠ 0 and v ∈ γ iv, then the abstract interval overlaps the true (non-zero) region. -/
theorem overlapsTrue_of_nonzero_mem {iv : Interval} {v : Int}
    (hv : v ∈ γ iv) (hne : v ≠ 0) : iv.overlapsTrue = true := by
  cases iv with
  | bot => simp [γ] at hv
  | range lo hi =>
    simp only [γ, Set.mem_setOf_eq] at hv
    by_contra h_f
    -- h_f : ¬(overlapsTrue = true), i.e., lo == fin 0 && hi == fin 0 = true
    simp only [Bool.not_eq_true', Interval.overlapsTrue,
               Bool.not_eq_false, Bool.and_eq_true] at h_f
    obtain ⟨hlo, hhi⟩ := h_f
    cases lo with
    | neg_inf => exact absurd hlo (by decide)
    | pos_inf => exact absurd hlo (by decide)
    | fin x =>
      cases hi with
      | neg_inf => exact absurd hhi (by decide)
      | pos_inf => exact absurd hhi (by decide)
      | fin y =>
        simp only [LE.le, ExtendedInt.leBool, decide_eq_true_eq] at hv
        -- derived BEq: fin x == fin 0 is definitionally (x == 0 : Int)
        have hx : x = 0 := by
          change (x == (0 : Int)) = true at hlo
          exact beq_iff_eq.mp hlo
        have hy : y = 0 := by
          change (y == (0 : Int)) = true at hhi
          exact beq_iff_eq.mp hhi
        subst hx; subst hy
        exact hne (Int.le_antisymm hv.2 hv.1)

/-- If 0 ∈ γ iv, then the abstract interval overlaps the false (zero) region. -/
theorem overlapsFalse_of_zero_mem {iv : Interval}
    (hv : (0 : Int) ∈ γ iv) : iv.overlapsFalse = true := by
  cases iv with
  | bot => simp [γ] at hv
  | range l h =>
    simp only [γ, Set.mem_setOf_eq] at hv
    simp only [Interval.overlapsFalse, Bool.and_eq_true]
    exact ⟨hv.1, hv.2⟩

/-- Local soundness: every concrete step is simulated by some abstract step. -/
theorem step_local_sound
    (c : Concrete.Config) (a : Config) (hSim : ConfigSim c a)
    (c' : Concrete.Config) (hStep : Concrete.step c = some c') :
    ∃ a' ∈ step a, ConfigSim c' a' := by
  cases hc : c.stmt with
  | assign x e =>
    simp only [Concrete.step, hc] at hStep
    -- Case split on each nested match in the concrete step
    cases heval : Concrete.evalExpr e c.env c.store with
    | none => simp [heval] at hStep
    | some v =>
      simp only [heval] at hStep
      cases haddr : c.env.find? x with
      | none => simp [haddr] at hStep
      | some addr =>
        simp only [haddr] at hStep
        cases hkont : c.store.find? c.kptr with
        | none => simp [hkont] at hStep
        | some sv =>
          cases sv with
          | vInt _ => simp [hkont] at hStep
          | vKont k =>
            cases k with
            | kDone     => simp [hkont] at hStep
            | kWhile _ _ _ => simp [hkont] at hStep
            | kSeq next s_next =>
              simp only [hkont] at hStep
              -- Pin down c' from hStep
              have hc'eq := Option.some.inj hStep
              subst hc'eq
              -- Abstract side facts
              have haStmt : a.stmt = .assign x e :=
                hSim.sameStmt.symm.trans hc
              have hv_mem : v ∈ γ (evalExpr e a.env a.store) :=
                evalExpr_sound e c.env c.store a.env a.store hSim.sameEnv hSim.sim v heval
              have ha_addr : a.env.find? x = some addr :=
                hSim.sameEnv ▸ haddr
              have ha_kont : a.store.find? a.kptr = some (.vKont (.kSeq next s_next)) := by
                rw [← hSim.sameKptr]
                exact (hSim.kontSim c.kptr (.kSeq next s_next)).mp hkont
              -- Abstract interval values for the assign update
              let iv_new : Interval := evalExpr e a.env a.store
              let oldVal : Interval :=
              (match a.store.find? addr with | some (.vInt i) => i | _ => Interval.bot)
              -- Provide the abstract witness config via 'use' to avoid ⟨{...}⟩ parse issues
              use { a with stmt := next, store :=
              a.store.insert addr (.vInt (iv_new.join oldVal)), kptr := s_next }
              refine ⟨?_, ?_⟩
              · -- Membership in abstract step
                simp [step, haStmt, ha_addr, ha_kont]; rfl
              · -- Simulation is preserved
                refine ⟨rfl, hSim.sameEnv, rfl, ?_, ?_⟩
                · exact storeSim_after_join c.store a.store addr v iv_new hv_mem hSim.sim
                · exact kontSim_preserved_vint
                   c.store a.store addr v (iv_new.join oldVal) hSim.kontSim
  | seq s1 s2 =>
    simp only [Concrete.step, hc] at hStep
    have hc'eq := Option.some.inj hStep
    subst hc'eq
    have haStmt : a.stmt = .seq s1 s2 := hSim.sameStmt.symm.trans hc
    let kAddr := Addr.mk ("k_" ++ toString (hash s2))
    use { a with stmt := s1, store :=
    a.store.insert kAddr (.vKont (.kSeq s2 a.kptr)), kptr := kAddr }
    refine ⟨?_, ?_⟩
    · simp! [step, haStmt]; exact ⟨rfl, rfl⟩
    · refine ⟨rfl, hSim.sameEnv, rfl, ?_, ?_⟩
      · rw [hSim.sameKptr]
        exact storeSim_preserved_kont c.store a.store kAddr (.kSeq s2 a.kptr) hSim.sim
      · rw [hSim.sameKptr]
        exact kontSim_after_kont_insert c.store a.store kAddr (.kSeq s2 a.kptr) hSim.kontSim
  | «while» e body =>
    simp only [Concrete.step, hc] at hStep
    have haStmt : a.stmt = .while e body := hSim.sameStmt.symm.trans hc
    cases heval : Concrete.evalExpr e c.env c.store with
    | none => simp [heval] at hStep
    | some v =>
      simp only [heval] at hStep
      by_cases hne : v ≠ 0
      · -- True branch: concrete enters loop body
        simp! [hne, ite_true] at hStep
        subst hStep
        have hv_mem : v ∈ γ (evalExpr e a.env a.store) :=
          evalExpr_sound e c.env c.store a.env a.store hSim.sameEnv hSim.sim v heval
        have hTrue : (evalExpr e a.env a.store).overlapsTrue = true :=
          overlapsTrue_of_nonzero_mem hv_mem hne
        -- Use a.stmt (= c.stmt) so kAddr matches the abstract step's kWhileAddr
        let kAddr := Addr.mk ("k_while_" ++ toString (hash a.stmt))
        use { a with stmt := body, store :=
        a.store.insert kAddr (.vKont (.kWhile e body a.kptr)), kptr := kAddr }
        have hkAddr : kAddr = Addr.mk ("k_while_" ++ toString (hash (Stmt.while e body))) := by
          change Addr.mk ("k_while_" ++ toString (hash a.stmt)) =
               Addr.mk ("k_while_" ++ toString (hash (Stmt.while e body)))
          rw [haStmt]
        refine ⟨?_, ?_⟩
        · simp! [step, haStmt, hTrue]; left;
          exact ⟨by rw [hkAddr], hkAddr⟩
        · refine ⟨rfl, hSim.sameEnv, hkAddr.symm, ?_, ?_⟩
          · rw [← hkAddr, hSim.sameKptr]
            exact storeSim_preserved_kont c.store a.store kAddr (.kWhile e body a.kptr) hSim.sim
          · rw [← hkAddr, hSim.sameKptr]
            exact kontSim_after_kont_insert
              c.store a.store kAddr (.kWhile e body a.kptr) hSim.kontSim
      · -- False branch: concrete exits loop
        rw [if_neg hne] at hStep
        have hv0 : v = 0 := by omega
        have hv_mem : v ∈ γ (evalExpr e a.env a.store) :=
          evalExpr_sound e c.env c.store a.env a.store hSim.sameEnv hSim.sim v heval
        have hFalse : (evalExpr e a.env a.store).overlapsFalse = true :=
          overlapsFalse_of_zero_mem (hv0 ▸ hv_mem)
        cases hkont : c.store.find? c.kptr with
        | none => simp [hkont] at hStep
        | some sv =>
          cases sv with
          | vInt _ => simp [hkont] at hStep
          | vKont k =>
            cases k with
            | kDone => simp [hkont] at hStep
            | kWhile _ _ _ => simp [hkont] at hStep
            | kSeq next s_next =>
              simp only [hkont] at hStep
              have hc'eq := Option.some.inj hStep
              subst hc'eq
              have ha_kont : a.store.find? a.kptr = some (.vKont (.kSeq next s_next)) := by
                rw [← hSim.sameKptr]
                exact (hSim.kontSim c.kptr (.kSeq next s_next)).mp hkont
              use { a with stmt := next, kptr := s_next }
              refine ⟨?_, ?_⟩
              · simp [step, haStmt, hFalse, ha_kont]
              · exact ⟨rfl, hSim.sameEnv, rfl, hSim.sim, hSim.kontSim⟩
  | skip =>
    simp only [Concrete.step, hc] at hStep
    have haStmt : a.stmt = .skip := hSim.sameStmt.symm.trans hc
    cases hkont : c.store.find? c.kptr with
    | none => simp [hkont] at hStep
    | some sv =>
      cases sv with
      | vInt _ => simp [hkont] at hStep
      | vKont k =>
        cases k with
        | kDone => simp [hkont] at hStep
        | kWhile e body s_exit =>
          simp only [hkont] at hStep
          have hc'eq := Option.some.inj hStep
          subst hc'eq
          have ha_kont : a.store.find? a.kptr = some (.vKont (.kWhile e body s_exit)) := by
            rw [← hSim.sameKptr]
            exact (hSim.kontSim c.kptr (.kWhile e body s_exit)).mp hkont
          use { a with stmt := .while e body, kptr := s_exit }
          refine ⟨?_, ?_⟩
          · simp [step, haStmt, ha_kont]
          · exact ⟨rfl, hSim.sameEnv, rfl, hSim.sim, hSim.kontSim⟩
        | kSeq next s_next =>
          simp only [hkont] at hStep
          have hc'eq := Option.some.inj hStep
          subst hc'eq
          have ha_kont : a.store.find? a.kptr = some (.vKont (.kSeq next s_next)) := by
            rw [← hSim.sameKptr]
            exact (hSim.kontSim c.kptr (.kSeq next s_next)).mp hkont
          use { a with stmt := next, kptr := s_next }
          refine ⟨?_, ?_⟩
          · simp [step, haStmt, ha_kont]
          · exact ⟨rfl, hSim.sameEnv, rfl, hSim.sim, hSim.kontSim⟩
  | ite e s1 s2 =>
    have haStmt : a.stmt = .ite e s1 s2 := hSim.sameStmt.symm.trans hc
    cases heval : Concrete.evalExpr e c.env c.store with
    | none =>
      have : Concrete.step c = none := by simp [Concrete.step, hc, heval]
      rw [this] at hStep; exact absurd hStep (by simp)
    | some v =>
      by_cases hne : v ≠ 0
      · -- True branch: concrete jumps to s1
        have hcStep : Concrete.step c = some { c with stmt := s1 } := by
          simp [Concrete.step, hc, heval, hne]
        rw [hcStep] at hStep
        have hc'eq := Option.some.inj hStep
        subst hc'eq
        have hv_mem : v ∈ γ (evalExpr e a.env a.store) :=
          evalExpr_sound e c.env c.store a.env a.store hSim.sameEnv hSim.sim v heval
        have hTrue : (evalExpr e a.env a.store).overlapsTrue = true :=
          overlapsTrue_of_nonzero_mem hv_mem hne
        use { a with stmt := s1 }
        exact ⟨by simp [step, haStmt, hTrue],
               ⟨rfl, hSim.sameEnv, hSim.sameKptr, hSim.sim, hSim.kontSim⟩⟩
      · -- False branch: concrete jumps to s2
        have hv0 : v = 0 := by omega
        have hcStep : Concrete.step c = some { c with stmt := s2 } := by
          simp [Concrete.step, hc, heval, show ¬(v ≠ 0) from hne]
        rw [hcStep] at hStep
        have hc'eq := Option.some.inj hStep
        subst hc'eq
        have hv_mem : v ∈ γ (evalExpr e a.env a.store) :=
          evalExpr_sound e c.env c.store a.env a.store hSim.sameEnv hSim.sim v heval
        have hFalse : (evalExpr e a.env a.store).overlapsFalse = true :=
          overlapsFalse_of_zero_mem (hv0 ▸ hv_mem)
        use { a with stmt := s2 }
        exact ⟨by simp [step, haStmt, hFalse],
               ⟨rfl, hSim.sameEnv, hSim.sameKptr, hSim.sim, hSim.kontSim⟩⟩

/-- Abstract reachability: `Reachable a a'` means `a'` is reachable from `a`
    by zero or more abstract steps. -/
inductive Reachable : Config → Config → Prop where
  | refl  {a}           : Reachable a a
  | trans {a a' a''}    : a' ∈ step a → Reachable a' a'' → Reachable a a''

/-- Global soundness: if `c` simulates `a` and `c` big-steps to `c'`,
    then some abstract state `a'` is reachable from `a` that simulates `c'`. -/
theorem global_soundness
    (c : Concrete.Config) (a : Config) (hSim : ConfigSim c a)
    (c' : Concrete.Config) (hEval : Concrete.BigStep c c') :
    ∃ a', Reachable a a' ∧ ConfigSim c' a' := by
  revert a
  induction hEval with
  | done _ => intro a hSim; exact ⟨a, .refl, hSim⟩
  | step hStep _ ih =>
    intro a hSim
    obtain ⟨a_mid, ha_mid, hSim_mid⟩ := step_local_sound _ a hSim _ hStep
    obtain ⟨a', hReach, hSim'⟩ := ih a_mid hSim_mid
    exact ⟨a', .trans ha_mid hReach, hSim'⟩

/-- Widening is sound: it always over-approximates the join. -/
lemma join_is_wf (i1 i2 : Interval) (h1 : i1.is_wf) (h2 : i2.is_wf) : (i1.join i2).is_wf := by
  cases i1 with
  | bot => exact h2
  | range l1 u1 =>
    simp only [Interval.is_wf] at h1
    cases i2 with
    | bot => exact h1
    | range l2 u2 =>
      simp only [Interval.is_wf] at h2
      simp only [Interval.join, mkInterval]
      split_ifs with hif
      · exact le_trans (le_trans (ExtendedInt.min_le_left l1 l2) h1) (ExtendedInt.le_max_left u1 u2)
      · exact True.intro

lemma widen_is_wf (i1 i2 : Interval) (h1 : i1.is_wf) (h2 : i2.is_wf) : (widen i1 i2).is_wf := by
  cases i1 with
  | bot => exact h2
  | range l1 u1 =>
    simp only [Interval.is_wf] at h1
    cases i2 with
    | bot => exact h1
    | range l2 u2 =>
      simp only [Interval.is_wf] at h2
      simp only [widen, mkInterval]
      by_cases h_l : l2.leBool l1 = false
      · by_cases h_h : u1.leBool u2 = false
        · simp [h_l, h_h, Interval.is_wf]
          exact neg_inf_leBool _
        · simp [h_l, h_h, Interval.is_wf]
          exact neg_inf_leBool _
      · by_cases h_h : u1.leBool u2 = false
        · simp [h_l, h_h, Interval.is_wf]
          exact ExtendedInt.leBool_pos_inf _
        · -- Case: l2.leBool l1 = true and u1.leBool u2 = true
          push_neg at h_l h_h
          -- Convert ≠ false to = true for simp
          have h_l_eq : l2.leBool l1 = true := by
            cases l2 <;> cases l1 <;> simp [ExtendedInt.leBool] at h_l ⊢ <;> omega
          have h_h_eq : u1.leBool u2 = true := by
            cases u1 <;> cases u2 <;> simp [ExtendedInt.leBool] at h_h ⊢ <;> omega
          -- Rewrite the conditions and simplify the ifs
          rw [h_l_eq, h_h_eq]
          -- Now the goal has (if true = false then ... else ...) which should simplify
          simp
          -- After simp, the goal is (if l2.leBool u2 = true then ...).is_wf
          -- We have h2 : l2 ≤ u2, which means l2.leBool u2 = true
          have : l2.leBool u2 = true := by
            simp [LE.le] at h2
            exact h2
          simp [this, Interval.is_wf]
          exact h2

theorem widen_sound (i1 i2 : Interval) : i1.join i2 ≤ widen i1 i2 := by
  cases i1 <;> cases i2 <;> simp! [Interval.join, widen, LE.le, Interval.leBool] at *
  · rw [← ExtendedInt.le_iff_bool, ← ExtendedInt.le_iff_bool]
    aesop
  · rw [← ExtendedInt.le_iff_bool, ← ExtendedInt.le_iff_bool]
    aesop
  · rename_i l1 h1 l2 h2
    have min_eq : ∀ (a b : ExtendedInt), b.leBool a = true → a.min b = b := by
      intro a b h
      cases a <;> cases b <;> simp_all [ExtendedInt.min, ExtendedInt.leBool]
    have max_eq : ∀ (a b : ExtendedInt), a.leBool b = true → a.max b = b := by
      intro a b h
      cases a <;> cases b <;> simp_all [ExtendedInt.max, ExtendedInt.leBool]
    have le_refl_bool : ∀ x : ExtendedInt, x.leBool x = true := fun x => le_refl x
    rcases Bool.eq_false_or_eq_true (l2.leBool l1) with hl | hl <;>
    rcases Bool.eq_false_or_eq_true (h1.leBool h2) with hh | hh <;>
    simp only [ mkInterval, hl, hh, ↓reduceIte] <;>
    split_ifs with hj <;>
    simp_all [Interval.leBool, ExtendedInt.leBool]
    · exact ExtendedInt.leBool_pos_inf _
    · cases l2 <;> simp_all
    · exact ExtendedInt.leBool_pos_inf _


end Analyzer
