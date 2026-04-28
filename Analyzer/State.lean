import Batteries.Data.RBMap.Basic
import Analyzer.Domain
import Analyzer.Syntax

namespace Analyzer
open Batteries

  /-
    1. Addresses (Addr)
    In a basic 0-CFA abstract machine, we map variable names directly to
    addresses. We also use Strings to generate unique addresses for our continuations.
  -/
structure Addr where
    id : String
    deriving BEq, Repr, Ord
  -- Mapping for the Environment and Store
 @[simp]
  lemma Addr.beq_eq (a b : Addr) : (a == b) = (a.id == b.id) := by
    unfold BEq.beq
    unfold instBEqAddr
    rfl

@[simp]
  lemma Addr.compare_eq (a b : Addr) : compare a b = compare a.id b.id := by
    cases a; cases b
    simp [compare, instOrdAddr.ord, Ordering.then_eq]

@[simp]
  lemma Addr.compare_def (id1 id2 : String) :
    compare ({ id := id1 } : Addr) { id := id2 } = compare id1 id2 := by
    simp [Addr.compare_eq]

  -- Lift TransOrd/LawfulEqOrd from String through the single-field wrapper Addr.
  -- This unblocks the Batteries find?_insert lemmas.
instance : Std.LawfulEqOrd Addr where
    eq_of_compare {a b} h := by
      rw [Addr.compare_eq] at h
      have hid : a.id = b.id := Std.LawfulEqOrd.eq_of_compare h
      cases a; cases b; cases hid; rfl
    -- The field you were missing:
    compare_self := by
      intro a
      rw [Addr.compare_eq]
      simp

instance : Std.TransOrd Addr where
    isLE_trans := fun hab hbc => by
      rw [Addr.compare_eq] at hab hbc
      rw [Addr.compare_eq]
      exact Std.TransCmp.isLE_trans (cmp := compare) hab hbc
    eq_swap := by
      intro a b
      rw [Addr.compare_eq a b, Addr.compare_eq b a]
      exact Std.OrientedOrd.eq_swap
  /-
    2. The 'K' in CESK: Continuations (The Stack)
    Instead of a recursive call, we store "what to do next."
    Note that `kSeq` and `kWhile` hold an `Addr` pointing to the REST of the stack.
  -/

inductive Kont where
    | kDone : Kont
    | kSeq : Stmt → Addr → Kont
    | kWhile : Expr → Stmt → Addr → Kont
    deriving BEq, Repr

inductive StoreVal where
    | vInt  : Interval → StoreVal
    | vKont : Kont → StoreVal
    deriving BEq, Repr


def Env := RBMap String Addr compare
def Store := RBMap Addr StoreVal compare

  -- Provide Repr for RBMap by converting to List
instance : Repr Env where
    reprPrec m _ := repr m.toList

instance : Repr Store where
    reprPrec m _ := repr m.toList

  -- Provide BEq for RBMap by comparing sorted lists
instance : BEq Env where
    beq m₁ m₂ := m₁.toList == m₂.toList

instance : BEq Store where
    beq m₁ m₂ := m₁.toList == m₂.toList

structure Config where
    stmt : Stmt -- Control (C)
    env  : Env -- Environment (E)
    store: Store -- Store (S)
    kptr : Addr -- Pointer to the current continuation (K)
    deriving BEq,Repr

  /-
    Helper: Expression Evaluator
    Evaluates an abstract syntax expression into an Interval.
  -/
def evalExpr (e : Expr) (env : Env) (store : Store) : Interval :=
    match e with
    | .const n => .range (.fin n) (.fin n)
    | .var x =>
        match env.find? x with
        | some addr =>
            match store.find? addr with
            | some (.vInt i) => i
            | _ => .bot -- Type mismatch or uninitialized
        | none => .bot  -- Uninitialized variable
    | .add e1 e2 =>
        (evalExpr e1 env store).add (evalExpr e2 env store)
    | .sub e1 e2 =>
        (evalExpr e1 env store).sub (evalExpr e2 env store)

  /-
    The AAM Step Function
    Returns a List of possible next configurations.
    Non-determinism occurs here when an 'if' condition
    overlaps both true and false values.
  -/
def step (conf : Config) : List Config :=
    match conf.stmt with
    -- Assignment: x := e
    | .assign x e =>
      let val := evalExpr e conf.env conf.store
      match conf.env.find? x with
      | some addr =>
        let oldVal := match conf.store.find? addr with -- look for variable's old value
          | some (StoreVal.vInt i) => i -- if there is some value
          | _ => .bot -- if no value, maybe first time
        let newStore := conf.store.insert addr (.vInt (val.join oldVal))
        -- transfer joins old with new value
        match conf.store.find? conf.kptr with
        -- return mechanism, look for kptr for the next execution
        | some (.vKont .kDone) =>
            [{ conf with stmt := .skip, store := newStore }] -- capture final store
        | some (.vKont (.kSeq next s_next)) =>
        -- we fount a seq that says next and following instructions
            [ {conf with stmt := next, store := newStore, kptr := s_next}]
            -- return a new Config moving to next and updated value
        | some (.vKont (.kWhile e body s_exit)) =>
        -- This is the "boomerang": jump back to the while statement to re-check 'e'
          [{ conf with stmt := (.while e body), store := newStore, kptr := s_exit }]
        | _ => []
        --catch all if kputr points to something we dont know we halt
      |none => []
    -- Sequence S1; S2
    | .seq s1 s2 =>
      --allocate the rest of program into store
      -- to ensure finiteness, the address is dervied from statement itself
        let kAddr := Addr.mk ("k_" ++ toString (hash s2))
        --using hash s2 forces reusing of same address and finite state
        let newKont :=  Kont.kSeq s2 conf.kptr
        --create a reminder object Kont on what to do next
        let newStore := conf.store.insert kAddr (StoreVal.vKont newKont)
        -- save reminder into store kAddr holds stack frame
        -- Focus the machine on s1
        [{ conf with stmt := s1, store := newStore, kptr := kAddr }]
    --While Loop: while e do s
    /-
    note that we implement Interval as Boolean state storing [0,0] as only false
    [1,1] as only true and [0,1] as maybe, taking true and false path
    -/
    | .while e body =>
      let val := evalExpr e conf.env conf.store
      -- Path 1: Entering the loop body(True)
      let trueBranch : Option Config :=
        if val.overlapsTrue then
          let kWhileAddr := Addr.mk ("k_while_" ++ toString (hash conf.stmt))
          let newKont := Kont.kWhile e body conf.kptr
          let newStore := conf.store.insert kWhileAddr (StoreVal.vKont newKont)
          some { conf with stmt := body, store := newStore, kptr := kWhileAddr }
        else
          none
      let falseBranch : Option Config :=
        if val.overlapsFalse then
          match conf.store.find? conf.kptr with
          | some (.vKont (.kSeq next s_next)) =>
            some { conf with stmt := next, kptr := s_next }
          | some (.vKont .kDone) => none
          | _ => none
        else
          none
      [trueBranch, falseBranch].filterMap id
    | .skip =>
      match conf.store.find? conf.kptr with
      | some (.vKont (.kSeq next s_next)) => [{ conf with stmt := next, kptr:=s_next}]
      | some (.vKont (.kWhile e body s_exit)) =>
            [{ conf with stmt := (.while e body), kptr := s_exit }]
      | _ => []
    -- If-then-else: if e then s1 else s2
    | .ite e s1 s2 =>
      let val := evalExpr e conf.env conf.store
      let trueBranch : Option Config :=
        if val.overlapsTrue then
          some { conf with stmt := s1 }
        else
          none
      let falseBranch : Option Config :=
        if val.overlapsFalse then
          some { conf with stmt := s2 }
        else
          none
      [trueBranch, falseBranch].filterMap id
end Analyzer
