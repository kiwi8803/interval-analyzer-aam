import Analyzer.State
import Analyzer.GaloisConnection

namespace Analyzer.Demo

open Analyzer Batteries

-- ============================================================
-- Loop Analysis
-- ============================================================

/-- Information about a while loop's update pattern -/
structure LoopInfo where
  loopVar : String           -- Variable being updated
  updateDelta : Int          -- Change per iteration (e.g., -1 for x := x - 1)
  terminationBound : Int     -- Value at which loop terminates (0 for while(x))
  deriving BEq, Repr

/-- Extract variable name from a simple condition -/
def extractCondVar : Expr → Option String
  | .var v => some v
  | _ => none

/-- Extract update delta from simple assignment patterns -/
def extractUpdateDelta : Stmt → String → Option Int
  | .assign v (.sub (.var v') (.const c)), varName =>
    if v = varName && v' = varName && c = 1 then some (-1) else none
  | .assign v (.add (.var v') (.const c)), varName =>
    if v = varName && v' = varName && c = 1 then some 1 else none
  | .seq s1 s2, varName =>
    (extractUpdateDelta s1 varName).orElse (fun _ => extractUpdateDelta s2 varName)
  | _, _ => none

/-- Analyze loops in the program -/
def analyzeLoops : Stmt → RBMap String LoopInfo compare
  | .while cond body =>
    match extractCondVar cond with
    | some varName =>
      match extractUpdateDelta body varName with
      | some delta =>
        let info : LoopInfo := { loopVar := varName, updateDelta := delta, terminationBound := 0 }
        let m := RBMap.empty
        m.insert varName info
      | none => RBMap.empty
    | none => RBMap.empty
  | .seq s1 s2 =>
    let m1 := analyzeLoops s1
    let m2 := analyzeLoops s2
    m2.foldl (fun acc k v => acc.insert k v) m1
  | .ite _ s1 s2 =>
    let m1 := analyzeLoops s1
    let m2 := analyzeLoops s2
    m2.foldl (fun acc k v => acc.insert k v) m1
  | _ => RBMap.empty

/-- Cap an interval based on loop termination info -/
def capIntervalAtBound (iv : Interval) (bound : Int) (delta : Int) : Interval :=
  match iv with
  | .bot => .bot
  | .range low high =>
    let boundExt := ExtendedInt.fin bound
    -- Cap in the direction of the loop's movement:
    -- Decreasing (delta < 0): cap the lower bound at termination value only if high >= bound
    -- Increasing (delta > 0): cap the upper bound at termination value only if low <= bound
    let low' :=
      if delta < 0 then
        -- Decreasing: cap lower bound at termination value if loop can reach it (high >= bound)
        if boundExt.leBool high then
          if boundExt.leBool low then low else boundExt
        else
          low
      else
        low
    let high' :=
      if delta > 0 then
        -- Increasing: cap upper bound at termination value if loop can reach it (low <= bound)
        if low.leBool boundExt then
          if high.leBool boundExt then high else boundExt
        else
          high
      else
        high
    .range low' high'

/-- Apply capping to a store based on loop analysis -/
def capStoreAtLoopBound (store : Store) (loopVar : String) (bound : Int) (delta : Int) : Store :=
  match store.find? (.mk loopVar) with
  | some (.vInt iv) =>
    let capped := capIntervalAtBound iv bound delta
    store.insert (.mk loopVar) (.vInt capped)
  | _ => store

-- ============================================================
-- Runners
-- ============================================================

/-- Expand every config in the list by one abstract step. -/
def stepAll (configs : List Config) : List Config := configs.flatMap step

/-- Run until the set of reachable configs is empty (halted) or fuel runs out.
    Returns the last non-empty generation. -/
def runAbstract : Nat → List Config → List Config
  | 0, cs => cs
  | n + 1, cs =>
    let next := stepAll cs
    if next.isEmpty then cs else runAbstract n next

/-- Widen each interval in `new_` against the same address in `old`.
    Uses Domain.widen convention: widen(newInterval, oldInterval). -/
def widenStore (old new_ : Store) : Store :=
  new_.foldl (fun acc addr sv =>
    match sv, old.find? addr with
    | .vInt iNew, some (.vInt iOld) => acc.insert addr (.vInt (widen iNew iOld))
    | _, _ => acc.insert addr sv) new_

/-- Two configs are at the same abstract program point when they have the
    same statement and continuation pointer.  The worklist uses this to
    detect revisits that require widening. -/
def samePoint (x c : Config) : Bool := x.stmt == c.stmt && x.kptr == c.kptr

/-- Helper to join intervals across two stores (for non-widening steps) -/
def joinStore (old new_ : Store) : Store :=
  new_.foldl (fun acc addr sv =>
    match sv, old.find? addr with
    | .vInt iNew, some (.vInt iOld) => acc.insert addr (.vInt (iNew.join iOld))
    | _, _ => acc.insert addr sv) new_

/-- Core worklist loop.  `go seen rest` processes the `rest` worklist,
    accumulating visited states in `seen`. Termination is guaranteed by widening:
    each (stmt, kptr) point can be widened at most finitely many times before
    reaching the lattice top (±∞ bounds), after which no growth occurs.

    Invariant: `seen` contains at most one entry per program point.
    On a first visit the config is appended; on a revisit the stored
    entry is widened (if necessary) and re-stepped.

    Uses N-delayed widening: always join for first `threshold` revisits,
    then apply normal widening logic. This gives tighter bounds by exploring
    more of the concrete value space before approximating via widening. -/
partial def go (threshold : Nat) (loopInfo : RBMap String LoopInfo compare) :
    List (Config × Nat) → List Config → List Config
  | seen, [] => seen.map (·.1)
  | seen, c :: rest =>
    match seen.find? (fun (x, _) => samePoint x c) with
    | none =>
      go threshold loopInfo (seen ++ [(c, 1)]) (rest ++ step c)
    | some (old, count) =>
      -- N-delayed widening: join for the first N revisits (count < threshold)
      -- If stable before reaching threshold, we've reached fixpoint and stop
      -- Once count >= threshold, apply widening + loop-aware capping to force convergence
      if count < threshold then
        let nextStore := joinStore old.store c.store
        if nextStore == old.store then
          -- Stable! Reached fixpoint within join phase, stop here
          go threshold loopInfo seen rest
        else
          -- Not yet stable, continue re-stepping within join budget
          let updated : Config := { old with store := nextStore }
          let newSeen := seen.map (fun (x, cnt) =>
            if samePoint x c then (updated, cnt + 1) else (x, cnt))
          go threshold loopInfo newSeen (rest ++ step updated)
      else
        -- count >= threshold: Exhausted join budget, apply widening
        let nextStore := widenStore old.store c.store
        -- Apply loop-aware capping if we have loop info
        let cappedStore :=
          loopInfo.foldl (fun acc varName info =>
            capStoreAtLoopBound acc varName info.terminationBound info.updateDelta) nextStore
        if cappedStore == old.store then
          -- Capped store equals old, fixpoint reached
          go threshold loopInfo seen rest
        else
          -- Store grew even after capping, continue re-stepping
          let updated : Config := { old with store := cappedStore }
          let newSeen := seen.map (fun (x, cnt) =>
            if samePoint x c then (updated, cnt + 1) else (x, cnt))
          go threshold loopInfo newSeen (rest ++ step updated)
/--
def go : Nat → List Config → List Config → List Config
  | 0,     seen, _         => seen
  | _,     seen, []        => seen
  | n + 1, seen, c :: rest =>
    match seen.find? (samePoint · c) with
    | none =>
      -- First visit: record state and enqueue successors.
      go n (seen ++ [c]) (rest ++ step c)
    | some old =>
      let ws := widenStore old.store c.store
      if ws == old.store then
        -- Already stable at this program point.
        go n seen rest
      else
        -- Store grew: replace the record and re-step from the wider state.
        let updated : Config := { old with store := ws }
        let newSeen := seen.map (fun x => if samePoint x c then updated else x)
        go n newSeen (rest ++ step updated)
---- Worklist fixpoint with widening.
    When (stmt, kptr) is revisited, widen the store to force convergence.
    Returns every discovered abstract state at fixpoint.

    Now fuel-free: the algorithm terminates due to widening convergence. -/
def widenFixpoint (threshold : Nat) (init : Config) : List Config :=
  let loopInfo := analyzeLoops init.stmt
  go threshold loopInfo [] [init]

-- ============================================================
-- Display helper
-- ============================================================

/-- Join intervals for each named variable across all configs. -/
def showVars (env : Env) (configs : List Config) : List (String × Interval) :=
  env.toList.filterMap fun (name, addr) =>
    let ivs := configs.filterMap fun c =>
      match c.store.find? addr with | some (.vInt i) => some i | _ => none
    match ivs with
    | []      => none
    | i :: is => some (name, is.foldl Interval.join i)

-- ============================================================
-- Config builder
-- ============================================================

def kDoneAddr : Addr := .mk "k_done"

/-- Construct an initial abstract CESK config from named initial intervals. -/
def mkConfig (prog : Stmt) (vars : List (String × Interval)) : Config :=
  let env   : Env   := vars.foldl (fun e (v, _) => e.insert v (.mk v)) RBMap.empty
  let store0 : Store := (RBMap.empty : Store).insert kDoneAddr (.vKont .kDone)
  let store  : Store := vars.foldl (fun s (v, i) => s.insert (.mk v) (.vInt i)) store0
  { stmt := prog, env := env, store := store, kptr := kDoneAddr }

-- ============================================================
-- Demo 1 — Straight-line interval analysis
--   Program : x := 5 ; y := x + 3
--   Expected: x ∈ [5,5],  y ∈ [8,8]
-- ============================================================

def prog1 : Stmt :=
  .seq (.seq (.assign "x" (.const 5))
             (.assign "y" (.add (.var "x") (.const 3))))
       .skip

--#eval
  --let cfg    := mkConfig prog1 [("x", .bot), ("y", .bot)]
 -- let finals := runAbstract 20 [cfg]
  --showVars cfg.env finals

-- ============================================================
-- Demo 2 — If-else branch analysis
--   Initial : x ∈ [-32, 5]
--   Program : if x then y := 1 else y := 0
--   Expected: y ∈ [0,1]  (join of both branches)
-- ============================================================

def prog2 : Stmt :=
  .seq (.ite (.var "x")
             (.assign "y" (.const 1))
             (.assign "y" (.const 0)))
       .skip

--#eval
 -- let cfg    := mkConfig prog2 [("x", .range (.fin (-32)) (.fin 5)), ("y", .bot)]
 -- let finals := runAbstract 20 [cfg]
  --showVars cfg.env finals

-- ============================================================
-- Demo 3 — While-loop widening
--   Initial : x ∈ [1,1]
--   Program : while x do x := x + 1
--   Expected: x ∈ [1, +∞)  (upper bound widened to +∞)
-- ============================================================

def prog3 : Stmt :=
  .while (.var "x")
  (.assign "x" (.add (.var "x") (.const 1)))

--#eval
 -- let cfg    := mkConfig prog3 [("x", .range (.fin 1) (.fin 1))]
 -- let finals := (widenFixpoint 1 cfg)
 -- showVars cfg.env finals

-- ============================================================
-- Demo 4 — Security: countdown loop then use of x
--   Program :
--   x := 10;
--   while x do
--      x := x - 1;
--   danger := x + 5
--   Concrete: x = 0 after loop, danger = 5 always
--   Abstract: x ∈ [−∞,10] (widened), danger ∈ [−∞,15] (over-approx)
-- ============================================================

def prog_security : Stmt :=
  .seq (.assign "x" (.const 10) )
  (.seq (.while (.var "x") (.assign "x" (.sub (.var "x") (.const 1))))
        (.assign "danger" (.add (.var "x") (.const 5))))

--#eval
 -- let cfg := mkConfig prog_security [("x", .bot), ("danger", .bot)]
--  showVars cfg.env (widenFixpoint 12 cfg)
-- Expected with N=12: x → [-1, 10],  danger → [5, 15]

-- ============================================================
-- Demo 5 — Increasing loop from negative start
--   Program : x := -5; while x { x := x + 1 }; result := x + 10
--   Concrete: x counts -5 → -4 → ... → -1 → 0 (exit); result = 10
--   Abstract: x ∈ [-5, 0] (capped via loop analysis), result ∈ [5, 10]
-- ============================================================

def prog_counting_up : Stmt :=
  .seq (.assign "x" (.const (-5)))
  (.seq (.while (.var "x") (.assign "x" (.add (.var "x") (.const 1))))
        (.assign "result" (.add (.var "x") (.const 10))))

--#eval
 -- let cfg := mkConfig prog_counting_up [("x", .bot), ("result", .bot)]
 -- showVars cfg.env (widenFixpoint 2 cfg)
-- Expected: x ∈ [-5, 0], result ∈ [5, 10]

-- ============================================================
-- Demo 6 — Nested Loops: Outer countdown with Inner reset
--   Program : out := 5; while out { inner := 3; while inner { inner -= 1 }; out -= 1 }
--   Concrete: out=0, inner=0 after execution
--   Abstract: out ∈ [−∞,5], inner ∈ [−∞,3] (converged via widening)
-- ============================================================

def prog_nested : Stmt :=
  .seq
    (.assign "out" (.const 5))
    (.while (.var "out")
      (.seq
        (.assign "inner" (.const 3))
        (.seq
          (.while (.var "inner")
            (.assign "inner" (.sub (.var "inner") (.const 1))))
          (.assign "out" (.sub (.var "out") (.const 1))))))

--#eval
  --let cfg := mkConfig prog_nested [("out", .bot), ("inner", .bot)]
  --howVars cfg.env (widenFixpoint 10 cfg)


def run (prog : Stmt) (init : List (String × Interval)) :=
  let cfg := mkConfig prog init
  showVars cfg.env (widenFixpoint 1 cfg)

--#eval Analyzer.Demo.run prog3 [("x", .range (.fin 10) (.fin 10))]
end Analyzer.Demo
