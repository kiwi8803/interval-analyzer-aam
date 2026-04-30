import Analyzer.Syntax
import Analyzer.State
import Analyzer.Concrete
import Analyzer.GaloisConnection
import Analyzer.Fixpoint
import Analyzer.Demo

-- ============================================================
-- Demo 1 — Straight-line interval analysis
--   Program : x := 5 ; y := x + 3
--   Expected: x ∈ [5,5],  y ∈ [8,8]
-- ============================================================

def prog1 : Analyzer.Stmt :=
  .seq (.seq (.assign "x" (.const 5))
             (.assign "y" (.add (.var "x") (.const 3))))
       .skip
def run_prog1 : IO Unit := do
  let res := Analyzer.Demo.run prog1 [("x", .bot), ("y", .bot)]
  IO.println (repr res)
-- ============================================================
-- Demo 2 — If-else branch analysis
--   Initial : x ∈ [-32, 5]
--   Program : if x then y := 1 else y := 0
--   Expected: y ∈ [0,1]  (join of both branches)
-- ============================================================

def prog2 : Analyzer.Stmt :=
  .seq (.ite (.var "x")
             (.assign "y" (.const 1))
             (.assign "y" (.const 0)))
       .skip

def run_prog2 : IO Unit := do
  let res := Analyzer.Demo.run prog2 [("x", .range (.fin (-32)) (.fin 5)), ("y", .bot)]
  IO.println (repr res)
-- ============================================================
-- Demo 3 — While-loop widening
--   Initial : x ∈ [1,1]
--   Program : while x do x := x + 1
--   Expected: x ∈ [1, +∞]  (upper bound widened to +∞)
-- ============================================================

def prog3 : Analyzer.Stmt :=
  .while (.var "x")
  (.assign "x" (.add (.var "x") (.const 1)))

def run_prog3 : IO Unit := do
  let res := Analyzer.Demo.run prog3 [("x",  .range (.fin 1) (.fin 1))]
  IO.println (repr res)

--#eval Analyzer.Demo.run prog3 [("x", .range (.fin 1) (.fin 1))]
-- ============================================================
-- Demo 4 — Security: countdown loop then use of x
--   Program :
--   x := 10;
--   while x do
--      x := x - 1;
--   danger := x + 5
--   Concrete: x = 0 after loop, danger = 5 always
--   Abstract: x ∈ [0,10] , danger ∈ [5,15] (over-approx)
-- ============================================================

def prog_security : Analyzer.Stmt :=
  .seq (.assign "x" (.const 10) )
  (.seq (.while (.var "x") (.assign "x" (.sub (.var "x") (.const 1))))
        (.assign "danger" (.add (.var "x") (.const 5))))

def run_security : IO Unit := do
  let res := Analyzer.Demo.run prog_security [("x", .bot), ("danger", .bot)]
  IO.println (repr res)

--#eval Analyzer.Demo.run prog_security [("x", .bot) , ("danger", .bot)]

def main : IO Unit := do
IO.println "==========================================";
IO.println "=    Running Interval Analyzer...        =";
IO.println "==========================================";
IO.println "Analysing program:";
IO.println "------------------------------------------";
IO.println "-                 Demo 1                 -";
IO.println "------------------------------------------";
IO.println "x := 5 ; ";
IO.println "y := x + 3";
IO.println "------------------------------------------";
run_prog1
IO.println "------------------------------------------";
IO.println "-                 Demo 2                 -";
IO.println "------------------------------------------";
IO.println "if x then ";
IO.println "  y := 1";
IO.println "else y := 0;";
IO.println "------------------------------------------";
run_prog2
IO.println "------------------------------------------";
IO.println "-                 Demo 3                 -";
IO.println "------------------------------------------";
IO.println "x := 1;";
IO.println "while x do";
IO.println "   x := x + 1;";
IO.println "------------------------------------------";
run_prog3
IO.println "------------------------------------------";
IO.println "-                 Demo 4                 -";
IO.println "------------------------------------------";
IO.println "x := 10;";
IO.println "while x do;";
IO.println "  x := x - 1;;";
IO.println "danger := x + 5;";
IO.println "------------------------------------------";
run_security
