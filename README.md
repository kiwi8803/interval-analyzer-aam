# Interval Analyzer (Lean 4)

This project implements an interval-based abstract interpreter in Lean 4.

It performs static analysis of simple imperative programs using:

- Interval abstract domain

- Loop widening

- Fixpoint computation

---

# Build

Run:
```
lake build
```
---

# Run

Run full demo suite:
```
lake exe analyzer
```

note: it takes ~10secs to run the analyzer

Or run individual examples in Lean:
```
#eval Analyzer.Demo.run prog1 [("x", .bot), ("y", .bot)]
```
---

# Expected Output

When running:

lake exe analyzer

the program prints results similar to:

Demo 1  Straight-line interval analysis
-  Program : x := 5 ; y := x + 3
-  Expected: x ∈ [5,5],  y ∈ [8,8]
```
x := 5
y := x + 3

x = [5,5]
y = [8,8]
```
Demo 2  If-else branch analysis
-   Initial : x ∈ [-32, 5]
-   Program : if x then y := 1 else y := 0
-  Expected: y ∈ [0,1]  (join of both branches)
```
if x then y := 1 else y := 0

x = [-32,5]
y = [0,1]
```
Demo 3  While-loop widening
-  Initial : x ∈ [1,1]
-  Program : while x do x := x + 1
-  Expected: x ∈ [1, +∞]  (upper bound widened to +∞)
```
x := 1
while x do x := x + 1

x = [1,+inf]
```
Demo 4  Security: countdown loop then use of x
-   Program :
```
x := 10;
  while x do
     x := x - 1;
  danger := x + 5
```
-  Concrete: x = 0 after loop, danger = 5 always
-   Abstract: x ∈ [0,10] , danger ∈ [5,15] (over-approx)
```
x := 10
while x do x := x - 1
danger := x + 5

x = [0,10]
danger = [5,15]
```
---

# Project Structure

Analyzer/                  -- Core abstract interpreter library

  Syntax.lean             -- AST of the language

  State.lean             -- Program state / environments

  Concrete.lean          -- Concrete semantics

  Domain.lean            -- Interval abstract domain

  GaloisConnection.lean  -- Soundness bridge (concrete ↔ abstract)

  Fixpoint.lean          -- Widening + fixpoint iteration engine

  Demo.lean                 --  evaluation harness + Driver

Analyzer.lean            -- Main module (re-exports / entry API)

---

# Notes

- Output is sound but may be imprecise due to widening

- Lean warnings may appear but are safe to ignore

- Main command: lake exe analyzer
