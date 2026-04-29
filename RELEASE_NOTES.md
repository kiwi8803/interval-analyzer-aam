# Release Notes — v0.1 (Pre-release)

**Verified Interval Abstract Interpreter**  
**Release date:** April 2026  
**Status:** Pre-release — research prototype, not production software  
**Lean 4 toolchain:** `leanprover/lean4:v4.26.0`  
**Repository:** https://github.com/kiwi8803/interval-analyzer-aam/releases/tag/v0.1

---

## Overview

This is the initial public release of a mechanically verified interval abstract interpreter
for a small imperative language, implemented in Lean 4.
The distinguishing property of this release is **formal soundness**: every concrete
program execution is guaranteed to be over-approximated by the abstract analysis —
proved by machine-checked theorem in Lean 4, with no unverified assumptions in the
core proof chain.

---

## What Is Included

### Verified Core (no `sorry`, no axioms)

| Component | File | Key Theorem |
|-----------|------|-------------|
| Interval abstract domain with Galois connection | `Analyzer/Domain.lean`, `Analyzer/GaloisConnection.lean` | `galois_connection` |
| Concrete CESK small-step semantics | `Analyzer/Concrete.lean`, `Analyzer/State.lean` | `Concrete.step`, `Concrete.BigStep` |
| Abstract CESK machine (AAM) | `Analyzer/State.lean` | `step` |
| Local soundness (one-step simulation) | `Analyzer/GaloisConnection.lean` | `step_local_sound` |
| Global soundness (full execution by induction) | `Analyzer/GaloisConnection.lean` | `global_soundness` |
| Widening operator soundness | `Analyzer/GaloisConnection.lean` | `widen_sound` |

The global soundness theorem states: for any concrete execution $c \to^* c'$ where $c$
is simulated by an abstract configuration $a$, there exists an abstract state $a'$
reachable from $a$ that simulates $c'$.
This is a machine-checked proof by induction over the execution chain with no
`sorry` placeholders and no axioms beyond Lean 4's kernel and Mathlib's verified library.

### Working Analyzer

A fully executable interval analyzer with four built-in demonstrations accessible via:

```bash
lake exe analyzer   # ~5–10 seconds
```

Six additional interactive examples are available in `Analyzer/Demo.lean` via `#eval`.

### Voluntary Proof Extension

`Analyzer/Fixpoint.lean` (1,382 lines) develops a formal bridge connecting the
mathematical `global_soundness` result to the concrete worklist implementation
`widenFixpoint`. This includes:

- `postfixpoint_contains_reachable` — Tarski-style containment principle (proved)
- `reachableSet_eq_lfp` — connection to Mathlib's `OrderHom.lfp` (proved)
- `DomPostFixpoint` — the correct closure property for widening-based algorithms (proved)
- `capIntervalAtBound_le`, `capping_preserves_widening_bound` — loop-analysis capping soundness (proved)
- `fixpoint_sound`, `end_to_end_soundness` — structurally complete; two worklist
  sub-lemmas (`go_dominator_invariant`, `widenFixpoint_dom_postfixpoint`) remain as
  identified future work with clear proof sketches

---

## Supported Language

The analyzer handles a minimal imperative language:

- **Expressions:** integer constants, variable reads, addition (`+`), subtraction (`−`)
- **Statements:** assignment (`:=`), sequencing (`;`), conditional (`if-then-else`), while-loop, skip
- **Semantics:** C-style boolean (non-zero = true); both branches explored when the abstract guard is ambiguous

---

## Demonstrations

| Demo | Program | Analysis result |
|------|---------|-----------------|
| Straight-line | `x := 5; y := x + 3` | `x ∈ [5,5], y ∈ [8,8]` |
| If-else | `if x then y:=1 else y:=0` (x ∈ [−32,5]) | `y ∈ [0,1]` |
| While widening | `while x do x := x+1` (x starts at 1) | `x ∈ [1,+∞)` |
| Countdown security | `x:=10; while x do x:=x−1; danger:=x+5` | `danger ∈ [5,15]` |
| Increasing counter | `x:=−5; while x do x:=x+1; result:=x+10` | `result ∈ [5,10]` |
| Nested loops | outer countdown with inner reset | `out ∈ (−∞,5], inner ∈ (−∞,3]` |

---

## Codebase Summary

| File | Lines | Role |
|------|-------|------|
| `Analyzer/Syntax.lean` | 23 | Language AST |
| `Analyzer/Domain.lean` | 214 | Interval lattice, α, γ, widening |
| `Analyzer/State.lean` | 206 | Abstract CESK machine |
| `Analyzer/Concrete.lean` | 109 | Concrete CESK machine |
| `Analyzer/GaloisConnection.lean` | 996 | All core soundness proofs |
| `Analyzer/Fixpoint.lean` | 1,382 | Fixpoint bridge extension |
| `Analyzer/Demo.lean` | 348 | Six runnable examples |
| `Analyzer.lean` | ~100 | Entry point and main function |
| **Total** | **~3,380** | |

The core proof file (`GaloisConnection.lean`) contains 38 theorems and lemmas,
all fully proved. The extension (`Fixpoint.lean`) contains 63 declarations,
of which the majority are proved; 2 worklist loop invariants remain pending.

---

## Build & Performance

| Action | Time |
|--------|------|
| First `lake build` (Mathlib cache download) | ~5 min |
| Incremental `lake build` | ~10–30 sec |
| `lake exe analyzer` | ~5–10 sec |
| `#eval` in VS Code | < 1 sec per example |

---

## Known Limitations

1. **Arithmetic:** only addition and subtraction are supported. Multiplication,
   division, and comparison operators are not in scope for v0.1.

2. **Precision:** 0-CFA allocation and aggressive widening can produce imprecise
   results for loops with large but finite bounds (e.g., a loop from 0 to 10 may
   produce `[0, +∞)` rather than `[0, 10]`). Loop-analysis capping mitigates this
   for common patterns; see Demos 4 and 5.

3. **Worklist bridge:** `fixpoint_sound` and `end_to_end_soundness` in `Fixpoint.lean`
   depend on two worklist sub-lemmas that are currently `sorry`. These are in the
   voluntary extension and do not affect the core `global_soundness` guarantee.
   A one-axiom bridge (`go_eq_goFuel`) is accepted for the `partial def` / kernel
   boundary; this becomes a theorem when `go` is refactored with `termination_by`.

4. **Loop exit via `kDone`:** a while-loop at top level with no trailing statement will
   silently terminate the analysis (no false-branch successors are generated). Wrap
   all programs in `.seq prog .skip` as shown in the demos.

---

## Future Work

- Prove the two remaining worklist sub-lemmas to complete `fixpoint_sound` without axioms
- Refactor `go` from `partial def` to a `termination_by` definition, eliminating `go_eq_goFuel`
- Add narrowing operator for post-fixpoint refinement
- Extend expressions with multiplication and comparison operators
- Explore relational domains (Octagons / Polyhedra) — the CESK architecture is parametric
  over the store value type, requiring only a new lattice definition and its domain-specific soundness proof

---

## Acknowledgements

Built using [Lean 4](https://leanprover.github.io/) and
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/).
The abstract machine design follows the Abstracting Abstract Machines (AAM)
methodology of Van Horn and Might (ICFP 2010).
