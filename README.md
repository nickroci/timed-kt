# timed_kt — Levin-Style Timed Complexity in Lean 4

A Lean 4 formalization of conditional time-bounded (Levin-style) Kolmogorov
complexity for bitstrings:

```
Kt_U(x | y) = min { |p| + ⌈log₂ t⌉ : U(p, y) outputs x in t transitions }
```

for one explicit universal machine `U`, with a machine-checked time-side invariance
theorem over a precisely stated comparison class. `|p|` is the length of an actual
bitstring program, and `t` counts transitions of an explicit operational semantics —
neither constructor counts nor `Code.evaln` fuel enter the definition.

The untimed algorithmic-information layer is Alexey Milovanov's
[`kolmogorov_complexity`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean)
library (Apache-2.0), pinned at commit `f11c8f01` on Lean/Mathlib v4.33.0. This
package uses its `Core.Basic`, `Core.UniversalDecompressor`, and `Core.Invariance`
modules: `BitString`, decompressors as partial recursive maps, `condK`/`plainK` over
`ENat`, the unary-prefix universal decompressor, and description-side invariance. The
timed layer — the operational clock, the clocked universal machine, and time-side
invariance — is what this package adds.

## Machine model

The public machine is the **flagged universal machine** (`TimedKt/Flagged.lean`): the
first program bit is a context flag, and the rest of the tape is run by the library's
`universalDecompressor`, which parses it as a unary prefix (`i` ones then a zero)
naming a `Nat.Partrec.Code` and simulates that code on the encoded pair of the
remaining tape and the selected context:

* `flaggedUniversal (true :: p, y) = universalDecompressor (p, [])` — context erased;
* `flaggedUniversal (false :: p, y) = universalDecompressor (p, y)` — context passed.

The flag costs one bit and one transition and buys the conditioning theorem with
additive constant zero (see below). Choosing a universal machine with this closure
property is the standard resolution: without it, erasing the context requires either
wrapping the simulated code (which inflates the unary prefix quadratically) or a
self-interpreter with a proved linear-overhead transition bound (open).

The operational semantics is `Run` (`TimedKt/Run.lean`): a fuel-free inductive
evaluation relation for `Nat.Partrec.Code` in which one transition is one dispatch on
a `Code` constructor. `Run` is proved sound and complete for `Code.eval` (through the
write-once trace evaluator `tracen`), and deterministic: the trace and the transition
count of a halting computation are unique (`Run.deterministic`, new here — the parent
project left this unproved).

`UniversalRuns` (`TimedKt/UniversalRun.lean`) replays the universal decompressor's
computation with this clock; forgetting the clock gives back exactly the library's
machine (`timedUniversal_toMap`, definitional), and the clocked relation is sound and
complete for the untimed semantics (`universalRuns_iff_produces`).

## Cost convention

For a tape with unary-prefix value `i` and a code execution of `steps` transitions:

* scanning the unary prefix costs `i + 1` transitions;
* the code execution costs `steps` transitions (`Run` node events);
* decoding the result costs `1` transition;
* decoding the prefix value to a `Code` and encoding the (remaining tape, context)
  pair are treated as atomic (free).

Total for the unflagged layer: `t = (i + 1) + steps + 1`; the flagged machine adds
one transition for reading the context flag. The run-time price is `ceilLog2 t`, the
least `k` with `t ≤ 2^k` (`ceilLog2_isLeast`); the convention at zero is
`ceilLog2 0 = 0`, which never prices a run since every successful run has `t ≥ 1`.

## The conditioning theorem

`Kt_cond_le_Kt` (`TimedKt/Kt.lean`): `Kt(x | y) ≤ Kt(x)`, with additive constant
zero — a plain-complexity witness runs with empty context, so flipping its flag to
`true` gives a conditional witness of the same length and transition count. The same
holds for the write measure (`Wt_cond_le_Wt`).

Contrast: for the parent project's fuel-priced measure even the constant-overhead
form `Kt(x | y) ≤ Kt(x) + C` is refuted
(`PredecessorSeparation.not_Kt_cond_le_Kt_add_const`), because `evaln` fuel taxes the
mere receipt of the conditioning input. The relativization behavior of the corrected
measure is the textbook one; the failure was a property of the fuel clock.

## Invariance scope

`condKt_timedUniversal_le` (`TimedKt/Invariance.lean`): for every timed decompressor
`D` with a `Realization` — a `Nat.Partrec.Code` simulating every run of `D` with the
same output in at most `a * t + b` transitions — and all `x`, `y`:

```
Kt_U(x | y) ≤ Kt_D(x | y) + overhead,
overhead = (encode code + 1) + ceilLog2 (a + b + encode code + 2)
```

All overhead assumptions are fields of `Realization`, visible in the statement. The
comparison class is inhabited (`idTimedRealization`). The public (flagged) measure
inherits invariance at two extra units (`Kt_cond_le_realized`,
`condKt_flagged_le_condKt_universal`), and instantiating at the identity machine
gives `Kt(x | y) ≤ |x| + O(1)` (`Kt_cond_le_length`).

What is **not** claimed: invariance over machines with no code realization or with
super-linear simulation overhead, and a realization of `timedUniversal` by itself
(linear-overhead self-simulation is open — it is the fuel-instrumented
self-interpreter problem, deliberately out of scope).

## The write-once ledger

The operational relation `Run` carries the write-once trace alongside its transition
count, so the universal machine has a second ledger for free: `UniversalRunsW`
(`TimedKt/WriteOnce.lean`) records the number of values the simulated code commits to
its append-only tape (prefix scanning and result decoding commit nothing). The
write-priced complexity is `Wt_cond x y = min { |p| + ceilLog2 w }`, with
`Wt x = Wt_cond x []`; `numWrites` and `traceBits` (`TimedKt/Trace.lean`) are the
event-count and bit-content ledgers of the underlying tape.

Against the transition clock the write and time prices nearly coincide:

* `Wt_cond_le_Kt_cond` — writes never exceed transitions on the same run of the same
  program, so `Wt_cond ≤ Kt_cond` with no overhead;
* `Kt_cond_le_of_flaggedRunsW` — transitions are linear in writes per fixed code
  (`Run.steps_le`), so each write witness bounds `Kt_cond` within an additive
  `ceilLog2 (|p| + 2 * progSize (parsedCode p) + 4)`, logarithmic in the witness's
  own description data.

In the parent project the same comparison against the *fuel* clock is only
multiplicative, with an unbounded conditional gap; both pathologies are properties of
the fuel clock, not of the write ledger.

The tape's second ledger is priced too: `Bt_cond x y = min { |p| + ceilLog2 b }` over
runs whose inner trace commits `b` total bits (`TimedKt/BitCost.lean`), with the same
commit convention, the witness bound, `K ≤ Bt`, finiteness on exactly the producible
outputs, and the conditioning theorem at constant zero (`Bt_cond_le_Bt`). No
inequality between `Bt` and `Wt` or `Kt` is claimed in either direction: a single
write can carry arbitrarily many bits and a written `0` carries none, so per-run
ledger domination fails both ways.

## Difference from the legacy fuel measure

The parent project's original `Kt` priced runtime by `Code.evaln` fuel and program
size by constructor count. `evaln` fuel is a value-magnitude quantity: the evaluator's
input guard forces fuel past the input value at every node, so the fuel measure taxes
the magnitude of values rather than work performed. The package keeps the least-fuel
cost as `minFuel` (`TimedKt/FuelCost.lean`) together with the regression theorems:

* `fuel_exceeds_writes_unboundedly` — computations with one write but arbitrarily
  large fuel;
* `succ_transitions_constant_fuel_linear` — the successor makes `1` transition for
  every input, while its fuel is `N + 1`.

The public `Kt` (`TimedKt/Kt.lean`) imports neither `minFuel` nor `progSize`; the two
measures meet only in `TimedKt/Examples.lean`, to be compared. `Run.sandwich` records
the write/transition exchange rate (linear per fixed code); it is a statement about
the two operational ledgers, not a write/`Kt` equivalence claim.

## Building and auditing

```
lake exe cache get         # mathlib cache
lake build                 # builds with mathlib's standard linter set enabled
./scripts/audit.sh         # forbidden constructs, sorry-freedom, suppression check
./scripts/check_axioms.sh  # axiom gate over the headline theorems (needs the oleans)
```

Headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; the
axiom gate enforces this in CI.

See `COVERAGE.md` for the source-to-Lean map and the open items.

## License and attribution

Apache-2.0 (see `LICENSE`). Depends on `kolmogorov_complexity` (Apache-2.0), pinned
by commit in `lakefile.toml`; no code is copied from it. The `tracen`/`Run` layer is
ported from the parent `irreducibility` project by the same author.
