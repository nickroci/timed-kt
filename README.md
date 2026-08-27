# timed_kt — Levin-Style Timed Complexity in Lean 4

To our knowledge, **the first machine-checked formalization of Levin's time-bounded
Kolmogorov complexity (`Kt`) in any proof assistant** (see Related work below): a
Lean 4 formalization of conditional time-bounded Kolmogorov complexity for
bitstrings,

```
Kt_U(x | y) = min { |p| + ⌈log₂ t⌉ : U(p, y) outputs x in t transitions }
```

for one explicit universal machine `U`, with a machine-checked time-side invariance
theorem over a precisely stated comparison class and a machine-checked triangle
inequality with explicit constants. `|p|` is the length of an actual
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

The public machine is the **composing universal machine** (`TimedKt/Comp.lean`):
the first program bit is a composition flag over the **flagged universal machine**
(`TimedKt/Flagged.lean`), which is embedded verbatim.

* `compUniversal (false :: s, z) = flaggedUniversal (s, z)` — an **embed node**;
* `compUniversal (true :: b :: gammaCode ℓ ++ p₁ ++ p₂, z)` with `|p₁| = ℓ` — a
  **composition node**: run `p₂` (recursively) on context `[]` or `z` as the erase
  bit `b` selects, obtaining `y`, then run `p₁` (recursively) on context `y`;
* undefined on every other tape — the gamma decoder is exact
  (`gammaParse_eq_some_iff`, `TimedKt/Gamma.lean`): it rejects tapes whose length
  code is missing, incomplete, or non-canonical, so a composition tape has exactly
  one reading.

The flagged machine beneath: its first bit is a context flag, and the rest of the
tape is run by the library's `universalDecompressor`, which parses it as a unary
prefix (`i` ones then a zero) naming a `Nat.Partrec.Code` and simulates that code on
the encoded pair of the remaining tape and the selected context:

* `flaggedUniversal (true :: p, y) = universalDecompressor (p, [])` — context erased;
* `flaggedUniversal (false :: p, y) = universalDecompressor (p, y)` — context passed.

One edge of the parse is worth stating: the zero delimiter of the unary prefix is
not formally required — on an all-ones tape the prefix value is the whole tape
length and the program remainder is empty (end of tape acts as the delimiter, and
the scan is still charged `i + 1` transitions). This matches the underlying
library's parser exactly.

Each flag costs one bit and one transition, and the erase bits buy the conditioning
theorem with additive constant zero (see below): a plain witness becomes a
conditional witness by flipping the single erase bit at its own root — the context
flag for an embed node, the comp erase bit for a composition node. Choosing a
universal machine with this closure property is the standard resolution: without
it, erasing the context requires either wrapping the simulated code (which inflates
the unary prefix quadratically) or a self-interpreter with a proved linear-overhead
transition bound (open). The composition primitive plays the same role for the
triangle inequality (see below): composing two programs by code-wrapping or
self-interpretation would face the identical obstruction, while the machine
primitive costs only the self-delimited split point.

Computability of the composing machine is proved through an iterative stack machine
and `Partrec.fix` (`TimedKt/CompPartrec.lean`); the recursion on the tape is
well-founded because both blocks of a composition node are strictly shorter than
their tape.

The operational semantics is `Run` (`TimedKt/Run.lean`): a fuel-free inductive
evaluation relation for `Nat.Partrec.Code` in which one transition is one dispatch on
a `Code` constructor. `Run` is proved sound and complete for `Code.eval` (through the
write-once trace evaluator `tracen`), and deterministic: the trace and the transition
count of a halting computation are unique (`Run.deterministic`).

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
one transition for reading the context flag. The composing layer adds, per node:

* an embed node costs `1` transition (the comp flag) on top of the flagged run;
* a composition node costs `2` transitions (the comp flag and the erase bit), one
  transition per bit of the gamma length code, and its two recursive stages:
  `t = t₂ + t₁ + |gammaCode ℓ| + 2`; the split of the tape at the decoded length is
  atomic (the same license as the free pair-encode).

The run-time price is `ceilLog2 t`, the
least `k` with `t ≤ 2^k` (`ceilLog2_isLeast`); the convention at zero is
`ceilLog2 0 = 0`, which never prices a run since every successful run has `t ≥ 1`.

## The conditioning theorem

`Kt_cond_le_Kt` (`TimedKt/Kt.lean`): `Kt(x | y) ≤ Kt(x)`, with additive constant
zero — a plain-complexity witness becomes a conditional witness of the same length
and transition count by flipping the single erase bit at its root: the context flag
for an embed node, the comp erase bit for a composition node
(`condKt_comp_cond_le_plain`; no induction over the tape is needed, which is
exactly what the composition node's own erase bit is for). The same holds for the
write and bit measures (`Wt_cond_le_Wt`, `Bt_cond_le_Bt`).

Contrast: a fuel clock cannot behave this way. Pricing runtime by the least
`Code.evaln` fuel taxes the mere receipt of the conditioning input — the evaluator's
input guard forces any halting evaluation's fuel past its input value
(`Code.evaln_bound`) — so the price of "given `y`" grows with the magnitude of `y`
rather than with work performed, which is incompatible with constant-overhead
conditioning. This package proves the underlying fuel/work divergence
(`fuel_exceeds_writes_unboundedly`, `succ_transitions_constant_fuel_linear`); the
relativization behavior of the transition-clocked measure is the textbook one.

Free conditioning makes the transfer quantity `Kt(x) − Kt(x | y)` — the time-bounded
analogue of `I(y : x) = K(x) − K(x | y)` — well-defined with no context-size
correction term (`ktTransfer`, `TimedKt/InfoTransfer.lean`): it is nonnegative by
construction and satisfies `ktTransfer y x + Kt(x | y) = Kt(x)` exactly. A finite
`condKt` is attained by an actual run (`TimedDecompressor.exists_runs_condKt`), so
the optimal description length bounds the witness runtime — a witness for `x` from `y`
runs within `2 ^ Kt(x | y)` transitions, and every bit of transferred information
halves that worst-case runtime (`exists_run_time_le_two_pow_of_ktTransfer`). The
write measure supports the same construction (`wtTransfer`).

## Invariance scope

`condKt_timedUniversal_le` (`TimedKt/Invariance.lean`): for every timed decompressor
`D` with a `Realization` — a `Nat.Partrec.Code` simulating every run of `D` with the
same output in at most `a * t + b` transitions — and all `x`, `y`:

```
Kt_U(x | y) ≤ Kt_D(x | y) + overhead,
overhead = (encode code + 1) + ceilLog2 (a + b + encode code + 2)
```

All overhead assumptions are fields of `Realization`, visible in the statement. The
comparison class is inhabited (`idTimedRealization`). The public (composing)
measure inherits invariance at four extra units — two for the context flag, two for
the comp flag (`Kt_cond_le_realized`, through `condKt_flagged_le_condKt_universal`
and `condKt_comp_le_condKt_flagged`) — and instantiating at the identity machine
gives `Kt(x | y) ≤ |x| + O(1)` (`Kt_cond_le_length`).

What is **not** claimed: invariance over machines with no code realization or with
super-linear simulation overhead, and a realization of `timedUniversal` by itself
(linear-overhead self-simulation is open — it is the fuel-instrumented
self-interpreter problem, deliberately out of scope).

## The triangle inequality

`Kt_triangle` (`TimedKt/Triangle.lean`), with the explicit constant `7`:

```
Kt(x | y) = n₁  and  Kt(y | z) = n₂   imply
Kt(x | z) ≤ n₁ + n₂ + 3 ⌈log₂ (n₁ + 1)⌉ + 7.
```

The two optimal witnesses are attained by actual runs
(`TimedDecompressor.exists_runs_condKt`) and composed on one composition node with
the erase bit `false`, so the outer context flows through; output determinism
recovers the middle value. The description overhead is the two flags plus the gamma
code of the split point (`2 ⌈log₂ (n₁ + 1)⌉ + 1` bits, `gammaCode_length`); the
time overhead is the ceiling logarithm of the summed clock, within two bits of the
sum of the ceiling logarithms (`ceilLog2_add_le`) plus a log-log term absorbed into
the constant (`ceilLog2_two_mul_add_three_le`).

The logarithmic term is necessary, not slack: on a plain-style (non-prefix-free)
program format, an injective packing of two arbitrary programs into one must spend
`Ω(log)` bits delimiting the split on some inputs, so a uniform additive constant
is the signature of a prefix-free sibling measure, not of plain `Kt` (Li–Vitányi
§2.1 and Chapter 7). At `z = []` the theorem specializes to the easy direction of
symmetry of information, `Kt(x) ≤ Kt(x | y) + Kt(y) + 3 ⌈log₂ (Kt(x | y) + 1)⌉ + 7`
(`Kt_le_Kt_cond_add_Kt`).

The write and bit measures compose over the same tape with the smaller overhead
`2 ⌈log₂ (m₁ + 1)⌉ + 4` (`Wt_triangle`, `Bt_triangle`): a composition node's ledger
is the plain sum of its stages' ledgers — the gamma scan costs transitions but
commits nothing — so the time-side log-log terms disappear.

## The write-once ledger

The operational relation `Run` carries the write-once trace alongside its transition
count, so the universal machines have a second ledger for free: `UniversalRunsW`
(`TimedKt/WriteOnce.lean`) records the number of values the simulated code commits to
its append-only tape (prefix scanning and result decoding commit nothing), and the
flagged and composing layers thread it through (`FlaggedRunsW`, `CompRunsW` — flags
and the gamma scan commit nothing, and a composition node's ledger is the sum of its
stages'). The write-priced complexity is `Wt_cond x y = min { |p| + ceilLog2 w }`
over the composing machine's ledgered runs, with `Wt x = Wt_cond x []`; `numWrites`
and `traceBits` (`TimedKt/Trace.lean`) are the event-count and bit-content ledgers
of the underlying tape.

Against the transition clock the write and time prices nearly coincide:

* `Wt_cond_le_Kt_cond` — writes never exceed transitions on the same run of the same
  program, so `Wt_cond ≤ Kt_cond` with no overhead;
* `Kt_cond_le_of_flaggedRunsW` — transitions are linear in writes per fixed code
  (`Run.steps_le`), so each flagged write witness on a tape `s` bounds `Kt_cond`
  within an additive `ceilLog2 (|s| + 2 * progSize (parsedCode s.tail) + 4) + 2`
  (the tail drops the context flag; the `+ 2` is the embed cost of the composing
  layer), logarithmic in the witness's own description data.

No comparison of this quality is available on a fuel clock: fuel diverges
unboundedly from the committed work (`fuel_exceeds_writes_unboundedly`), so a
fuel-priced time measure cannot track the write ledger at zero overhead. The tight
coupling above is possible because both prices are derived from the same
operational run.

The tape's second ledger is priced too: `Bt_cond x y = min { |p| + ceilLog2 b }` over
runs whose inner trace commits `b` total bits (`TimedKt/BitCost.lean`), with the same
commit convention, the witness bound, `K ≤ Bt`, finiteness on exactly the producible
outputs, and the conditioning theorem at constant zero (`Bt_cond_le_Bt`). No
inequality between `Bt` and `Wt` or `Kt` is claimed in either direction: a single
write can carry arbitrarily many bits and a written `0` carries none, so per-run
ledger domination fails both ways.

## The asymptotic layer

Single-instance `Kt` admits hardcoding — `Kt(x | y) ≤ |x| + O(1)`
(`Kt_cond_le_length`) — so per-instance optimality cannot separate computing an output
from printing it, and for a one-bit output even the conditional complexity is `O(1)`
outright. The standard resolution measures a whole output family:
`TimedKt/Asymptotic.lean` fixes an infinite sequence `Z : ℕ → Bool` and tracks the
profile `ktProfile Z n = Kt(Z↾n)` (a natural number — the measure is everywhere
finite) and its limsup density `ktRate Z = limsup ktProfile Z n / n`, valued in
`ℝ≥0∞`. The rate is the time-bounded sibling of the prefix-complexity densities of
constructive dimension (Lutz's dimension in complexity classes; Mayordomo's Kolmogorov
characterization; the `limsup` form corresponds to the strong dimension of Athreya,
Hitchcock, Lutz, and Mayordomo).

Two theorems bracket the rate. Hardcoding pins it at the ceiling: `ktRate Z ≤ 1` for
every sequence, however uncomputable (`ktRate_le_one`). Cheap generation collapses
it, at three uniformity levels. Level 1 (`ktRate_eq_zero_of_witnesses`): if runs of
the flagged machine — the embedded inner layer, carried into the public measure by
the embed bridge `Kt_cond_le_of_flaggedRuns` at one bit and one transition, both
absorbed by the densities — produce every prefix with description length at most
`g n` and runtime at most `T n`, and the densities `g n / n` and `ceilLog2 (T n) / n`
both vanish, then `ktRate Z = 0`. The hypothesis is `∀ n, ∃ p` — the witness may vary
arbitrarily with `n` — so this level is *nonuniform*: a sublinear-advice collapse.
Level 2 (`ktRate_eq_zero_of_code`) fixes a single `Nat.Partrec.Code` fed an input-tape
family `d n`, the code's unary prefix entering as a constant absorbed by the density
hypotheses; the family `d` is an arbitrary — possibly noncomputable — function, so
this level is code-uniform with advice inputs. Level 3
(`ktRate_eq_zero_of_uniform_code`) is fully uniform: one fixed code on the canonical
input `Nat.bits n`, no advice — the description density is discharged internally,
since the binary expansion has length at most `ceilLog2 (n + 1)`
(`bits_length_le_ceilLog2_succ`) and that density vanishes
(`tendsto_ceilLog2_succ_div_atTop_nhds_zero`), leaving only the log-runtime density
as a hypothesis. Cheap generation is therefore visible at the rate level even though
every single prefix admits the printing bound. The write measure supports the same
construction (`wtProfile`, `wtRate`), with `wtRate ≤ ktRate` (`wtRate_le_ktRate`).

Boolean functions enter at two distinct objects. The **characteristic sequence**
(`charSeq f`, rate `charSeqKtRate f`) reads `f` along the canonical enumeration
`bitStringEnum : ℕ ≃ BitString`; its prefixes are enumeration-dependent fragments —
the enumeration interleaves lengths, so they are *not* truth tables of any single
arity. The **truth table** (`truthTable f n`, the `2 ^ n`-bit values of `f` on all
length-`n` inputs in lexicographic order via `lexStrings`, with `mem_lexStrings` and
`lexStrings_nodup` certifying the enumeration) is the meta-complexity convention of
Allender, Buhrman, Koucký, van Melkebeek, and Ronneburger; its rate `ttKtRate f`
normalizes the per-arity profile `ttProfile f n = Kt(truthTable f n)` by the table
length `2 ^ n`. The bracketing pair transfers: `ttKtRate f ≤ 1` for every function
(`ttKtRate_le_one`), and table witnesses of vanishing table-normalized densities
force `ttKtRate f = 0` (`ttKtRate_eq_zero_of_witnesses`).

What is **not** claimed: any sequence separating the `Kt`-rate from the untimed
`K`-rate. A sequence of positive `Kt`-rate and zero `K`-rate would exhibit
computational depth as a density; the package proves the two bracketing theorems
only.

## The probabilistic layer

Probabilistic time-bounded complexity replaces the single program run by a majority
over random tapes. On a machine with a context slot the natural convention is to pass
the randomness **as** a distinguished context, so no machine changes are needed:
`TimedKt/Probabilistic.lean` counts, for each program and time bound, the length-`R`
random tapes (functions `Fin R → Bool`, `2^R` of them, entering the machine as
bitstrings) on which a clocked run produces `x` within the bound, and prices

```
pKt(x) = min { |p| + ⌈log₂ t⌉ : p produces x within t transitions on ≥ 2/3 of the tapes }
```

with the tape length minimized over but not priced — randomness is free, only
description and time are priced, the convention of Oliveira's `rKt` (ICALP 2019) and
the `pKt` of Goldberg, Kabanets, Lu, and Oliveira (CCC 2022). The conditional form
needs no new machine either: `pKt_cond x y` passes the pair of the conditioning
string and the tape as the context (`ctxJoin`).

The deterministic embedding is exact (`pKt_le_Kt`, `pKt_cond_le_Kt`): an attained
`Kt`-witness runs with empty context, so flipping the single erase bit at its root
(the flagged context flag for an embed node, the comp erase bit for a composition
node) erases whatever context it receives — it succeeds on **every** random tape, a
majority of `2^R` out of `2^R`, with the same length and transition count. `Kt`
therefore bounds both probabilistic measures with additive constant zero.

What is **not** claimed: `pKt_cond x y ≤ pKt x` — conditioning for the probabilistic
measure. The machine's erase bits discard the whole context, conditioning string and
randomness together, so a probabilistic witness that actually reads its tape cannot
be transported to the joined context; the statement needs a randomness-preserving
erase (a machine variant that discards `y` while keeping the tape), a further
machine-design step recorded as open. The coding theorem and the average-case theory
of the probabilistic measures need probability-weighted enumeration and clocked
self-simulation, deliberately out of scope (clocked self-simulation is the
self-interpreter open item of the invariance scope above).

## Certified evaluation

`TimedKt/Evaluator.lean` makes the operational semantics executable inside the
kernel's reach: `runBounded b c n` mirrors `Run`'s clauses one for one under a
transition budget `b` — computable, structurally recursive on the budget, no fuel —
and returns the exact write-once trace together with the exact transition count, or
`none` when the run does not fit within `b` transitions. Soundness and completeness
identify its successes with the `Run` derivations within budget (`runBounded_sound`,
`runBounded_complete`, packaged as `runBounded_eq_some_iff`), so **bounded halting is
decidable**: `∃ T s, Run c n T s ∧ s ≤ b` is decided by running the evaluator
(`runBounded_isSome_iff`, `decidableRunWithin`), and any success computes `numSteps`
exactly (`numSteps_of_runBounded`).

Every evaluator success is a certificate: `Kt_cond_le_of_runBounded` replays the
witness through the timed universal machine (`universalRuns_of_run`) under a `false`
context flag and the embed bridge (`Kt_cond_le_of_flaggedRuns`), pricing the decoded
output at `encode c + 3 + |d|` program bits plus `⌈log₂ (encode c + s + 4)⌉` time
bits. Concrete certified bounds, every component evaluated by `rfl`/`simp`/kernel
`decide` — no `native_decide` anywhere: `Kt [true] ≤ 9` (`Kt_singleton_true_le`),
`Kt [false] ≤ 7` (`Kt_singleton_false_le`), and the conditional
`Kt_cond [true] [true] ≤ 9` (`Kt_cond_singleton_true_self_le`). Concrete values are
machine-relative — these are the composing-machine values (the flagged-machine
numerals are two smaller: one comp-flag bit, one transition inside the logarithm).

One value is exact. Every run of the composing machine spends its comp flag on top
of a flagged run — itself at least four transitions (flag, prefix scan, at least one
code transition, decode) on at least one program bit — or is a composition of such
runs, which only costs more; so every witness value is at least `2 + ⌈log₂ 5⌉ = 5`
(`five_le_Kt_cond`) — a universal floor, with no enumeration involved. The empty
string attains it with the two-bit program `[false, true]`, embedding the flagged
one-bit eraser whose empty tail parses to `Code.zero`: `Kt_cond [] y = 5` for every
context, and **`Kt [] = 5`** (`Kt_cond_nil`, `Kt_nil`) — the first exact `Kt` value
of the formalization.

## Why the clock is transitions, not fuel

The obvious first candidate for a runtime notion over `Nat.Partrec.Code` is
Mathlib's own evaluation bound: price a computation by the least `Code.evaln` fuel.
That fuel is a value-magnitude quantity, not a work count: the evaluator's input
guard forces fuel past the input value at every node, so a fuel-priced measure taxes
the magnitude of values rather than work performed. The package keeps the least-fuel
cost as `minFuel` (`TimedKt/FuelCost.lean`) together with the divergence theorems:

* `fuel_exceeds_writes_unboundedly` — computations with one write but arbitrarily
  large fuel;
* `succ_transitions_constant_fuel_linear` — the successor makes `1` transition for
  every input, while its fuel is `N + 1`.

The definitions of `Kt` and `Kt_cond` mention neither fuel nor constructor size, and
the fuel module `FuelCost.lean` is outside `Kt.lean`'s import closure (`progSize`
does occur transitively, in the `Run` step ledger and the write-witness penalty —
never in the measure's definition); the two measures meet only in
`TimedKt/Examples.lean`, to be compared. `Run.sandwich` records
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

## Related work

Machine-checked algorithmic information theory has so far covered the *untimed*
measures. Catt and Norrish formalize plain Kolmogorov complexity and its invariance
theorem in HOL4 ([CPP 2021](https://dl.acm.org/doi/10.1145/3437992.3439921)); Forster,
Kunze, and Lauermann formalize plain K in Coq via synthetic computability
([uds-psl/coq-kolmogorov-complexity](https://github.com/uds-psl/coq-kolmogorov-complexity));
and the [`kolmogorov_complexity`](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean)
Lean library this package builds on covers plain and prefix K, algorithmic
probability, and algorithmic statistics. None of these define a time-bounded measure
or prove a time-side simulation theorem. We are not aware of a prior machine-checked
formalization of `Kt` in any proof assistant; corrections are welcome.

## License and attribution

Apache-2.0 (see `LICENSE`). Depends on `kolmogorov_complexity` (Apache-2.0), pinned
by commit in `lakefile.toml`; no code is copied from it.
