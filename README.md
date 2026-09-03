# Erdős problem #74: disproof

[![CI](https://github.com/tadamcz/erdos74/actions/workflows/ci.yml/badge.svg)](https://github.com/tadamcz/erdos74/actions/workflows/ci.yml)

> **Note.** This README, the documentation in `Challenge.lean` and `formalization.yaml` were machine-written by Claude (Anthropic)
> at the direction of Tom Adamczewski, from the FrontierMath Erdős paper, the benchmark files and the module documentation inside
> the proof files, and reviewed by him. The Lean proofs themselves were written by GPT-6 Astra, as described below.

Machine-checked disproof of [Erdős problem #74](https://www.erdosproblems.com/74) in Lean 4 with Mathlib, found autonomously by a
pre-release version of **GPT-6 Astra** (OpenAI) in the **FrontierMath Erdős** benchmark (Adamczewski and Bloom, 2026). The
repository packages the AI-written proofs for the [Palomar registry](https://palomar-registry.org/): `Challenge.lean` is the
small statement a reader audits, `Solution.lean` proves it, and [Comparator](https://github.com/leanprover/comparator) checks that the two
statements coincide and that only the standard axioms are used.

## The result

Erdős, Hajnal and Szemerédi [EHS82] asked: let `f(n) → ∞`, possibly very slowly. Is there a graph of infinite chromatic
number such that every finite subgraph on `n` vertices can be made bipartite by deleting at most `f(n)` edges? They
suspected such a graph exists however slowly `f` diverges; erdosproblems.com lists a $500 prize.

The answer is **no**: there is a function `f(n) → ∞` such that every graph (finite or infinite) in which every finite
`n`-vertex subgraph can be made bipartite by deleting at most `f(n)` edges has finite chromatic number. Formally, the
theorem proved is the negation of the Formal Conjectures statement `Erdos74.erdos_74`, which asserts the existence of
such a graph for *every* `f → ∞`. Every resolution in this repository in fact shows that such graphs are 3-colourable,
but only the negation of the formal conjecture is advertised in `Challenge.lean`. The FrontierMath Erdős paper notes
that the argument appears to work for `f(n) ≍ log n / log log n`; that rate is not part of the formal statement.

The compared declaration, from `Challenge.lean`:

```lean
theorem erdos_74.disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n)) := by
  sorry
```

The formal conjecture asserts the *existence* claim for every `f → ∞`; its negation, proved here, is an existence statement about `f`. 

For disproofs the benchmark file states the conjecture `erdos_N` and its negation `erdos_N.disproof`, both with `sorry`, and the model fills in exactly one. Here the compared theorem is the negation, written out explicitly instead of via `type_of%` (see *Edits* below).

**Fidelity.** The compared theorem is exactly the negation of the Formal Conjectures statement. Points a reader should be aware of:
(1) `f : ℕ → ℕ` is integer-valued and `Tendsto f atTop atTop` is the formal sense of `f(n) → ∞`; (2) the graph ranges
over `SimpleGraph V` for a vertex type `V` in an arbitrary universe `u`, and the theorem is universe-polymorphic; (3)
`maxSubgraphEdgeDistToBipartite G n` is the supremum over *all* (not only induced) `n`-vertex subgraphs of the minimum
number of edge deletions making the subgraph bipartite — since edge deletion distance is monotone in the edge set, this
agrees with the maximum over induced subgraphs; it uses `sSup` on `ℕ`, which is `0` for the empty set (graphs with fewer
than `n` vertices), and `sInf`, whose argument set is always nonempty; (4) `G.chromaticNumber = ⊤` is Mathlib's
formalisation of infinite chromatic number. The formal statement asserts only existence of some `f → ∞`; the Lean proofs
construct explicit budgets but no growth rate is advertised.

## Provenance

**Benchmark.** FrontierMath Erdős (Adamczewski and Bloom, 2026) evaluates AI systems on 68 open Erdős problems selected by Thomas F. Bloom, in the Lean proof
assistant, autonomously and under a fixed, disclosed budget ($300 and 72 hours of working time per attempt in the default configuration). The
agent works in a network-isolated Docker container with a Lean 4 toolchain (v4.27.0) and Mathlib, SageMath and Python; its final
`Spec.lean` is checked in a separate pristine container by Comparator against the trusted statement, permitting only `propext`,
`Quot.sound` and `Classical.choice`. The benchmark, harness and statements are public at
[epoch-research/LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems); the paper is in preparation. No human saw or steered the proof search.

**Statement.** The definitions and the statement come verbatim from [`FormalConjectures/ErdosProblems/74.lean`](https://github.com/google-deepmind/formal-conjectures/blob/488aade228ec37880b8fec178c173c07d279bb53/FormalConjectures/ErdosProblems/74.lean) in Google DeepMind's Formal Conjectures at commit `488aade228ec`, where the problem is stated with `sorry` as open. The benchmark isolated the selected statement into [`apn/data/erdos/Isolated/Erdos74.erdos_74.lean`](https://github.com/epoch-research/LeanOpenProblems/blob/77882c437ca1dfefab3b27fa00f1d29788100311/apn/data/erdos/Isolated/Erdos74.erdos_74.lean) (with the FC `answer(sorry) ↔` wrapper removed and a `.disproof` negation added), and that file is exactly what the model received.

**Resolutions.** Several independent attempts resolved this statement; all verified files are included.
"Default configuration" is the deepagent-based agent with subagents, memory and an offline arXiv snapshot under the benchmark's
budget of $300 and 72 hours of working time per attempt; "ReAct agent, larger budget" is a basic agent under a $1,000 budget.
**Cost** is computed from the attempt's exact token counts (from the harness's eval logs) at GPT-6 Astra's standard rates as provided
by OpenAI on 3 September 2026: $10 per million input tokens, $50 per million output tokens, $1 per million cache-read tokens and
$12.50 per million cache-write tokens. The harness itself metered spend at stand-in GPT-5.6 Sol prices, which is what the `usd` figure
in each file name reflects. **Working time** is the harness's `working_time` (time the agent was actually working, excluding waits on
API retries and rate limits), read from the harness's eval logs; the `h` figure in each file name is instead wall-clock time.
The Inspect transcripts are linked for the record (access may be restricted).

| Module | Role | Attempt | Cost | Working time | Tokens, millions (input / output / cache read / cache write) | Inspect log |
|---|---|---|---|---|---|---|
| `Erdos74/Resolutions/Erdos74_118usd_22h.lean` | **primary** (wired to `Solution.lean`) | default configuration, 28 Aug 2026 (benchmark run) | $218 | 15.0 h | 0.04 / 1.7 / 44 / 7.2 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/XPZMV4Vttpzg9Ffp7S2BKh) |
| `Erdos74/Resolutions/Erdos74_25usd_5h.lean` | alternate | ReAct agent, larger budget, 26 Aug 2026 | $47 | 5.0 h | 0.02 / 0.3 / 16 / 1.1 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/azYP4n7z4uELLofhEHA6Ev) |
| `Erdos74/Resolutions/Erdos74_46usd_6h.lean` | alternate | ReAct agent, larger budget, 26 Aug 2026 (re-run) | $84 | 6.0 h | 0.04 / 0.7 / 18 / 2.4 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/Gwo8829ijia8kjDmp6wHKq) |
| `Erdos74/Resolutions/Erdos74_81usd_13h.lean` | alternate | default configuration, 2 Sep 2026 | $150 | 8.0 h | 0.06 / 1.1 / 30 / 5.2 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/oQQQye6GFubTyEcNDRKbY2) |
| `Erdos74/Resolutions/Erdos74_99usd_17h.lean` | alternate | default configuration, 31 Aug 2026 | $183 | 12.0 h | 0.03 / 1.5 / 34 / 6.1 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/YEPWohsDWZZNaRG2QQ3Pa6) |
| `Erdos74/Resolutions/Erdos74_146usd_19h.lean` | alternate | default configuration, 28 Aug 2026 (re-run) | $271 | 19.0 h | 0.05 / 2.0 / 65 / 8.5 | [transcript](https://viewer.hawk.hawkbench.com/permalink/sample/gWbugBEYhF8F6sS9TGJwjY) |

## Proof account

The accounts below paraphrase the module documentation the model wrote inside each file; they describe the Lean proofs actually
present. They are not a human verification of the mathematics beyond what Comparator establishes.

**`Erdos74_118usd_22h`** (default configuration, 28 Aug 2026 (benchmark run)). Develops finite binary-colouring defect and a local profile for finite graphs (`E74`), proves a finite-profile exclusion (`not_exists_infinite_chromatic_of_finite_profile_exclusion`) and constructs a divergent envelope function `exists_finite_profile_envelope`; the counterexample `E74.counterexample` packages an `f → ∞` for which no graph of infinite chromatic number satisfies the profile bound.

**`Erdos74_25usd_5h`** (ReAct agent, larger budget, 26 Aug 2026). Exhibits a slowly divergent budget `slowBudget` such that every finite graph whose `n`-vertex subgraphs are within `slowBudget n` edges of bipartite is 3-colourable (`finite_three_colorable_of_slow_budget`); infinite chromatic number would force a finite witness of non-3-colourability, contradiction.

**`Erdos74_46usd_6h`** (ReAct agent, larger budget, 26 Aug 2026 (re-run)). For each `D`, `finite_distance_witness` bounds the size of a subgraph witnessing bipartization distance `d` inside any finite non-3-colourable graph of distance at most `D`, via a bounded-radius extraction or plateau compression with a two-apex closure; `diagonal_rate` then supplies a monotone divergent `f` with `f (N d) < d`, and coloring compactness gives a global 3-colouring.

**`Erdos74_81usd_13h`** (default configuration, 2 Sep 2026). Constructs graph-independent finite thresholds: every finite non-3-colourable graph contains a small finite edge set on which every Boolean colouring has at least `k` monochromatic edges (strong induction on bad edges, ball repair, four-level annulus gluing). A sufficiently slowly divergent budget stays below `k` on these certificates, so every finite subgraph is 3-colourable; finite-colour compactness rules out infinite chromatic number.

**`Erdos74_99usd_17h`** (default configuration, 31 Aug 2026). Constructs a slowly divergent budget for which all finite subgraphs are 3-colourable: an independent odd-cycle transversal is localised near an arbitrary cut's bad edges, short closed-walk parity supports reduce the number of bad edges, and separated buffers let every stage reuse the same third colour; compactness supplies a 3-colouring of the whole graph.

**`Erdos74_146usd_19h`** (default configuration, 28 Aug 2026 (re-run)). Uses an explicit slowly divergent budget; bounded local deletion sets give sparse binary parity corrections whose successive differences have integer potential lifts (a finite-dimensional affine Helly theorem is proved for this), a doubling recurrence yields a 3-colouring of each finite subgraph, and graph-colouring compactness gives a global 3-colouring.

**Informal summary from the FrontierMath Erdős paper** (Thomas F. Bloom, appendix; a fuller sketch is on the problem page of
erdosproblems.com): The formalisation proves the existence statement, but the argument appears to give `f(n) ≍ log n / log log n`. It is
elementary and proceeds inductively: consider a sequence `G = G_0 ⊇ G_1 ⊇ ⋯` where `G_k` has no odd cycles of length
`O(k)` and is obtained from `G_{k-1}` by deleting few edges. Eventually (if `G` is finite, which can be assumed by
compactness) such a `G_k` is bipartite. A gluing argument, using that `G_k` and `G_{k-1}` differ in only a small number
of edges, shows how a 3-colouring of `G_k` (with the location of the third colour carefully controlled) yields a
3-colouring of `G_{k-1}` with similar control, and eventually a 3-colouring of `G_0`. After an initial examination the
paper judges the six disproofs to consist of three distinct arguments.

## Repository layout

- `Challenge.lean` — the statement surface: definitions copied verbatim from the benchmark statement and the compared theorem with `sorry`.
- `Solution.lean` — imports the primary resolution module, in whose environment the compared theorem is proved.
- `Erdos74.lean`, `Erdos74/Resolutions/` — the AI-written proof module(s); `Erdos74.lean` imports the primary one.
- Alternate resolutions are built as the separate Lake library `Erdos74Alternates`; each is a self-contained copy of the statement preamble plus its own proof, so they are never imported together.
- `comparator.json` — Comparator configuration naming `Erdos74.erdos_74.disproof`.
- `formalization.yaml` — structured metadata (provenance, sources, classification, automation, review) in the mathlib-initiative v0.4 format.
- `provenance/` — SHA-256 sums of the benchmark output files and unified diffs from them to the modules here.
- `scripts/verify-comparator.sh` runs the pinned Comparator, lean4export, NanoDa and Landrun locally (Linux); `scripts/validate-formalization.rb` checks the metadata file.
- `.github/workflows/ci.yml` — builds the project and runs Comparator (layout from the Palomar template; the template's doc-gen4 job is omitted because the modules import all of Mathlib).

## Edits relative to the benchmark output

The proof modules are the model's final `Spec.lean` files, verified by the benchmark, with only the following mechanical changes; the
exact diffs are in `provenance/`. The toolchain was moved from Lean v4.27.0 / Mathlib (via Formal Conjectures at commit
`488aade2`) to Lean v4.28.0 / Mathlib v4.28.0, the oldest release Palomar accepts; the only change this required is the
`loopless` adjustment listed below for the files it affects.

- `Erdos74_118usd_22h.lean` (SHA-256 of the benchmark output: `e9e9c244e5be1215805ac11ce355474d7fea26f9af665e182f1033df0c98837f`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - removed the sorry'd stub of the original conjecture `erdos_74` (lines 57–65 of the original) together with its docstring
  - restated `Erdos74.erdos_74.disproof` explicitly (the original used `¬ (type_of% @Erdos74.erdos_74)`, which referenced the removed stub) and added a docstring
  - port to Mathlib v4.28.0: Mathlib v4.28.0 changed the field `SimpleGraph.loopless` from `Irreflexive Adj` to the class `Std.Irrefl Adj`, so proofs of that field need a `constructor` step (or an anonymous-constructor wrapper) and uses of `G.loopless` as a function become `G.loopless.irrefl`. Changed lines:
    - line 70: `loopless := by intro x h; exact G.loopless x h.1` → `loopless := by constructor; intro x h; exact G.loopless.irrefl x h.1`
    - line 79: `loopless := by intro x h; exact G.loopless x h.1` → `loopless := by constructor; intro x h; exact G.loopless.irrefl x h.1`
    - line 1077: `loopless := by intro s h; exact h.1 rfl` → `loopless := by constructor; intro s h; exact h.1 rfl`
    - line 1462: inserted `constructor` at the start of the `loopless := by` block
    - line 1466: `| inl x => exact G.loopless x h.1` → `| inl x => exact G.loopless.irrefl x h.1`
- `Erdos74_25usd_5h.lean` (SHA-256 of the benchmark output: `1cc61ae3084e801dc0c6ed06b0508d3a40e56877fe38b9d7e79a7b787c818934`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - no other changes (react-agent file: statement contained only the proved direction)
  - port to Mathlib v4.28.0: Mathlib v4.28.0 changed the field `SimpleGraph.loopless` from `Irreflexive Adj` to the class `Std.Irrefl Adj`, so proofs of that field need a `constructor` step (or an anonymous-constructor wrapper) and uses of `G.loopless` as a function become `G.loopless.irrefl`. Changed lines:
    - line 265: inserted `constructor` at the start of the `loopless := by` block
    - line 268: `exact (Gs i).loopless x ha` → `exact (Gs i).loopless.irrefl x ha`
    - line 1220: `loopless := by intro x h; exact h.1 rfl }` → `loopless := by constructor; intro x h; exact h.1 rfl }`
- `Erdos74_46usd_6h.lean` (SHA-256 of the benchmark output: `74dc4b7949f54ff81f8203c4a72a0b15bcae2329434ce3500f9426a3f351f982`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - no other changes (react-agent file: statement contained only the proved direction)
  - port to Mathlib v4.28.0: Mathlib v4.28.0 changed the field `SimpleGraph.loopless` from `Irreflexive Adj` to the class `Std.Irrefl Adj`, so proofs of that field need a `constructor` step (or an anonymous-constructor wrapper) and uses of `G.loopless` as a function become `G.loopless.irrefl`. Changed lines:
    - line 311: `loopless := by intro x; exact fun h => G.loopless x h.1` → `loopless := by constructor; intro x; exact fun h => G.loopless.irrefl x h.1`
    - line 438: inserted `constructor` at the start of the `loopless := by` block
    - line 794: `loopless := by intro x; simp` → `loopless := by constructor; intro x; simp`
    - line 967: `loopless := by intro x; simp` → `loopless := by constructor; intro x; simp`
- `Erdos74_81usd_13h.lean` (SHA-256 of the benchmark output: `f3b42596c9fce48e3c389cf8b06da4afaca654c657f228a33a3ef2497fa1698d`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - removed the sorry'd stub of the original conjecture `erdos_74` (lines 57–65 of the original) together with its docstring
  - restated `Erdos74.erdos_74.disproof` explicitly (the original used `¬ (type_of% @Erdos74.erdos_74)`, which referenced the removed stub) and added a docstring
  - port to Mathlib v4.28.0: Mathlib v4.28.0 changed the field `SimpleGraph.loopless` from `Irreflexive Adj` to the class `Std.Irrefl Adj`, so proofs of that field need a `constructor` step (or an anonymous-constructor wrapper) and uses of `G.loopless` as a function become `G.loopless.irrefl`. Changed lines:
    - line 361: `loopless := fun v h => G.loopless v h.1` → `loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩`
- `Erdos74_99usd_17h.lean` (SHA-256 of the benchmark output: `3488ece82c00f7c142aa891503feac991b323a4c7d847915c416b7d685939812`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - removed the sorry'd stub of the original conjecture `erdos_74` (lines 57–65 of the original) together with its docstring
  - restated `Erdos74.erdos_74.disproof` explicitly (the original used `¬ (type_of% @Erdos74.erdos_74)`, which referenced the removed stub) and added a docstring
  - port to Mathlib v4.28.0: Mathlib v4.28.0 changed the field `SimpleGraph.loopless` from `Irreflexive Adj` to the class `Std.Irrefl Adj`, so proofs of that field need a `constructor` step (or an anonymous-constructor wrapper) and uses of `G.loopless` as a function become `G.loopless.irrefl`. Changed lines:
    - line 82: `loopless := fun v h ↦ G.loopless v h.1` → `loopless := ⟨fun v h ↦ G.loopless.irrefl v h.1⟩`
    - line 97: `loopless := fun v h ↦ G.loopless v h.1` → `loopless := ⟨fun v h ↦ G.loopless.irrefl v h.1⟩`
    - line 1359: inserted `constructor` at the start of the `loopless := by` block
    - line 1689: `exact G.loopless u hab` → `exact G.loopless.irrefl u hab`
- `Erdos74_146usd_19h.lean` (SHA-256 of the benchmark output: `93794de7cfaf04f4a09a364b19b046602ebc3ac851f0f919b27c4ea2bd246740`):
  - line 1: `import FormalConjecturesUtil` → `import Mathlib`
  - removed the sorry'd stub of the original conjecture `erdos_74` (lines 57–65 of the original) together with its docstring
  - restated `Erdos74.erdos_74.disproof` explicitly (the original used `¬ (type_of% @Erdos74.erdos_74)`, which referenced the removed stub) and added a docstring

## Verification

```sh
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux: Comparator + NanoDa under Landrun
```

CI runs the same checks. The compared theorem depends on no `sorry` and on no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`. This repository is prepared for submission to Palomar through the
[submission form](https://submit.palomar-registry.org/) with the full commit SHA; registration is a separate step by the maintainer.

## Licence and attribution

This repository snapshot is licensed under the Apache License 2.0 (see `LICENSE`). The benchmark statement it reproduces is
from Formal Conjectures, © The Formal Conjectures Authors, Apache-2.0 (see `NOTICE`). Cited papers,
erdosproblems.com and Mathlib retain their own licences.
