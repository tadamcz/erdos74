import Mathlib

/-!
# Erdős problem #74: disproof

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)

Erdős, Hajnal and Szemerédi [EHS82] asked: let `f(n) → ∞`, possibly very slowly. Is there a graph
of infinite chromatic number such that every finite subgraph on `n` vertices can be made bipartite
by deleting at most `f(n)` edges? They suspected such a graph exists however slowly `f` diverges;
erdosproblems.com lists a $500 prize.

The answer is **no**: there is a function `f(n) → ∞` such that every graph (finite or infinite) in
which every finite `n`-vertex subgraph can be made bipartite by deleting at most `f(n)` edges has
finite chromatic number. Formally, the theorem proved is the negation of the Formal Conjectures
statement `Erdos74.erdos_74`, which asserts the existence of such a graph for *every* `f → ∞`.
Every resolution in this repository in fact shows that such graphs are 3-colourable, but only the
negation of the formal conjecture is advertised in `Challenge.lean`. The FrontierMath Erdős paper
notes that the argument appears to work for `f(n) ≍ log n / log log n`; that rate is not part of
the formal statement.

This file is the small statement surface a reader should audit: the theorem
`Erdos74.erdos_74.disproof` below is the compared declaration, and the conjecture is refuted (its
negation is proved) in `Solution.lean` and the module it imports. Only the theorem's `sorry` is
filled in there.

The definitions and the statement inside this file are copied verbatim from
`FormalConjectures/ErdosProblems/74.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind,
Apache-2.0) at commit `488aade228ec37880b8fec178c173c07d279bb53`, which is the statement the AI system was
given in the FrontierMath Erdős benchmark (isolated statement file
`apn/data/erdos/Isolated/Erdos74.erdos_74.lean` in [LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems) at commit
`77882c437ca1dfefab3b27fa00f1d29788100311`).
-/
open Filter SimpleGraph

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given subgraph `A`, this is the set of all numbers `k` such that `A` can be made
bipartite by deleting `k` edges.
-/
def SimpleGraph.edgeDistancesToBipartite {G : SimpleGraph V} (A : G.Subgraph) : Set ℕ :=
  { (E.ncard) | (E : Set (Sym2 V)) (_ : E ⊆ A.edgeSet) (_ : IsBipartite (A.deleteEdges E).coe)}

/--
The minimum number of edges that must be deleted from a subgraph `A` to make it bipartite.
-/
noncomputable def SimpleGraph.minEdgeDistToBipartite {G : SimpleGraph V} (A : G.Subgraph) : ℕ :=
  sInf <| SimpleGraph.edgeDistancesToBipartite A

/--
For a graph `G` and a number `n`, this is the set of `minEdgeDistToBipartite A` for all
induced subgraphs `A` of `G` on `n` vertices.
-/
def SimpleGraph.subgraphEdgeDistsToBipartite (G : SimpleGraph V) (n : ℕ) : Set ℕ :=
  { (SimpleGraph.minEdgeDistToBipartite A) |
    (A : Subgraph G) (_ : A.verts.ncard = n) (_ : A.verts.Finite) }

/--
For a given graph $G$ and size $n$, this defines the smallest number $k$
such that any subgraph of $G$ on $n$ vertices can be made bipartite by deleting
at most $k$ edges.

This value is optimal because it is the maximum of `minEdgeDistToBipartite` taken
over all $n$-vertex subgraphs. This means there exists at least one $n$-vertex
subgraph that requires exactly this many edge deletions.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.maxSubgraphEdgeDistToBipartite
    (G : SimpleGraph V) (n : ℕ) : ℕ := sSup <| SimpleGraph.subgraphEdgeDistsToBipartite G n

/--
**Disproof of Erdős problem #74.** The bracketed statement is the conjecture `erdos_74` exactly as
formalized in Formal Conjectures: for every $f(n) \to \infty$ there is a graph of infinite chromatic
number such that every finite subgraph on $n$ vertices can be made bipartite by deleting at most
$f(n)$ edges. This theorem says that is false: there is some $f(n) \to \infty$ such that every graph
(finite or infinite, on a vertex type in any universe) whose $n$-vertex subgraphs can all be made
bipartite by deleting at most $f(n)$ edges has finite chromatic number.
-/
theorem erdos_74.disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, G.maxSubgraphEdgeDistToBipartite n ≤ f n)) := by
  sorry

end Erdos74
