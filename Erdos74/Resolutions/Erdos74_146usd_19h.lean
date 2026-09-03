import Mathlib

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

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

-- TODO(firsching): add the remaining statements/comments

end Erdos74

/-
The disproof uses an explicit slowly divergent budget. Bounded local deletion
sets give sparse binary parity corrections, whose successive differences have
integer potential lifts. A doubling recurrence yields a three-coloring of each
finite subgraph, and graph-coloring compactness gives a global three-coloring.
-/
namespace E74LocalCutTools

open SimpleGraph

abbrev F2 := ZMod 2

variable {V : Type*}

def LocalCut (G : SimpleGraph V) (l : V → V → F2) (R : ℕ) : Prop :=
  ∀ U : Finset V, U.card ≤ R →
    ∃ c : V → F2, ∀ u ∈ U, ∀ v ∈ U,
      G.Adj u v → c v - c u = l u v

lemma localCut_mono {G : SimpleGraph V} {l : V → V → F2} {R T : ℕ}
    (h : LocalCut G l R) (hTR : T ≤ R) : LocalCut G l T := by
  intro U hU
  exact h U (hU.trans hTR)

lemma localCut_add {G : SimpleGraph V} {l k : V → V → F2} {R : ℕ}
    (hl : LocalCut G l R) (hk : LocalCut G k R) :
    LocalCut G (fun u v => l u v + k u v) R := by
  intro U hU
  obtain ⟨c, hc⟩ := hl U hU
  obtain ⟨d, hd⟩ := hk U hU
  refine ⟨fun v => c v + d v, ?_⟩
  intro u hu v hv huv
  change c v + d v - (c u + d u) = l u v + k u v
  rw [← hc u hu v hv huv, ← hd u hu v hv huv]
  ring

lemma localCut_global [Fintype V] {G : SimpleGraph V} {l : V → V → F2} {R : ℕ}
    (h : LocalCut G l R) (hn : Fintype.card V ≤ R) :
    ∃ c : V → F2, ∀ u v, G.Adj u v → c v - c u = l u v := by
  classical
  obtain ⟨c, hc⟩ := h Finset.univ (by simpa using hn)
  exact ⟨c, fun u v huv => hc u (Finset.mem_univ _) v (Finset.mem_univ _) huv⟩

def Close (H : SimpleGraph V) (r : ℕ) (u v : V) : Prop :=
  ∃ w : H.Walk u v, w.length ≤ r

def CapWitness (H : SimpleGraph V) (S : Set V) (r : ℕ) (v : V) (n : ℕ) : Prop :=
  n = r ∨ ∃ t ∈ S, ∃ w : H.Walk v t, w.length ≤ n

noncomputable def capDist (H : SimpleGraph V) (S : Set V) (r : ℕ) (v : V) : ℕ := by
  classical
  exact Nat.find (show ∃ n, CapWitness H S r v n from ⟨r, Or.inl rfl⟩)

lemma capDist_le_of_witness (H : SimpleGraph V) (S : Set V) (r : ℕ) (v : V) {n : ℕ}
    (hn : CapWitness H S r v n) : capDist H S r v ≤ n := by
  classical
  exact Nat.find_min' _ hn

lemma capDist_le (H : SimpleGraph V) (S : Set V) (r : ℕ) (v : V) :
    capDist H S r v ≤ r :=
  capDist_le_of_witness H S r v (Or.inl rfl)

lemma capDist_spec (H : SimpleGraph V) (S : Set V) (r : ℕ) (v : V) :
    CapWitness H S r v (capDist H S r v) := by
  classical
  exact Nat.find_spec (show ∃ n, CapWitness H S r v n from ⟨r, Or.inl rfl⟩)

lemma capDist_of_mem (H : SimpleGraph V) (S : Set V) (r : ℕ) {v : V} (hv : v ∈ S) :
    capDist H S r v = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply capDist_le_of_witness
  exact Or.inr ⟨v, hv, .nil, by simp⟩

lemma capDist_of_far (H : SimpleGraph V) (S : Set V) (r : ℕ) {v : V}
    (hfar : ∀ t ∈ S, ¬ Close H r v t) : capDist H S r v = r := by
  rcases capDist_spec H S r v with h | ⟨t, ht, w, hw⟩
  · exact h
  · exact False.elim (hfar t ht ⟨w, hw.trans (capDist_le H S r v)⟩)

lemma capDist_adj_le (H : SimpleGraph V) (S : Set V) (r : ℕ) {u v : V}
    (huv : H.Adj u v) : capDist H S r v ≤ capDist H S r u + 1 := by
  rcases capDist_spec H S r u with h | ⟨t, ht, w, hw⟩
  · rw [h]
    exact (capDist_le H S r v).trans (Nat.le_succ r)
  · apply capDist_le_of_witness
    exact Or.inr ⟨t, ht, .cons huv.symm w, by simpa using Nat.succ_le_succ hw⟩

lemma capDist_adj_abs (H : SimpleGraph V) (S : Set V) (r : ℕ) {u v : V}
    (huv : H.Adj u v) :
    |(capDist H S r v : ℤ) - (capDist H S r u : ℤ)| ≤ 1 := by
  have h₁ := capDist_adj_le H S r huv
  have h₂ := capDist_adj_le H S r huv.symm
  rw [abs_le]
  constructor <;> omega

lemma integer_rounding_ne (m u v z : ℤ) (hm : 0 < m) (hz : Odd z)
    (herr : 3 * |m*z + v-u| ≤ m) :
    ((3*u) / (2*m)) % 3 ≠ ((3*v) / (2*m)) % 3 := by
  obtain ⟨k, rfl⟩ := hz
  have hlo : 3*u + (2*m)*(3*(-k-1)+1) ≤ 3*v := by
    nlinarith [neg_abs_le (m*(2*k+1)+v-u)]
  have hhi : 3*v ≤ 3*u + (2*m)*(3*(-k-1)+2) := by
    nlinarith [le_abs_self (m*(2*k+1)+v-u)]
  have hm2 : 0 < 2*m := by omega
  have hlo' := Int.ediv_le_ediv hm2 hlo
  have hhi' := Int.ediv_le_ediv hm2 hhi
  rw [Int.add_mul_ediv_left _ _ (ne_of_gt hm2)] at hlo' hhi'
  intro heq
  omega

def residueThree (z : ℤ) : Fin 3 := ⟨(z % 3).toNat, by omega⟩

lemma residueThree_ne {u v : ℤ} (h : u % 3 ≠ v % 3) : residueThree u ≠ residueThree v := by
  intro heq
  have hval := congrArg Fin.val heq
  dsimp [residueThree] at hval
  apply h
  omega

lemma integer_colorable (G : SimpleGraph V) (m : ℤ) (z : V → V → ℤ) (Y : V → ℤ)
    (hm : 0 < m) (hz : ∀ u v, G.Adj u v → Odd (z u v))
    (herr : ∀ u v, G.Adj u v → 3 * |m*z u v + Y v-Y u| ≤ m) :
    G.Colorable 3 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => residueThree ((3*Y v)/(2*m))) ?_⟩
  intro u v huv
  apply residueThree_ne
  exact integer_rounding_ne m (Y u) (Y v) (z u v) hm (hz u v huv) (herr u v huv)

lemma accumulated_error_step (m a a' Bu Bv bu bv E : ℤ)
    (hold : |m*a+Bv-Bu| ≤ E) (hnew : |(2*m)*a'+bv-bu| ≤ 1) :
    |(2*m)*(a+a') + (2*Bv+bv) - (2*Bu+bu)| ≤ 2*E+1 := by
  obtain ⟨hold₁, hold₂⟩ := abs_le.mp hold
  obtain ⟨hnew₁, hnew₂⟩ := abs_le.mp hnew
  apply abs_le.mpr
  constructor <;> nlinarith


def localWindow (j : ℕ) : ℕ := 64 * (j+1) * 2^j

def largeScale (j : ℕ) : ℕ := (j+1) * localWindow j

def scaleThreshold (j : ℕ) : ℕ := largeScale j ^ (2*j+3)

lemma endpoint_window_bound (j s : ℕ) (hs : s ≤ 4*j+2) :
    (s+1) * (8*2^j+1) ≤ localWindow j := by
  have hr : 1 ≤ 8 * 2^j := by
    have h : 0 < 8 * (2:ℕ)^j := by positivity
    omega
  calc
    (s+1) * (8*2^j+1) ≤ (4*(j+1)) * (2*(8*2^j)) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ = localWindow j := by unfold localWindow; ring

lemma localWindow_pos (j : ℕ) : 0 < localWindow j := by
  unfold localWindow
  positivity

lemma localWindow_mono : Monotone localWindow := by
  intro i j hij
  unfold localWindow
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.succ_le_succ hij))
    (Nat.pow_le_pow_right (by decide) hij)

lemma largeScale_pos (j : ℕ) : 0 < largeScale j := by
  unfold largeScale
  exact Nat.mul_pos (Nat.succ_pos j) (localWindow_pos j)

lemma largeScale_mono : Monotone largeScale := by
  intro i j hij
  exact Nat.mul_le_mul (Nat.succ_le_succ hij) (localWindow_mono hij)

lemma self_le_largeScale (j : ℕ) : j ≤ largeScale j := by
  have h : 1 ≤ localWindow j := localWindow_pos j
  calc
    j ≤ j+1 := Nat.le_succ j
    _ = (j+1)*1 := by omega
    _ ≤ (j+1)*localWindow j := Nat.mul_le_mul_left _ h

lemma scaleThreshold_mono : Monotone scaleThreshold := by
  intro i j hij
  unfold scaleThreshold
  exact (Nat.pow_le_pow_left (largeScale_mono hij) _).trans
    (Nat.pow_le_pow_right (largeScale_pos j) (by omega))

lemma self_le_scaleThreshold (j : ℕ) : j ≤ scaleThreshold j := by
  calc
    j ≤ largeScale j := self_le_largeScale j
    _ = largeScale j ^ 1 := by simp
    _ ≤ scaleThreshold j := Nat.pow_le_pow_right (largeScale_pos j) (by omega)

noncomputable def thresholdInverse (T : ℕ → ℕ) (hT : ∀ n, ∃ j, n ≤ T j) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (hT n)

lemma thresholdInverse_spec (T : ℕ → ℕ) (hT : ∀ n, ∃ j, n ≤ T j) (n : ℕ) :
    n ≤ T (thresholdInverse T hT n) := by
  classical
  exact Nat.find_spec (hT n)

lemma thresholdInverse_le (T : ℕ → ℕ) (hT : ∀ n, ∃ j, n ≤ T j) {n j : ℕ}
    (h : n ≤ T j) : thresholdInverse T hT n ≤ j := by
  classical
  exact Nat.find_min' (hT n) h

lemma thresholdInverse_tendsto (T : ℕ → ℕ) (hT : ∀ n, ∃ j, n ≤ T j)
    (hmono : Monotone T) :
    Filter.Tendsto (thresholdInverse T hT) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 ?_
  intro k
  refine ⟨T k + 1, ?_⟩
  intro n hn
  have hspec := thresholdInverse_spec T hT n
  by_contra h
  have hle : thresholdInverse T hT n ≤ k := by omega
  have hbound := hmono hle
  omega

noncomputable def budget (n : ℕ) : ℕ :=
  thresholdInverse scaleThreshold (fun n => ⟨n, self_le_scaleThreshold n⟩) n

lemma budget_le_of_le_threshold {n j : ℕ} (h : n ≤ scaleThreshold j) : budget n ≤ j :=
  thresholdInverse_le _ _ h

lemma budget_tendsto : Filter.Tendsto budget Filter.atTop Filter.atTop :=
  thresholdInverse_tendsto _ _ scaleThreshold_mono


/- Shared graph interfaces for the finite obstruction. -/

noncomputable def edgeIndicator (A : Finset (Sym2 V)) (u v : V) : F2 := by
  classical
  exact if s(u, v) ∈ A then 1 else 0

def BipOn (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∃ c : V → F2, ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → c v - c u = 1

def HasDeletion (G : SimpleGraph V) (U : Finset V) (k : ℕ) : Prop :=
  ∃ F : Finset (Sym2 V), F.card ≤ k ∧ BipOn (G.deleteEdges (F : Set (Sym2 V))) U

def SmallHit (G : SimpleGraph V) (F : Finset (Sym2 V)) (L : ℕ) : Prop :=
  LocalCut (G.deleteEdges (F : Set (Sym2 V))) (fun _ _ => 1) L

def HereditaryBudget (G : SimpleGraph V) (f : ℕ → ℕ) : Prop :=
  ∀ U : Finset V, HasDeletion G U (f U.card)

lemma hasDeletion_mono {G : SimpleGraph V} {U : Finset V} {j k : ℕ}
    (h : HasDeletion G U j) (hjk : j ≤ k) : HasDeletion G U k := by
  obtain ⟨F, hF, hc⟩ := h
  exact ⟨F, hF.trans hjk, hc⟩

end E74LocalCutTools

/-
# Finite-dimensional affine Helly

A bounded finite subfamily determines the intersection of any family of affine
subspaces in a finite-dimensional vector space. This gives affine Helly without
any finiteness assumption on the index type or any ordering of the field.
-/

namespace E74LocalCutTools

section AffineHelly

variable {K W I : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- The empty affine subspace has height zero; a nonempty one has height one
more than the dimension of its direction. -/
private noncomputable def affineHeight (Q : AffineSubspace K W) : ℕ := by
  classical
  exact if Q = ⊥ then 0 else Module.finrank K Q.direction + 1

variable [FiniteDimensional K W]

private theorem affineHeight_strictMono :
    StrictMono (affineHeight (K := K) (W := W)) := by
  classical
  intro S T hST
  have hT : T ≠ ⊥ := ne_bot_of_gt hST
  by_cases hS : S = ⊥
  · simp [affineHeight, hS, hT]
  · have hdim := Submodule.finrank_lt_finrank_of_lt
      (AffineSubspace.direction_lt_of_nonempty hST
        ((AffineSubspace.nonempty_iff_ne_bot S).2 hS))
    simpa only [affineHeight, if_neg hS, if_neg hT] using Nat.add_lt_add_right hdim 1

private theorem affine_finite_intersection_aux (P : I → AffineSubspace K W)
    (Q : AffineSubspace K W) :
    ∃ s : Finset I, s.card ≤ affineHeight Q ∧
      Q ⊓ (⨅ i ∈ s, P i) ≤ ⨅ i, P i := by
  classical
  induction Q using (measure (affineHeight (K := K) (W := W))).wf.induction with
  | h Q ih =>
    by_cases hQ : Q ≤ ⨅ i, P i
    · exact ⟨∅, by simp, by simpa using hQ⟩
    · have hex : ∃ i, ¬ Q ≤ P i := by
        simpa only [le_iInf_iff, not_forall] using hQ
      obtain ⟨i, hi⟩ := hex
      have hlt : Q ⊓ P i < Q := inf_lt_left.mpr hi
      have hheight := affineHeight_strictMono hlt
      obtain ⟨s, hs, hsP⟩ := ih (Q ⊓ P i) hheight
      refine ⟨insert i s, (Finset.card_insert_le _ _).trans ?_, ?_⟩
      · omega
      · simpa only [Finset.iInf_insert, inf_assoc] using hsP

/-- An arbitrary intersection of affine subspaces is determined by at most
`finrank K W + 1` members of the family. -/
theorem affine_iInf_eq_finite (P : I → AffineSubspace K W) :
    ∃ s : Finset I, s.card ≤ Module.finrank K W + 1 ∧
      (⨅ i ∈ s, P i) = ⨅ i, P i := by
  obtain ⟨s, hs, hle⟩ := affine_finite_intersection_aux P ⊤
  refine ⟨s, ?_, le_antisymm ?_ ?_⟩
  · rw [affineHeight, if_neg top_ne_bot, AffineSubspace.direction_top, finrank_top] at hs
    exact hs
  · simpa using hle
  · exact le_iInf fun i => le_iInf fun _ => iInf_le P i

/-- Affine Helly over any field, for an arbitrary (possibly infinite) index type. -/
theorem affine_helly (P : I → AffineSubspace K W)
    (h : ∀ s : Finset I, s.card ≤ Module.finrank K W + 1 →
      ∃ x : W, ∀ i ∈ s, x ∈ P i) :
    ∃ x : W, ∀ i, x ∈ P i := by
  obtain ⟨s, hs, heq⟩ := affine_iInf_eq_finite P
  obtain ⟨x, hx⟩ := h s hs
  have hx' : x ∈ ⨅ i ∈ s, P i := by
    simpa only [AffineSubspace.mem_iInf_iff] using hx
  rw [heq] at hx'
  exact ⟨x, (AffineSubspace.mem_iInf_iff P x).1 hx'⟩

end AffineHelly

end E74LocalCutTools

/-
# Finite branching certificates for local edge deletions

A failure of every small hitting set has a finite vertex-set obstruction.
The branches are indexed by all ordered pairs in the initial obstruction;
nonedges and duplicate unordered pairs cause no difficulty.  In particular,
the argument does not require the ambient vertex type to be finite.
-/

namespace E74LocalCutTools

open SimpleGraph

variable {V : Type*}

/-- The size bound for the depth-`k` branching certificate. -/
def branchingBound (L : ℕ) : ℕ → ℕ
  | 0 => L
  | k + 1 => L + L ^ 2 * branchingBound L k

/-- A spare unit in the bound makes the recursive estimate immediate. -/
lemma branchingBound_add_one_le {L k : ℕ} (hL : 2 ≤ L) :
    branchingBound L k + 1 ≤ L ^ (2 * k + 2) := by
  have hbase : L + 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 2 : ℤ)]
  induction k with
  | zero => simpa [branchingBound] using hbase
  | succ k ih =>
      calc
        branchingBound L (k + 1) + 1 = L + L ^ 2 * branchingBound L k + 1 := rfl
        _ ≤ L ^ 2 * (branchingBound L k + 1) := by nlinarith
        _ ≤ L ^ 2 * L ^ (2 * k + 2) := Nat.mul_le_mul_left _ ih
        _ = L ^ (2 * (k + 1) + 2) := by
          rw [← pow_add]
          congr 1
          omega

lemma branchingBound_le_power {L k : ℕ} (hL : 2 ≤ L) :
    branchingBound L k ≤ L ^ (2 * k + 3) := by
  calc
    branchingBound L k ≤ branchingBound L k + 1 := Nat.le_succ _
    _ ≤ L ^ (2 * k + 2) := branchingBound_add_one_le hL
    _ ≤ L ^ (2 * k + 3) := Nat.pow_le_pow_right (by omega) (by omega)

private lemma obstruction_of_not_smallHit_empty {G : SimpleGraph V} {L : ℕ}
    (h : ¬ SmallHit G ∅ L) :
    ∃ U : Finset V, U.card ≤ L ∧ ¬ BipOn G U := by
  classical
  by_contra! hn
  apply h
  simpa only [SmallHit, Finset.coe_empty, SimpleGraph.deleteEdges_empty, LocalCut, BipOn]
    using hn

/-- If no deletion of at most `k` pairs makes all `L`-vertex sets bipartite,
there is a bounded finite vertex set that cannot be bipartized by `k` deletions.
No assumption that the deleted pairs are edges is needed. -/
theorem branching_obstruction (G : SimpleGraph V) (L k : ℕ)
    (h : ∀ F : Finset (Sym2 V), F.card ≤ k → ¬ SmallHit G F L) :
    ∃ U : Finset V, U.card ≤ branchingBound L k ∧ ¬ HasDeletion G U k := by
  classical
  induction k generalizing G with
  | zero =>
      obtain ⟨U, hU, hnU⟩ := obstruction_of_not_smallHit_empty (h ∅ (by simp))
      refine ⟨U, hU, ?_⟩
      rintro ⟨F, hF, hb⟩
      have hFempty : F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hF)
      subst F
      apply hnU
      simpa only [Finset.coe_empty, SimpleGraph.deleteEdges_empty] using hb
  | succ k ih =>
      obtain ⟨U₀, hU₀, hnU₀⟩ := obstruction_of_not_smallHit_empty (h ∅ (by simp))
      -- Deleting any one pair leaves a graph with no hitting set of budget `k`.
      have hres : ∀ e : Sym2 V, ∀ F : Finset (Sym2 V), F.card ≤ k →
          ¬ SmallHit (G.deleteEdges {e}) F L := by
        intro e F hF hs
        apply h (insert e F)
          ((Finset.card_insert_le e F).trans (Nat.succ_le_succ hF))
        simpa only [SmallHit, SimpleGraph.deleteEdges_deleteEdges, Finset.coe_insert,
          Set.singleton_union] using hs
      have hob : ∀ e : Sym2 V, ∃ U : Finset V,
          U.card ≤ branchingBound L k ∧ ¬ HasDeletion (G.deleteEdges {e}) U k :=
        fun e => ih (G.deleteEdges {e}) (hres e)
      choose W hW hnW using hob
      let P : Finset (V × V) := U₀ ×ˢ U₀
      let U : Finset V := U₀ ∪ P.biUnion (fun p => W s(p.1, p.2))
      have hP : P.card ≤ L ^ 2 := by
        calc
          P.card = U₀.card * U₀.card := Finset.card_product _ _
          _ ≤ L * L := Nat.mul_le_mul hU₀ hU₀
          _ = L ^ 2 := by ring
      have hUnion : (P.biUnion (fun p => W s(p.1, p.2))).card ≤
          P.card * branchingBound L k :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun p _ => hW s(p.1, p.2))
      refine ⟨U, ?_, ?_⟩
      · calc
          U.card ≤ U₀.card + (P.biUnion (fun p => W s(p.1, p.2))).card :=
            Finset.card_union_le _ _
          _ ≤ L + P.card * branchingBound L k := Nat.add_le_add hU₀ hUnion
          _ ≤ L + L ^ 2 * branchingBound L k :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hP) _
          _ = branchingBound L (k + 1) := rfl
      · rintro ⟨B, hB, c, hc⟩
        -- A coloring after deleting `B` must delete an edge inside `U₀`.
        have hhit : ∃ u ∈ U₀, ∃ v ∈ U₀, G.Adj u v ∧ s(u, v) ∈ B := by
          by_contra! hn
          apply hnU₀
          refine ⟨c, ?_⟩
          intro u hu v hv huv
          exact hc u (Finset.mem_union_left _ hu) v (Finset.mem_union_left _ hv)
            (SimpleGraph.deleteEdges_adj.mpr ⟨huv, hn u hu v hv huv⟩)
        obtain ⟨u, hu, v, hv, _, heB⟩ := hhit
        have hWU : W s(u, v) ⊆ U := by
          intro w hw
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, hw⟩
        -- The branch has already deleted this edge, so `B.erase` has budget `k`.
        apply hnW s(u, v)
        refine ⟨B.erase s(u, v), ?_, c, ?_⟩
        · rw [Finset.card_erase_of_mem heB]
          omega
        · intro x hx y hy hxy
          apply hc x (hWU hx) y (hWU hy)
          simp only [SimpleGraph.deleteEdges_adj, Finset.mem_coe, Set.mem_singleton_iff,
            Finset.mem_erase] at hxy ⊢
          exact ⟨hxy.1.1, fun hmem => hxy.2 ⟨hxy.1.2, hmem⟩⟩

/-- Uniform bounded local deletion budgets yield one bounded small hitting set. -/
theorem smallHit_of_local_deletions (G : SimpleGraph V) {L k : ℕ} (hL : 2 ≤ L)
    (h : ∀ U : Finset V, U.card ≤ L ^ (2 * k + 3) → HasDeletion G U k) :
    ∃ F : Finset (Sym2 V), F.card ≤ k ∧ SmallHit G F L := by
  classical
  by_contra! hn
  obtain ⟨U, hU, hnU⟩ := branching_obstruction G L k hn
  exact hnU (h U (hU.trans (branchingBound_le_power hL)))

end E74LocalCutTools

/-
# Bridge from the Erdős 74 specification to hereditary finite deletion budgets

The natural supremum is bounded before it is used, and the natural infimum
is attained by a finite edge-deletion set. Only the graph-distance definitions
above are used here.
-/

open SimpleGraph

namespace Erdos74

variable {V : Type*} {G : SimpleGraph V}

/-- The edges of a finite-vertex subgraph form a finite set of size at most the
square of its number of vertices. -/
lemma finiteSubgraph_edgeSet_bound (A : G.Subgraph) (hA : A.verts.Finite) :
    A.edgeSet.Finite ∧ A.edgeSet.ncard ≤ A.verts.ncard ^ 2 := by
  have hsub : A.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' (A.verts ×ˢ A.verts) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : A.Adj u v := he
      exact ⟨(u, v), ⟨A.edge_vert huv, A.edge_vert huv.symm⟩, rfl⟩
  have hprod := hA.prod hA
  have himage := hprod.image (fun p : V × V => s(p.1, p.2))
  refine ⟨himage.subset hsub, ?_⟩
  calc
    A.edgeSet.ncard ≤ ((fun p : V × V => s(p.1, p.2)) ''
        (A.verts ×ˢ A.verts)).ncard := Set.ncard_le_ncard hsub himage
    _ ≤ (A.verts ×ˢ A.verts).ncard := Set.ncard_image_le hprod
    _ = A.verts.ncard ^ 2 := by rw [Set.ncard_prod, pow_two]

/-- Deleting every edge is always an admissible bipartite deletion. -/
lemma edgeCount_mem_edgeDistancesToBipartite (A : G.Subgraph) :
    A.edgeSet.ncard ∈ SimpleGraph.edgeDistancesToBipartite A := by
  refine ⟨A.edgeSet, Set.Subset.rfl, ?_, rfl⟩
  refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 2)) ?_⟩
  intro u v huv
  exact False.elim (huv.2 huv.1)

lemma edgeDistancesToBipartite_nonempty (A : G.Subgraph) :
    (SimpleGraph.edgeDistancesToBipartite A).Nonempty :=
  ⟨_, edgeCount_mem_edgeDistancesToBipartite A⟩

/-- The natural infimum in the specification is an actual deletion distance. -/
lemma minEdgeDistToBipartite_mem (A : G.Subgraph) :
    SimpleGraph.minEdgeDistToBipartite A ∈ SimpleGraph.edgeDistancesToBipartite A :=
  Nat.sInf_mem (edgeDistancesToBipartite_nonempty A)

lemma minEdgeDistToBipartite_le_edgeCount (A : G.Subgraph) :
    SimpleGraph.minEdgeDistToBipartite A ≤ A.edgeSet.ncard :=
  Nat.sInf_le (edgeCount_mem_edgeDistancesToBipartite A)

lemma minEdgeDistToBipartite_le_sq (A : G.Subgraph) (hA : A.verts.Finite) :
    SimpleGraph.minEdgeDistToBipartite A ≤ A.verts.ncard ^ 2 :=
  (minEdgeDistToBipartite_le_edgeCount A).trans (finiteSubgraph_edgeSet_bound A hA).2

/-- This boundedness is essential when using the natural `sSup` in the spec. -/
lemma subgraphEdgeDistsToBipartite_bddAbove (G : SimpleGraph V) (n : ℕ) :
    BddAbove (SimpleGraph.subgraphEdgeDistsToBipartite G n) := by
  refine ⟨n ^ 2, ?_⟩
  rintro k ⟨A, hcard, hfinite, rfl⟩
  simpa only [hcard] using minEdgeDistToBipartite_le_sq A hfinite

lemma minEdgeDistToBipartite_le_max (A : G.Subgraph) (hA : A.verts.Finite) :
    SimpleGraph.minEdgeDistToBipartite A ≤
      SimpleGraph.maxSubgraphEdgeDistToBipartite G A.verts.ncard := by
  exact le_csSup (subgraphEdgeDistsToBipartite_bddAbove G A.verts.ncard)
    ⟨A, rfl, hA, rfl⟩

/-- Extract a genuinely finite, edge-supported deletion witness from the spec's
bound on its maximum distance. -/
lemma finiteSubgraph_deletion_of_max {f : ℕ → ℕ}
    (h : ∀ n, SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)
    (A : G.Subgraph) (hA : A.verts.Finite) :
    ∃ F : Finset (Sym2 V), (F : Set (Sym2 V)) ⊆ A.edgeSet ∧
      F.card ≤ f A.verts.ncard ∧ (A.deleteEdges (F : Set (Sym2 V))).coe.IsBipartite := by
  classical
  obtain ⟨E, hEsub, hEbip, hEcard⟩ := minEdgeDistToBipartite_mem A
  have hEfinite : E.Finite := (finiteSubgraph_edgeSet_bound A hA).1.subset hEsub
  refine ⟨hEfinite.toFinset, ?_, ?_, ?_⟩
  · simpa only [hEfinite.coe_toFinset] using hEsub
  · rw [← Set.ncard_eq_toFinset_card E hEfinite, hEcard]
    exact (minEdgeDistToBipartite_le_max A hA).trans (h A.verts.ncard)
  · simpa only [SimpleGraph.Subgraph.coe_deleteEdges_eq, hEfinite.coe_toFinset] using hEbip

end Erdos74

namespace E74LocalCutTools

variable {V : Type*} {G : SimpleGraph V}

private lemma finTwo_sub_eq_one {a b : Fin 2} (h : a ≠ b) :
    ZMod.finEquiv 2 b - ZMod.finEquiv 2 a = 1 := by
  revert a b
  decide

/-- A two-coloring on an induced subgraph after deletion extends to the ambient
vertex type, giving exactly the `BipOn` interface. -/
lemma bipOn_of_induce_deleteEdges_isBipartite (U : Finset V) (E : Set (Sym2 V))
    (h : ((((⊤ : G.Subgraph).induce (U : Set V)).deleteEdges E).coe).IsBipartite) :
    BipOn (G.deleteEdges E) U := by
  classical
  obtain ⟨c⟩ := h
  let color : V → F2 := fun v =>
    if hv : v ∈ U then ZMod.finEquiv 2 (c ⟨v, hv⟩) else 0
  refine ⟨color, ?_⟩
  intro u hu v hv huv
  rw [SimpleGraph.deleteEdges_adj] at huv
  have hadj : ((((⊤ : G.Subgraph).induce (U : Set V)).deleteEdges E).coe).Adj
      ⟨u, hu⟩ ⟨v, hv⟩ :=
    ⟨⟨hu, hv, huv.1⟩, huv.2⟩
  simpa only [color, dif_pos hu, dif_pos hv] using finTwo_sub_eq_one (c.valid hadj)

/-- The exact hypothesis in the specification implies the finite hereditary
budget used by the local-cut tools. -/
theorem hereditaryBudget_of_max {f : ℕ → ℕ}
    (h : ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n) :
    HereditaryBudget G f := by
  classical
  intro U
  let A : G.Subgraph := (⊤ : G.Subgraph).induce (U : Set V)
  have hA : A.verts.Finite := U.finite_toSet
  obtain ⟨F, _, hFcard, hFbip⟩ := Erdos74.finiteSubgraph_deletion_of_max h A hA
  refine ⟨F, ?_, bipOn_of_induce_deleteEdges_isBipartite U (F : Set (Sym2 V)) hFbip⟩
  simpa only [A, SimpleGraph.Subgraph.induce_verts, Set.ncard_coe_finset] using hFcard

/-- Hereditary budgets pull back along an injective graph homomorphism.  No
monotonicity of the budget function or finiteness of the graphs is required. -/
lemma hereditaryBudget_of_injective_hom {W : Type*} {H : SimpleGraph W} {f : ℕ → ℕ}
    (h : HereditaryBudget G f) (φ : H →g G) (hφ : Function.Injective φ) :
    HereditaryBudget H f := by
  classical
  intro U
  obtain ⟨F, hFcard, c, hc⟩ := h (U.image φ)
  have hUcard : (U.image φ).card = U.card := Finset.card_image_of_injective U hφ
  let F' : Finset (Sym2 W) := F.preimage (Sym2.map φ) (Sym2.map.injective hφ).injOn
  have hF'card : F'.card ≤ F.card := by
    dsimp only [F']
    rw [Finset.card_preimage]
    exact Finset.card_filter_le _ _
  refine ⟨F', hF'card.trans (by simpa only [hUcard] using hFcard),
    (fun w => c (φ w)), ?_⟩
  intro u hu v hv huv
  rw [SimpleGraph.deleteEdges_adj] at huv
  apply hc (φ u) (Finset.mem_image_of_mem φ hu) (φ v) (Finset.mem_image_of_mem φ hv)
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨φ.map_rel huv.1, ?_⟩
  simpa only [F', Finset.mem_coe, Finset.mem_preimage, Sym2.map_pair_eq] using huv.2

/-- Restriction to any subgraph; in particular this applies to the finite
subgraphs in the coloring compactness theorem. -/
lemma hereditaryBudget_subgraph {f : ℕ → ℕ} (h : HereditaryBudget G f)
    (H : G.Subgraph) : HereditaryBudget H.coe f :=
  hereditaryBudget_of_injective_hom h H.hom SimpleGraph.Subgraph.hom_injective

/-- Restriction to an induced graph on an arbitrary set of vertices. -/
lemma hereditaryBudget_induce {f : ℕ → ℕ} (h : HereditaryBudget G f) (s : Set V) :
    HereditaryBudget (G.induce s) f := by
  rw [SimpleGraph.induce_eq_coe_induce_top s]
  exact hereditaryBudget_subgraph h ((⊤ : G.Subgraph).induce s)

end E74LocalCutTools

/-
# Sparse local parity selection

The unknown edge labels live in the finite-dimensional space `F → F2`, even
when the vertex type is infinite. For each small vertex set, the labels that
admit a local potential form an affine subspace. Affine Helly produces one
labeling that works on every small vertex set, and its support is the required
subset of `F`.

No assumption that `F` consists of actual graph edges is needed.
-/

namespace E74LocalCutTools

variable {V : Type*}

/-- Extend a coordinate function on `F` by zero, evaluated at an unordered pair. -/
private noncomputable def sparseEval (F : Finset (Sym2 V)) (e : Sym2 V) :
    (F → F2) →ₗ[F2] F2 := by
  classical
  exact {
    toFun := fun x => if he : e ∈ F then x ⟨e, he⟩ else 0
    map_add' := by intro x y; by_cases he : e ∈ F <;> simp [he]
    map_smul' := by intro t x; by_cases he : e ∈ F <;> simp [he]
  }

/-- The edge labels on `F` that admit a potential on the internal edges of `U`. -/
private noncomputable def sparseAffine (G : SimpleGraph V) (F : Finset (Sym2 V))
    (U : Finset V) : AffineSubspace F2 (F → F2) where
  carrier := {x | ∃ c : V → F2, ∀ u ∈ U, ∀ v ∈ U,
    G.Adj u v → c v - c u = 1 + sparseEval F s(u, v) x}
  smul_vsub_vadd_mem := by
    intro t x y z hx hy hz
    obtain ⟨cx, hcx⟩ := hx
    obtain ⟨cy, hcy⟩ := hy
    obtain ⟨cz, hcz⟩ := hz
    refine ⟨fun v => t * (cx v - cy v) + cz v, ?_⟩
    intro u hu v hv huv
    change t * (cx v - cy v) + cz v - (t * (cx u - cy u) + cz u) =
      1 + sparseEval F s(u, v) (t • (x - y) + z)
    calc
      t * (cx v - cy v) + cz v - (t * (cx u - cy u) + cz u) =
          t * ((cx v - cx u) - (cy v - cy u)) + (cz v - cz u) := by ring
      _ = 1 + sparseEval F s(u, v) (t • (x - y) + z) := by
        rw [hcx u hu v hv huv, hcy u hu v hv huv, hcz u hu v hv huv,
          map_add, map_smul, map_sub, smul_eq_mul]
        ring

/-- In characteristic two, the parity correction is well defined on unordered pairs. -/
private def sparseParity (c : V → F2) : Sym2 V → F2 :=
  Sym2.lift ⟨fun u v => 1 + (c v - c u), by
    intro u v
    simp only [CharTwo.sub_eq_add]
    rw [add_comm (c v) (c u)]⟩

/-- A bounded finite family of local constraints has a simultaneous solution. -/
private theorem sparseFinite_feasible {G : SimpleGraph V} {F : Finset (Sym2 V)}
    {L R : ℕ} (h : SmallHit G F L) (hwin : (F.card + 1) * R ≤ L)
    (s : Finset {U : Finset V // U.card ≤ R}) (hs : s.card ≤ F.card + 1) :
    ∃ x : F → F2, ∀ U ∈ s, x ∈ sparseAffine G F U.val := by
  classical
  let W : Finset V := s.biUnion fun U => U.val
  have hW : W.card ≤ L := by
    calc
      W.card ≤ ∑ U ∈ s, U.val.card := Finset.card_biUnion_le
      _ ≤ ∑ _U ∈ s, R := Finset.sum_le_sum fun U _ => U.property
      _ = s.card * R := by simp
      _ ≤ (F.card + 1) * R := Nat.mul_le_mul_right R hs
      _ ≤ L := hwin
  obtain ⟨c, hc⟩ := h W hW
  let x : F → F2 := fun e => sparseParity c e.val
  refine ⟨x, ?_⟩
  intro U hU
  refine ⟨c, ?_⟩
  intro u hu v hv huv
  have huW : u ∈ W := Finset.mem_biUnion.mpr ⟨U, hU, hu⟩
  have hvW : v ∈ W := Finset.mem_biUnion.mpr ⟨U, hU, hv⟩
  by_cases he : s(u, v) ∈ F
  · have hx : sparseEval F s(u, v) x = 1 + (c v - c u) := by
      simp [sparseEval, x, he, sparseParity]
    rw [hx, CharTwo.add_cancel_left]
  · have huv' : (G.deleteEdges (F : Set (Sym2 V))).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩
    simpa [sparseEval, he] using hc u huW v hvW huv'

/-- A small deletion set admits a sparse parity correction on every `R`-vertex set.

This holds for arbitrary vertex types, and `F` may contain nonedges or loops. -/
theorem sparse_localCut {V : Type*} {G : SimpleGraph V} {F : Finset (Sym2 V)}
    {L R : ℕ} (h : SmallHit G F L) (hwin : (F.card + 1) * R ≤ L) :
    ∃ X : Finset (Sym2 V), X ⊆ F ∧
      LocalCut G (fun u v => 1 + edgeIndicator X u v) R := by
  classical
  obtain ⟨x, hx⟩ := affine_helly
    (fun U : {U : Finset V // U.card ≤ R} => sparseAffine G F U.val) (by
      intro s hs
      apply sparseFinite_feasible h hwin s
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hs)
  let X : Finset (Sym2 V) := F.filter fun e => sparseEval F e x = 1
  have hbits : ∀ t : F2, t = 0 ∨ t = 1 := by decide
  have hext : ∀ u v, sparseEval F s(u, v) x = edgeIndicator X u v := by
    intro u v
    by_cases he : s(u, v) ∈ F
    · rcases hbits (sparseEval F s(u, v) x) with ht | ht
      · simp [edgeIndicator, X, he, ht]
      · simp [edgeIndicator, X, he, ht]
    · simp [sparseEval, edgeIndicator, X, he]
  refine ⟨X, Finset.filter_subset _ _, ?_⟩
  intro U hU
  obtain ⟨c, hc⟩ := hx ⟨U, hU⟩
  refine ⟨c, ?_⟩
  intro u hu v hv huv
  change c v - c u = 1 + edgeIndicator X u v
  rw [← hext u v]
  exact hc u hu v hv huv

end E74LocalCutTools

/-
# Capped-distance integer lifts of sparse local cuts

Only the endpoints of the finite set `A` are used in the affine Helly space.
The set `A` is allowed to contain nonedges and diagonal pairs: flip constraints
are imposed only on actual graph edges belonging to `A`.
-/

namespace E74LocalCutTools

open SimpleGraph

variable {V : Type*}

/-- An affine equation on two coordinates, including its possibly empty fiber. -/
private def liftEquation {T : Type*} (u v : T) (t : F2) :
    AffineSubspace F2 (T → F2) where
  carrier := {p | p v - p u = t}
  smul_vsub_vadd_mem := by
    intro c p₁ p₂ p₃ h₁ h₂ h₃
    change c * (p₁ v - p₂ v) + p₃ v - (c * (p₁ u - p₂ u) + p₃ u) = t
    calc
      _ = c * ((p₁ v - p₁ u) - (p₂ v - p₂ u)) + (p₃ v - p₃ u) := by ring
      _ = t := by rw [h₁, h₂, h₃]; ring

/-- A local potential is constant along any residual walk supported in its window. -/
private theorem lift_walk_constant {G : SimpleGraph V} {A : Finset (Sym2 V)}
    {U : Finset V} {c : V → F2}
    (hc : ∀ u ∈ U, ∀ v ∈ U, G.Adj u v → c v - c u = edgeIndicator A u v)
    {u v : V} (w : (G.deleteEdges (A : Set (Sym2 V))).Walk u v) :
    (∀ x ∈ w.support, x ∈ U) → c v = c u := by
  classical
  induction w with
  | nil => intro _; rfl
  | @cons u t v h w ih =>
    intro hU
    have hu : u ∈ U := hU u (by simp)
    have ht : t ∈ U := hU t (by
      simp only [Walk.support_cons, List.mem_cons]
      exact Or.inr w.start_mem_support)
    have hadj := SimpleGraph.deleteEdges_adj.mp h
    have hn : s(u, t) ∉ A := hadj.2
    have he : c t = c u := by
      apply sub_eq_zero.mp
      simpa [edgeIndicator, hn] using hc u hu t ht hadj.1
    apply Eq.trans (ih ?_) he
    intro x hx
    exact hU x (by simp only [Walk.support_cons, List.mem_cons]; exact Or.inr hx)

/-- Helly supplies a potential on any finite endpoint set. The two kinds of
constraints have separate indices, so neither is lost if both apply to a pair. -/
private theorem lift_endpoint_potential {G : SimpleGraph V} {A : Finset (Sym2 V)}
    {R r : ℕ} (S : Finset V) (hr : 1 ≤ r)
    (hwin : (S.card + 1) * (r + 1) ≤ R)
    (hcut : LocalCut G (edgeIndicator A) R) :
    ∃ p : S → F2,
      (∀ u v : S, G.Adj u v → s((u : V), (v : V)) ∈ A → p v - p u = 1) ∧
      (∀ u v : S, Close (G.deleteEdges (A : Set (Sym2 V))) r u v → p v - p u = 0) := by
  classical
  let H := G.deleteEdges (A : Set (Sym2 V))
  let E := {uv : S × S // G.Adj uv.1 uv.2 ∧ s((uv.1 : V), (uv.2 : V)) ∈ A}
  let C := {uv : S × S // Close H r uv.1 uv.2}
  let I := E ⊕ C
  let chosen (i : C) : H.Walk i.1.1 i.1.2 := Classical.choose i.2
  have chosen_le (i : C) : (chosen i).length ≤ r := Classical.choose_spec i.2
  let T : I → Finset V := Sum.elim
    (fun i : E => {(i.1.1 : V), (i.1.2 : V)})
    (fun i : C => (chosen i).support.toFinset)
  have hTcard (i : I) : (T i).card ≤ r + 1 := by
    cases i with
    | inl i =>
      have hpair : ({(i.1.1 : V), (i.1.2 : V)} : Finset V).card ≤ 2 := by
        simpa using Finset.card_insert_le (i.1.1 : V) {(i.1.2 : V)}
      exact hpair.trans (by omega)
    | inr i =>
      calc
        (T (Sum.inr i)).card ≤ (chosen i).support.length := List.toFinset_card_le _
        _ = (chosen i).length + 1 := Walk.length_support _
        _ ≤ r + 1 := Nat.add_le_add_right (chosen_le i) 1
  let Q : I → AffineSubspace F2 (S → F2) := Sum.elim
    (fun i : E => liftEquation i.1.1 i.1.2 1)
    (fun i : C => liftEquation i.1.1 i.1.2 0)
  have hsmall (J : Finset I) (hJ : J.card ≤ Module.finrank F2 (S → F2) + 1) :
      ∃ p : S → F2, ∀ i ∈ J, p ∈ Q i := by
    have hJ' : J.card ≤ S.card + 1 := by
      simpa only [Module.finrank_pi, Fintype.card_coe] using hJ
    let W := J.biUnion T
    have hW : W.card ≤ R := by
      calc
        W.card ≤ ∑ i ∈ J, (T i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ J, (r + 1) := Finset.sum_le_sum (fun i _ => hTcard i)
        _ = J.card * (r + 1) := by simp
        _ ≤ (S.card + 1) * (r + 1) := Nat.mul_le_mul_right _ hJ'
        _ ≤ R := hwin
    obtain ⟨c, hc⟩ := hcut W hW
    have hsub : ∀ i ∈ J, T i ⊆ W := by
      intro i hi x hx
      exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
    refine ⟨fun u => c u, ?_⟩
    intro i hi
    cases i with
    | inl i =>
      change c i.1.2 - c i.1.1 = 1
      have hu : (i.1.1 : V) ∈ W := hsub (Sum.inl i) hi (by simp [T])
      have hv : (i.1.2 : V) ∈ W := hsub (Sum.inl i) hi (by simp [T])
      simpa [edgeIndicator, i.2.2] using hc i.1.1 hu i.1.2 hv i.2.1
    | inr i =>
      change c i.1.2 - c i.1.1 = 0
      apply sub_eq_zero.mpr
      apply lift_walk_constant hc (chosen i)
      intro x hx
      exact hsub (Sum.inr i) hi (List.mem_toFinset.mpr hx)
  obtain ⟨p, hp⟩ := affine_helly Q hsmall
  refine ⟨p, ?_, ?_⟩
  · intro u v huv hA
    exact hp (Sum.inl ⟨(u, v), huv, hA⟩)
  · intro u v huv
    exact hp (Sum.inr ⟨(u, v), huv⟩)

/-- The two possible endpoint values, stated without any enumeration of vertices. -/
private theorem lift_f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 := by omega
  rcases hval with h | h
  · left
    rw [← ZMod.natCast_zmod_val x, h]
    rfl
  · right
    rw [← ZMod.natCast_zmod_val x, h]
    rfl

/-- A finite sparse local cut admits an integer lift with error at most one.
No finiteness hypothesis on `V`, or edge/loop restriction on `A`, is required. -/
theorem integer_lift {V : Type*} {G : SimpleGraph V} {A : Finset (Sym2 V)}
    {R r : ℕ} (hr : 1 ≤ r) (hwin : (2 * A.card + 1) * (r + 1) ≤ R)
    (hcut : LocalCut G (edgeIndicator A) R) :
    ∃ a : V → V → ℤ, ∃ b : V → ℤ,
      (∀ u v, G.Adj u v → (a u v : F2) = edgeIndicator A u v) ∧
      (∀ u v, G.Adj u v → |(r : ℤ) * a u v + b v - b u| ≤ 1) := by
  classical
  let S : Finset V := A.biUnion Sym2.toFinset
  have hScard : S.card ≤ 2 * A.card := by
    calc
      S.card ≤ ∑ e ∈ A, e.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ A, 2 := Finset.sum_le_sum (fun e _ => by
        rw [Sym2.card_toFinset]
        split_ifs <;> omega)
      _ = 2 * A.card := by simp [Nat.mul_comm]
  have hends {u v : V} (h : s(u, v) ∈ A) : u ∈ S ∧ v ∈ S := by
    constructor <;> apply Finset.mem_biUnion.mpr <;>
      refine ⟨s(u, v), h, ?_⟩ <;> simp
  have hSwin : (S.card + 1) * (r + 1) ≤ R :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hScard 1)).trans hwin
  obtain ⟨p, hpA, hpC⟩ := lift_endpoint_potential S hr hSwin hcut
  let P : V → ℤ := fun v => if hv : v ∈ S then ((p ⟨v, hv⟩).val : ℤ) else 0
  let S₀ : Set V := {v | ∃ hv : v ∈ S, p ⟨v, hv⟩ = 0}
  let H := G.deleteEdges (A : Set (Sym2 V))
  let D : V → ℕ := capDist H S₀ r
  let b : V → ℤ := fun v => -(D v : ℤ)
  have hP (v : S) : P v = ((p v).val : ℤ) := by simp [P, v.2]
  have hPcast (v : S) : (P v : F2) = p v := by
    rw [hP]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hb (v : S) : b v = -(r : ℤ) * P v := by
    rcases lift_f2_cases (p v) with hp0 | hp1
    · have hv0 : (v : V) ∈ S₀ := ⟨v.2, hp0⟩
      have hDv : D v = 0 := capDist_of_mem H S₀ r hv0
      change -(D v : ℤ) = -(r : ℤ) * P v
      rw [hDv, hP, hp0]
      simp
    · have hfar : ∀ t ∈ S₀, ¬ Close H r (v : V) t := by
        rintro t ⟨ht, hpt⟩ hvt
        have he := sub_eq_zero.mp (hpC v ⟨t, ht⟩ hvt)
        rw [hp1, hpt] at he
        exact zero_ne_one he
      have hDv : D v = r := capDist_of_far H S₀ r hfar
      change -(D v : ℤ) = -(r : ℤ) * P v
      rw [hDv, hP, hp1]
      simp [ZMod.val_one]
  let a : V → V → ℤ := fun u v => if s(u, v) ∈ A then P v - P u else 0
  refine ⟨a, b, ?_, ?_⟩
  · intro u v huv
    by_cases hA : s(u, v) ∈ A
    · obtain ⟨hu, hv⟩ := hends hA
      change ((if s(u, v) ∈ A then P v - P u else 0 : ℤ) : F2) = _
      rw [if_pos hA, Int.cast_sub, hPcast ⟨v, hv⟩, hPcast ⟨u, hu⟩]
      simpa [edgeIndicator, hA] using hpA ⟨u, hu⟩ ⟨v, hv⟩ huv hA
    · simp [a, edgeIndicator, hA]
  · intro u v huv
    by_cases hA : s(u, v) ∈ A
    · obtain ⟨hu, hv⟩ := hends hA
      change |(r : ℤ) * (if s(u, v) ∈ A then P v - P u else 0) + b v - b u| ≤ 1
      rw [if_pos hA, hb ⟨v, hv⟩, hb ⟨u, hu⟩]
      have he : (r : ℤ) * (P v - P u) + -(r : ℤ) * P v - -(r : ℤ) * P u = 0 := by ring
      rw [he]
      norm_num
    · have hH : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, hA⟩
      have hlip := capDist_adj_abs H S₀ r hH
      change |(r : ℤ) * (if s(u, v) ∈ A then P v - P u else 0) + -(D v : ℤ) - -(D u : ℤ)| ≤ 1
      simp only [if_neg hA, mul_zero, zero_add, sub_neg_eq_add]
      have he : -(D v : ℤ) + (D u : ℤ) = -((D v : ℤ) - (D u : ℤ)) := by ring
      rw [he, abs_neg]
      exact hlip

end E74LocalCutTools

/-
# Finite multiscale three-coloring

The sparse local-cut selection and integer lifting results are explicit hypotheses
with their shared interfaces.  No implementation of either result is assumed by
this module.  Integer potentials are accumulated by a doubling recurrence, and
the final coloring uses the checked integer rounding theorem from `E74Base`.
-/

namespace E74LocalCutTools

open SimpleGraph
open scoped symmDiff

variable {V : Type*}

private lemma assemble_indicator_symmDiff [DecidableEq V]
    (A B : Finset (Sym2 V)) (u v : V) :
    edgeIndicator (A ∆ B) u v = edgeIndicator A u v + edgeIndicator B u v := by
  classical
  by_cases ha : s(u, v) ∈ A <;> by_cases hb : s(u, v) ∈ B <;>
    simp [edgeIndicator, Finset.mem_symmDiff, ha, hb, CharTwo.add_self_eq_zero]

private lemma assemble_cancel_ones (x y : F2) :
    (1 + x) + (1 + y) = x + y := by
  calc
    _ = (1 + 1) + (x + y) := by ring
    _ = x + y := by simp [CharTwo.add_self_eq_zero]

private lemma assemble_cancel_repeat (x y : F2) : x + (y + x) = y := by
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

/-- The vertex count itself is a sufficient terminal multiscale index. -/
lemma self_le_localWindow (j : ℕ) : j ≤ localWindow j := by
  calc
    j ≤ j + 1 := Nat.le_succ _
    _ ≤ 64 * (j + 1) := by omega
    _ = 64 * (j + 1) * 1 := by simp
    _ ≤ localWindow j := Nat.mul_le_mul_left _ Nat.one_le_two_pow

/-- A small-hit profile at the fixed scales forces a finite graph to be
three-colorable.  The only graph-specific inputs besides the profile are the
exact sparse-selection and integer-lift interfaces. -/
theorem finite_colorable_of_profile [Fintype V] (G : SimpleGraph V)
    (hsparse : ∀ (F : Finset (Sym2 V)) (L R : ℕ),
      SmallHit G F L → (F.card + 1) * R ≤ L →
      ∃ X : Finset (Sym2 V), X ⊆ F ∧
        LocalCut G (fun u v => 1 + edgeIndicator X u v) R)
    (hlift : ∀ (A : Finset (Sym2 V)) (R r : ℕ), 1 ≤ r →
      (2 * A.card + 1) * (r + 1) ≤ R → LocalCut G (edgeIndicator A) R →
      ∃ a : V → V → ℤ, ∃ b : V → ℤ,
        (∀ u v, G.Adj u v → (a u v : F2) = edgeIndicator A u v) ∧
        (∀ u v, G.Adj u v → |(r : ℤ) * a u v + b v - b u| ≤ 1))
    (hprofile : ∀ j : ℕ, ∃ F : Finset (Sym2 V),
      F.card ≤ j ∧ SmallHit G F (largeScale j)) :
    G.Colorable 3 := by
  classical
  -- Sparse representatives at each scale; the zero-scale one is empty.
  have hX : ∀ j : ℕ, ∃ X : Finset (Sym2 V), X.card ≤ j ∧
      LocalCut G (fun u v => 1 + edgeIndicator X u v) (localWindow j) := by
    intro j
    obtain ⟨F, hF, hhit⟩ := hprofile j
    obtain ⟨X, hXF, hcut⟩ := hsparse F (largeScale j) (localWindow j) hhit
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ hF))
    exact ⟨X, (Finset.card_le_card hXF).trans hF, hcut⟩
  choose X hXcard hXcut using hX
  have hXzero : X 0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hXcard 0))
  -- The existential induction realizes α' = α + a and B' = 2B + b.
  have hacc : ∀ j : ℕ, ∃ α : V → V → ℤ, ∃ B : V → ℤ,
      (∀ u v, G.Adj u v → (α u v : F2) = edgeIndicator (X j) u v) ∧
      (∀ u v, G.Adj u v →
        |(4 * (2 : ℤ)^j) * α u v + B v - B u| ≤ (2 : ℤ)^j - 1) := by
    intro j
    induction j with
    | zero =>
        refine ⟨fun _ _ => 0, fun _ => 0, ?_, ?_⟩
        · intro u v huv
          simp [hXzero, edgeIndicator]
        · intro u v huv
          simp
    | succ j ih =>
        obtain ⟨α, B, hα, hB⟩ := ih
        let A : Finset (Sym2 V) := X (j + 1) ∆ X j
        have hAcard : A.card ≤ 2 * j + 1 := by
          calc
            A.card ≤ (X (j + 1) ∪ X j).card :=
              Finset.card_le_card Finset.symmDiff_subset_union
            _ ≤ (X (j + 1)).card + (X j).card := Finset.card_union_le _ _
            _ ≤ 2 * j + 1 := by
              have h₁ := hXcard (j + 1)
              have h₂ := hXcard j
              omega
        have hAcut : LocalCut G (edgeIndicator A) (localWindow j) := by
          convert localCut_add
            (localCut_mono (hXcut (j + 1)) (localWindow_mono (Nat.le_succ j)))
            (hXcut j) using 1
          funext u v
          exact (assemble_indicator_symmDiff (X (j + 1)) (X j) u v).trans
            (assemble_cancel_ones _ _).symm
        obtain ⟨a, b, ha, hb⟩ := hlift A (localWindow j) (8 * 2^j)
          (by have := Nat.one_le_two_pow (n := j); omega)
          (endpoint_window_bound j (2 * A.card) (by omega)) hAcut
        refine ⟨fun u v => α u v + a u v, fun v => 2 * B v + b v, ?_, ?_⟩
        · intro u v huv
          simp only [Int.cast_add, hα u v huv, ha u v huv, A,
            assemble_indicator_symmDiff]
          exact assemble_cancel_repeat _ _
        · intro u v huv
          have hnew : |(2 * (4 * (2 : ℤ)^j)) * a u v + b v - b u| ≤ 1 := by
            have hscale : (2 : ℤ) * (4 * 2^j) = ((8 * 2^j : ℕ) : ℤ) := by
              push_cast
              ring
            rw [hscale]
            exact hb u v huv
          have herr := accumulated_error_step (4 * (2 : ℤ)^j) (α u v) (a u v)
            (B u) (B v) (b u) (b v) ((2 : ℤ)^j - 1) (hB u v huv) hnew
          have hm : (2 : ℤ) * (4 * 2^j) = 4 * 2^(j + 1) := by
            rw [pow_succ]
            ring
          have hE : 2 * ((2 : ℤ)^j - 1) + 1 = (2 : ℤ)^(j + 1) - 1 := by
            rw [pow_succ]
            ring
          rw [hm, hE] at herr
          exact herr
  -- At the terminal scale the local binary potential is global.
  let M := Fintype.card V
  obtain ⟨α, B, hα, hB⟩ := hacc M
  obtain ⟨h, hh⟩ := localCut_global (hXcut M) (self_le_localWindow M)
  let bit : V → ℤ := fun v => (h v).val
  let m : ℤ := 4 * 2^M
  apply integer_colorable G m (fun u v => α u v + (bit v - bit u))
    (fun v => B v - m * bit v)
  · dsimp [m]
    positivity
  · intro u v huv
    apply ZMod.intCast_eq_one_iff_odd.mp
    change ((α u v + (bit v - bit u) : ℤ) : F2) = 1
    simp only [Int.cast_add, Int.cast_sub, bit, Int.cast_natCast,
      ZMod.natCast_zmod_val, hα u v huv]
    rw [hh u v huv]
    exact assemble_cancel_repeat _ _
  · intro u v huv
    have hcancel : m * (α u v + (bit v - bit u)) +
        (B v - m * bit v) - (B u - m * bit u) = m * α u v + B v - B u := by ring
    rw [hcancel]
    calc
      3 * |m * α u v + B v - B u| ≤ 3 * ((2 : ℤ)^M - 1) :=
        mul_le_mul_of_nonneg_left (hB u v huv) (by norm_num)
      _ ≤ m := by
        dsimp [m]
        have : 0 ≤ (2 : ℤ)^M := by positivity
        linarith

/-- The fixed inverse budget supplies the profile through the finite branching
certificate, hence forces three-colorability for every finite graph. -/
theorem finite_colorable_of_hereditary [Fintype V] (G : SimpleGraph V)
    (hsparse : ∀ (F : Finset (Sym2 V)) (L R : ℕ),
      SmallHit G F L → (F.card + 1) * R ≤ L →
      ∃ X : Finset (Sym2 V), X ⊆ F ∧
        LocalCut G (fun u v => 1 + edgeIndicator X u v) R)
    (hlift : ∀ (A : Finset (Sym2 V)) (R r : ℕ), 1 ≤ r →
      (2 * A.card + 1) * (r + 1) ≤ R → LocalCut G (edgeIndicator A) R →
      ∃ a : V → V → ℤ, ∃ b : V → ℤ,
        (∀ u v, G.Adj u v → (a u v : F2) = edgeIndicator A u v) ∧
        (∀ u v, G.Adj u v → |(r : ℤ) * a u v + b v - b u| ≤ 1))
    (hbudget : HereditaryBudget G budget) : G.Colorable 3 := by
  apply finite_colorable_of_profile G hsparse hlift
  intro j
  have hL : 2 ≤ largeScale j :=
    (show 2 ≤ largeScale 0 by norm_num [largeScale, localWindow]).trans
      (largeScale_mono (Nat.zero_le j))
  apply smallHit_of_local_deletions G hL
  intro U hU
  exact hasDeletion_mono (hbudget U) (budget_le_of_le_threshold hU)

end E74LocalCutTools

namespace E74LocalCutTools

open SimpleGraph

/-- The explicit divergent deletion budget forces three-colorability. -/
theorem colorable_of_hereditary {V : Type*} (G : SimpleGraph V)
    (h : HereditaryBudget G budget) : G.Colorable 3 := by
  classical
  apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
  intro H hH
  letI : Fintype H.verts := hH.fintype
  exact (finite_colorable_of_hereditary H.coe
    (fun _ _ _ => sparse_localCut)
    (fun _ _ _ => integer_lift)
    (hereditaryBudget_subgraph h H)).some

end E74LocalCutTools

universe u

open E74LocalCutTools in
/--
**Disproof of Erdős problem #74.** It is not the case that for every `f : ℕ → ℕ` tending to
infinity there is a graph of infinite chromatic number all of whose `n`-vertex subgraphs can
be made bipartite by deleting at most `f n` edges. Equivalently, some `f → ∞` forces every
such graph to have finite chromatic number. This is the negation of the statement `erdos_74`
of the benchmark file.
-/
theorem Erdos74.erdos_74.disproof : ¬ (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ (V : Type u) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
    ∀ n, Erdos74.SimpleGraph.maxSubgraphEdgeDistToBipartite G n ≤ f n)) := by
  intro h
  obtain ⟨V, G, htop, hbudget⟩ := h budget budget_tendsto
  have hc : G.Colorable 3 := colorable_of_hereditary G (hereditaryBudget_of_max hbudget)
  exact (SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨3, hc⟩) htop
