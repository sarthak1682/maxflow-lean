import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Chain

/-
# Max-Flow Min-Cut Theorem Formalization Project
Team: Sarthak Parikh, Rasmus Valeth
-/

open Finset BigOperators Classical

-- We assume a type V for vertices, which must be finite and have decidable equality.
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Definitions: Network and Flow -/

structure FlowNetwork (V : Type*) [Fintype V] where
  source : V
  sink   : V
  capacity : V → V → ℚ
  c_nonneg : ∀ u v, 0 ≤ capacity u v
  src_neq_sink : source ≠ sink

structure Flow (N : FlowNetwork V) where
  f : V → V → ℚ
  /-- Capacity constraint: flow cannot exceed capacity -/
  capacity_le : ∀ u v, f u v ≤ N.capacity u v
  /-- Skew symmetry simplifies residual arithmetic -/
  skew : ∀ u v, f u v = - f v u
  /-- Flow Conservation: Net flow out of any node (except s, t) is 0 -/
  conservation : ∀ v, v ≠ N.source → v ≠ N.sink → ∑ u, f u v = 0

namespace FlowNetwork

variable {N : FlowNetwork V}

/-- The value of a flow is the net flow out of the source. -/
def _root_.Flow.flowValue (fl : Flow N) : ℚ :=
  ∑ v, fl.f N.source v

/-! ### 2. Cuts and Weak Duality -/

/-- A Cut is just a Finset containing the source but not the sink.
    Using Finset avoids manual Decidable instances. -/
structure Cut (N : FlowNetwork V) where
  S : Finset V
  source_in : N.source ∈ S
  sink_not_in : N.sink ∉ S

/-- The capacity of a cut is the sum of capacities of edges going from S to T. -/
def cutCapacity (C : Cut N) : ℚ :=
  ∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, N.capacity u v



-- **some lemmas from weak_duality**
-- extracted some lemmas from weak_duality to reuse in optimality_condition
-- could also use them directly in weak_diality, whatever's better for readability
omit [DecidableEq V] in
lemma flow_out_eq_zero (fl : Flow N) (u : V) (h_src : u ≠ N.source) (h_sink : u ≠ N.sink) :
    ∑ v, fl.f u v = 0 := by
  have h_neg : ∑ v, fl.f u v = ∑ v, - fl.f v u := by
    apply Finset.sum_congr rfl
    intro v _
    rw [fl.skew]
  rw [h_neg, Finset.sum_neg_distrib, fl.conservation u h_src h_sink, neg_zero]

omit [DecidableEq V] in
lemma flow_internal_sum_zero (fl : Flow N) (S : Finset V) :
    ∑ u ∈ S, ∑ v ∈ S, fl.f u v = 0 := by
  let vol := ∑ u ∈ S, ∑ v ∈ S, fl.f u v
  have h_vol_neg : vol = - vol := calc
    vol = ∑ v ∈ S, ∑ u ∈ S, fl.f u v := Finset.sum_comm
    _   = ∑ v ∈ S, ∑ u ∈ S, - fl.f v u := by
            apply Finset.sum_congr rfl
            intro v _
            apply Finset.sum_congr rfl
            intro u _
            exact fl.skew u v
    _   = - ∑ v ∈ S, ∑ u ∈ S, fl.f v u := by simp only [Finset.sum_neg_distrib]
    _   = - vol := rfl
  linarith

lemma flow_sum_split (fl : Flow N) (C : Cut N) : ∑ u ∈ C.S, ∑ v, fl.f u v =
                 (∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v) +
                 (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f u v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl C.S (fl.f u)).symm



/-- **Weak Duality**: The value of any flow is ≤ capacity of any cut. -/
theorem weak_duality (fl : Flow N) (C : Cut N) : fl.flowValue ≤ cutCapacity C := by
  -- Helper: Net flow *out* of any node u (where u ≠ s, t) is 0.
  have h_out_zero : ∀ u, u ≠ N.source → u ≠ N.sink → ∑ v, fl.f u v = 0 := by
    intro u h_src h_sink
    -- Rewrite outgoing flow as negative incoming flow
    have h_neg : ∑ v, fl.f u v = ∑ v, - fl.f v u := by
      apply Finset.sum_congr rfl
      intro v _
      rw [fl.skew]
    rw [h_neg, Finset.sum_neg_distrib, fl.conservation u h_src h_sink, neg_zero]

  -- Express flowValue as the sum of divergences over S.
  have h_val_eq_div_S : fl.flowValue = ∑ u ∈ C.S, ∑ v, fl.f u v := by
    rw [← Finset.sum_erase_add _ _ C.source_in]
    have h_src_term : ∑ v, fl.f N.source v = fl.flowValue := rfl
    rw [h_src_term]
    have h_rest_zero : ∑ u ∈ C.S.erase N.source, ∑ v, fl.f u v = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.mem_erase] at hu
      have u_ne_sink : u ≠ N.sink := fun h => C.sink_not_in (h ▸ hu.2)
      exact h_out_zero u hu.1 u_ne_sink
    rw [h_rest_zero, zero_add]

  -- Decompose the flow sum into Internal (S->S) and Crossing (S->Sᶜ).
  have h_split : ∑ u ∈ C.S, ∑ v, fl.f u v =
                 (∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v) +
                 (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f u v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl C.S (fl.f u)).symm

  -- Internal flow cancels out to 0 due to skew symmetry.
  have h_internal_zero : ∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v = 0 := by
    let vol := ∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v
    -- Use a calc block to avoid 'rw' modifying both sides of vol = -vol
    have h_vol_neg : vol = - vol := calc
      vol = ∑ v ∈ C.S, ∑ u ∈ C.S, fl.f u v := Finset.sum_comm
      _   = ∑ v ∈ C.S, ∑ u ∈ C.S, - fl.f v u := by
              apply Finset.sum_congr rfl
              intro v _
              apply Finset.sum_congr rfl
              intro u _
              exact fl.skew u v
      _   = - ∑ v ∈ C.S, ∑ u ∈ C.S, fl.f v u := by simp only [Finset.sum_neg_distrib]
      _   = - vol := rfl -- Alpha-equivalence handles the variable renaming (v <-> u)
    linarith

  -- Final calculation
  rw [h_val_eq_div_S, h_split, h_internal_zero, zero_add]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact fl.capacity_le u v

/-! ### 3. Residual Graph & Soundness -/

/-- Residual capacity: The remaining capacity + flow that can be pushed back. -/
def residualCapacity (fl : Flow N) (u v : V) : ℚ :=
  N.capacity u v - fl.f u v

/-- The Residual Graph contains edges where residual capacity is positive. -/
def isResidualEdge (fl : Flow N) (u v : V) : Prop :=
  residualCapacity fl u v > 0

/-- Helper for augmentation logic -/
-- A path is valid if it starts at source, ends at sink, and every edge has positive residual capacity.
def isValidAugmentingPath (fl : Flow N) (path : List V) : Prop :=
  path.head? = some N.source ∧
  path.getLast? = some N.sink ∧
  path.IsChain (isResidualEdge fl)


/-- **Soundness**: Augmenting flow along a valid path preserves flow properties. -/
-- Todo, instead of axioms
def augmentFlow (fl : Flow N) (path : List V) (amount : ℚ) : Flow N :=
  sorry


def pathContainsEdge (p : List V) (u v : V) : Bool :=
      match p with
      | [] => false
      | [_] => false
      | x :: y :: rest => (x == u && y == v) || pathContainsEdge (y :: rest) u v

/-- For any valid augmenting path, there exists a positive bottleneck capacity. -/
axiom exists_bottleneck :
  ∀ (fl : Flow N) (path : List V),
    isValidAugmentingPath fl path →
    ∃ amount > 0, ∀ u v, pathContainsEdge path u v → amount ≤ residualCapacity fl u v

/-- Augmenting along a path with amount ≤ bottleneck increases flow value by amount. -/
axiom augmentFlow_increases_value :
  ∀ (fl : Flow N) (path : List V) (amount : ℚ),
    isValidAugmentingPath fl path →
    (∀ u v, pathContainsEdge path u v → amount ≤ residualCapacity fl u v) →
    0 < amount →
    (augmentFlow fl path amount).flowValue = fl.flowValue + amount

/-! ### 4. Optimality & Strong Duality -/

/-- **Optimality Condition**:
    A flow is maximum iff no augmenting path exists in the residual graph. -/
def hasAugmentingPath (fl : Flow N) : Prop :=
  ∃ path, isValidAugmentingPath fl path -- Simplify definition as needed

/-- A vertex v is reachable if there is a valid chain of residual edges starting at source. -/
def reachable (fl : Flow N) : Set V :=
  { v | ∃ (path : List V), path.head? = some N.source ∧
    path.getLast? = some v ∧
    path.IsChain (isResidualEdge fl) }

omit [DecidableEq V] in
/-- Helper lemma: If u is reachable and (u,v) is a residual edge, then v is reachable. -/
lemma reachable_extend {fl : Flow N} {u v : V}
  (h_reachable : u ∈ reachable fl) (h_edge : isResidualEdge fl u v) : v ∈ reachable fl := by
  obtain ⟨path, h_head, h_last, h_chain⟩ := h_reachable
  use path ++ [v]
  constructor
  · -- Head remains source
    cases path
    · -- path is empty (impossible since head is source)
      simp at h_head
    · -- path is not empty
      exact Option.mem_def.mp h_head
  · constructor
    · -- Last becomes v
      simp
    · -- Chain is preserved
      rw [List.isChain_append]
      aesop

theorem optimality_condition (fl : Flow N) :
  (¬ hasAugmentingPath fl) ↔ ∀ fl' : Flow N, fl'.flowValue ≤ fl.flowValue := by
  sorry

/-- **Max-Flow Min-Cut Theorem (Strong Duality)**:
    There exists a flow f and a cut C such that their values are equal.
    (This implies f is max and C is min). -/
theorem max_flow_min_cut :
  ∃ fl : Flow N, ∃ C : Cut N, fl.flowValue = cutCapacity C := by
  sorry

end FlowNetwork
