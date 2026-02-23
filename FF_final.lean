import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-
# Max-Flow Min-Cut Theorem Formalization Project
Team: Sarthak Parikh, Rasmus Valeth
-/

open Finset BigOperators Classical
set_option linter.unusedSectionVars false

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

/-- Helper: The value of a flow is exactly the sum of flow crossing any cut. -/
lemma flow_value_eq_crossing (fl : Flow N) (C : Cut N) :
    fl.flowValue = ∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f u v := by
  have h_node_cons : ∀ u, u ∈ C.S → u ≠ N.source → ∑ v, fl.f u v = 0 := by
    intro u h_in_S h_neq_src
    have h_neq_sink : u ≠ N.sink := fun h => C.sink_not_in (h ▸ h_in_S)
    trans ∑ v, - fl.f v u
    · apply Finset.sum_congr rfl
      intro v _
      rw [fl.skew]
    rw [Finset.sum_neg_distrib]
    rw [fl.conservation u h_neq_src h_neq_sink]
    exact neg_zero

  have h_val_eq_sum_S : fl.flowValue = ∑ u ∈ C.S, ∑ v, fl.f u v := by
    rw [← Finset.sum_erase_add _ _ C.source_in]
    rw [show (∑ v, fl.f N.source v) = fl.flowValue from rfl]
    have : ∑ u ∈ C.S.erase N.source, ∑ v, fl.f u v = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.mem_erase] at hu
      exact h_node_cons u hu.2 hu.1
    rw [this, zero_add]

  rw [h_val_eq_sum_S]
  trans ∑ u ∈ C.S, (∑ v ∈ C.S, fl.f u v + ∑ v ∈ C.Sᶜ, fl.f u v)
  · apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl C.S _).symm
  rw [Finset.sum_add_distrib]

  have h_internal : ∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v = 0 := by
    let vol := ∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v
    have h_vol_neg : vol = - vol := calc
      vol = ∑ v ∈ C.S, ∑ u ∈ C.S, fl.f u v := Finset.sum_comm
      _   = ∑ v ∈ C.S, ∑ u ∈ C.S, - fl.f v u := by
              apply Finset.sum_congr rfl
              intro v _
              apply Finset.sum_congr rfl
              intro u _
              exact fl.skew u v
      _   = - ∑ v ∈ C.S, ∑ u ∈ C.S, fl.f v u := by simp only [Finset.sum_neg_distrib]
      _   = - vol := rfl
    linarith

  rw [h_internal, zero_add]

/-- **Weak Duality**: The value of any flow is ≤ capacity of any cut. -/
theorem weak_duality (fl : Flow N) (C : Cut N) : fl.flowValue ≤ cutCapacity C := by
  have h_out_zero : ∀ u, u ≠ N.source → u ≠ N.sink → ∑ v, fl.f u v = 0 := by
    intro u h_src h_sink
    have h_neg : ∑ v, fl.f u v = ∑ v, - fl.f v u := by
      apply Finset.sum_congr rfl
      intro v _
      rw [fl.skew]
    rw [h_neg, Finset.sum_neg_distrib, fl.conservation u h_src h_sink, neg_zero]

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

  have h_split : ∑ u ∈ C.S, ∑ v, fl.f u v =
                 (∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v) +
                 (∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, fl.f u v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.sum_add_sum_compl C.S (fl.f u)).symm

  have h_internal_zero : ∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v = 0 := by
    let vol := ∑ u ∈ C.S, ∑ v ∈ C.S, fl.f u v
    have h_vol_neg : vol = - vol := calc
      vol = ∑ v ∈ C.S, ∑ u ∈ C.S, fl.f u v := Finset.sum_comm
      _   = ∑ v ∈ C.S, ∑ u ∈ C.S, - fl.f v u := by
              apply Finset.sum_congr rfl
              intro v _
              apply Finset.sum_congr rfl
              intro u _
              exact fl.skew u v
      _   = - ∑ v ∈ C.S, ∑ u ∈ C.S, fl.f v u := by simp only [Finset.sum_neg_distrib]
      _   = - vol := rfl
    linarith

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

section Reachability

/-- Inductive definition of reachability in the residual graph -/
inductive ResidualReachable (fl : Flow N) : V → Prop
  | source : ResidualReachable fl N.source
  | step {u v} : ResidualReachable fl u → isResidualEdge fl u v → ResidualReachable fl v

/-- If u is reachable and v is NOT, then residual capacity u->v must be 0. -/
lemma residual_zero_of_boundary (fl : Flow N) {u v : V}
    (hu : ResidualReachable fl u) (hv : ¬ ResidualReachable fl v) :
    residualCapacity fl u v = 0 := by
  by_contra h_neq_zero
  have h_nonneg : 0 ≤ residualCapacity fl u v := by
    dsimp [residualCapacity]
    linarith [fl.capacity_le u v]
  have h_pos : 0 < residualCapacity fl u v :=
    lt_of_le_of_ne h_nonneg (Ne.symm h_neq_zero)
  have h_edge : isResidualEdge fl u v := h_pos
  have v_reachable : ResidualReachable fl v := ResidualReachable.step hu h_edge
  contradiction

/-- The canonical cut constructed from the residual graph.
    This is only a valid 'Cut' if the sink is NOT reachable. -/
noncomputable def residualCut (fl : Flow N) (h_unreachable : ¬ ResidualReachable fl N.sink) : Cut N where
  S := {v | ResidualReachable fl v}.toFinset
  source_in := by
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    exact ResidualReachable.source
  sink_not_in := by
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    exact h_unreachable

/-- **Key Lemma**: If the sink is not reachable, Flow equals Cut Capacity. -/
theorem flow_eq_cut_if_not_reachable (fl : Flow N)
    (h_unreachable : ¬ ResidualReachable fl N.sink) :
    fl.flowValue = cutCapacity (residualCut fl h_unreachable) := by
  let C := residualCut fl h_unreachable
  rw [flow_value_eq_crossing fl C, cutCapacity]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv

  change u ∈ (residualCut fl h_unreachable).S at hu
  simp only [residualCut, Set.mem_toFinset, Set.mem_setOf_eq] at hu
  have u_reach : ResidualReachable fl u := hu

  rw [Finset.mem_compl] at hv
  change v ∉ (residualCut fl h_unreachable).S at hv
  simp only [residualCut, Set.mem_toFinset, Set.mem_setOf_eq] at hv
  have v_not_reach : ¬ ResidualReachable fl v := hv

  have h_res_zero := residual_zero_of_boundary fl u_reach v_not_reach
  dsimp [residualCapacity] at h_res_zero
  linarith

end Reachability

/-- A path is valid if every step is a residual edge. -/
def isValidAugmentingPath (fl : Flow N) (path : List V) : Prop :=
  path.IsChain (isResidualEdge fl) ∧
  path.head? = some N.source ∧
  path.getLast? = some N.sink

/-- Bridge: Convert the inductive Reachability definition to a concrete List Path. -/
theorem exists_path_of_reachable (fl : Flow N) {w : V} (h : ResidualReachable fl w) :
    ∃ path : List V, List.IsChain (isResidualEdge fl) path ∧ List.head? path = some N.source ∧ List.getLast? path = some w := by
  induction h with
  | source =>
    use [N.source]
    simp
  | step h_u_reach h_edge ih =>
    rename_i u v
    rcases ih with ⟨p, h_chain, h_head, h_last⟩
    use p ++ [v]
    constructor
    · rw [List.isChain_append]
      constructor
      · exact h_chain
      · constructor
        · simp only [List.IsChain.singleton]
        · intro x hx y hy
          rw [h_last] at hx
          simp only [Option.mem_some_iff] at hx
          simp only [List.head?_singleton, Option.mem_some_iff] at hy
          rw [← hx, ← hy]
          exact h_edge
    · constructor
      · cases p with
        | nil =>
          simp only [List.head?_nil] at h_head
          contradiction
        | cons a as =>
          simp at h_head
          simp
          exact h_head
      · simp

/-- Helper to check if an edge (u,v) is in the path. -/
def edgeInPath (path : List V) (u v : V) : Bool :=
  (path.zip path.tail).any (fun (a, b) => a = u ∧ b = v)

/-- Calculate the bottleneck capacity of a path. -/
def pathBottleneck (fl : Flow N) (path : List V) : ℚ :=
  let edges := path.zip path.tail
  let residuals := edges.map (fun x => residualCapacity fl x.1 x.2)
  residuals.min?.getD 0

/-- Lemma: If a path is valid, the bottleneck is positive. -/
lemma bottleneck_pos_of_valid (fl : Flow N) (path : List V)
  (h_path : isValidAugmentingPath fl path) :
  pathBottleneck fl path > 0 := by
  sorry

/-- Lemma: The bottleneck is ≤ the residual capacity of any edge in the path. -/
lemma bottleneck_le_residual (fl : Flow N) (path : List V) (u v : V)
    (h_edge : edgeInPath path u v = true) :
    pathBottleneck fl path ≤ residualCapacity fl u v := by
  sorry

/-- Topological Law 1: For any intermediate node in a valid path, In-Degree = Out-Degree. -/
lemma path_conservation_lemma (fl : Flow N) (path : List V) (v : V)
    (h_valid : isValidAugmentingPath fl path)
    (h_src : v ≠ N.source) (h_sink : v ≠ N.sink) :
    ∑ u, (if edgeInPath path u v then (1 : ℚ) else 0) =
    ∑ u, (if edgeInPath path v u then (1 : ℚ) else 0) := by
  sorry

/-- Topological Law 2: The path leaves the source exactly 1 more time than it enters it. -/
lemma path_source_lemma (fl : Flow N) (path : List V)
    (h_valid : isValidAugmentingPath fl path) :
    (∑ v, (if edgeInPath path N.source v then (1 : ℚ) else 0)) -
    (∑ u, (if edgeInPath path u N.source then (1 : ℚ) else 0)) = 1 := by
  sorry

/-- Augment flow along a path, updating forward and backward edges. -/
def augmentFlow (fl : Flow N) (path : List V) (amount : ℚ)
    (h_valid : isValidAugmentingPath fl path)
    (h_amount : ∀ u v, edgeInPath path u v = true → amount ≤ residualCapacity fl u v)
    (h_pos : 0 ≤ amount) : Flow N :=
  let new_f (u v : V) : ℚ :=
    fl.f u v + (if edgeInPath path u v then amount else 0)
             - (if edgeInPath path v u then amount else 0)
  { f := new_f
    capacity_le := by
      intro u v
      dsimp [new_f]
      have h_cap := fl.capacity_le u v
      split_ifs
      · linarith
      · have h_res := h_amount u v (by assumption)
        dsimp [residualCapacity] at h_res
        linarith
      · linarith
      · linarith

    skew := by
      intro u v
      dsimp [new_f]
      have h_skew := fl.skew u v
      split_ifs <;> linarith

    conservation := by
      intro v h_src h_sink
      dsimp [new_f]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [fl.conservation v h_src h_sink]

      have h_in : ∑ u, (if edgeInPath path u v then amount else 0) = amount * ∑ u, (if edgeInPath path u v then (1:ℚ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        split_ifs
        · ring
        · ring

      have h_out : ∑ u, (if edgeInPath path v u then amount else 0) = amount * ∑ u, (if edgeInPath path v u then (1:ℚ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        split_ifs
        · ring
        · ring

      rw [h_in, h_out]
      rw [path_conservation_lemma fl path v h_valid h_src h_sink]
      ring
  }

/-- Lemma: Pushing flow along a valid path strictly increases the flow value. -/
lemma augment_increases_flow (fl : Flow N) (path : List V) (amount : ℚ)
    (h_path : isValidAugmentingPath fl path)
    (h_amount : ∀ u v, edgeInPath path u v = true → amount ≤ residualCapacity fl u v)
    (h_pos : amount > 0) :
    (augmentFlow fl path amount h_path h_amount (le_of_lt h_pos)).flowValue > fl.flowValue := by
  dsimp [Flow.flowValue, augmentFlow]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

  have h_out : ∑ v, (if edgeInPath path N.source v then amount else 0) = amount * ∑ v, (if edgeInPath path N.source v then (1:ℚ) else 0) := by
    have : ∀ v, (if edgeInPath path N.source v then amount else 0) = amount * (if edgeInPath path N.source v then (1:ℚ) else 0) := by
      intro v; split_ifs <;> ring
    simp_rw [this]
    rw [← Finset.mul_sum]

  have h_in : ∑ u, (if edgeInPath path u N.source then amount else 0) = amount * ∑ u, (if edgeInPath path u N.source then (1:ℚ) else 0) := by
    have : ∀ u, (if edgeInPath path u N.source then amount else 0) = amount * (if edgeInPath path u N.source then (1:ℚ) else 0) := by
      intro u; split_ifs <;> ring
    simp_rw [this]
    rw [← Finset.mul_sum]

  rw [h_out, h_in]

  have h_alg : (∑ v, fl.f N.source v) + amount * ∑ v, (if edgeInPath path N.source v then (1:ℚ) else 0) - amount * ∑ u, (if edgeInPath path u N.source then (1:ℚ) else 0) =
               (∑ v, fl.f N.source v) + amount * ((∑ v, (if edgeInPath path N.source v then (1:ℚ) else 0)) - ∑ u, (if edgeInPath path u N.source then (1:ℚ) else 0)) := by ring

  rw [h_alg]
  rw [path_source_lemma fl path h_path]

  have h_final : (∑ v, fl.f N.source v) + amount * 1 = fl.flowValue + amount := by
    dsimp [Flow.flowValue]
    ring

  rw [h_final]
  linarith

/-! ### 4. Optimality & Strong Duality -/

/-- **Optimality Condition**:
    A flow is maximum iff no augmenting path exists in the residual graph. -/
def hasAugmentingPath (fl : Flow N) : Prop :=
  ∃ path, isValidAugmentingPath fl path

/-- **Optimality Condition**: Max Flow iff No Augmenting Path. -/
theorem optimality_condition (fl : Flow N) :
  (¬ hasAugmentingPath fl) ↔ ∀ fl' : Flow N, fl'.flowValue ≤ fl.flowValue := by
  constructor
  · intro h_no_path fl'
    have h_unreachable : ¬ ResidualReachable fl N.sink := by
      intro h_reach
      rcases exists_path_of_reachable fl h_reach with ⟨p, hp⟩
      exact h_no_path ⟨p, hp⟩
    rw [flow_eq_cut_if_not_reachable fl h_unreachable]
    apply weak_duality

  · intro h_max h_exists
    rcases h_exists with ⟨path, h_valid⟩

    let ε := pathBottleneck fl path
    have h_pos : ε > 0 := bottleneck_pos_of_valid fl path h_valid
    have h_amount : ∀ u v, edgeInPath path u v = true → ε ≤ residualCapacity fl u v := by
      intro u v h_edge
      exact bottleneck_le_residual fl path u v h_edge

    let fl_new : Flow N := augmentFlow fl path ε h_valid h_amount (le_of_lt h_pos)
    have h_better := augment_increases_flow fl path ε h_valid h_amount h_pos

    specialize h_max fl_new
    linarith

/-- **Max-Flow Min-Cut Theorem (Strong Duality)**:
    If a flow admits no augmenting path, there is a cut with equal capacity.-/
theorem max_flow_min_cut (fl : Flow N) (h_opt : ¬ hasAugmentingPath fl) :
  ∃ C : Cut N, fl.flowValue = cutCapacity C := by
  have h_unreachable : ¬ ResidualReachable fl N.sink := by
    intro h_reach
    rcases exists_path_of_reachable fl h_reach with ⟨p, hp⟩
    exact h_opt ⟨p, hp⟩

  use residualCut fl h_unreachable
  exact flow_eq_cut_if_not_reachable fl h_unreachable

end FlowNetwork
