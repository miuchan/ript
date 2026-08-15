import Mathlib.Algebra.BigOperators.Fin
import Ript.Models.Causal.DAG
import Ript.Models.FiniteDistribution

/-!
# Finite causal mechanisms and observational joint distributions

A `FiniteCausalModel n Value` combines a topologically numbered finite DAG
with one exact conditional distribution per node.  A local mechanism receives
only the values of the parents declared by the DAG.

The observational joint mass is the product of those local conditionals.  Its
normalization is proved by induction over the certified topological order, so
the resulting `FinDist` is executable and contains no normalization axiom.
-/

set_option autoImplicit false

namespace Ript.Models.Causal

open scoped BigOperators

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

/-- An exact conditional mechanism for one node of a finite DAG. -/
structure Mechanism {n : Nat} (graph : FiniteDAG n) (Value : Type u)
    [Fintype Value] [DecidableEq Value] (node : Fin n) where
  /-- Evaluate the node distribution from the values of exactly its declared
  parents. -/
  run : graph.ParentAssignment Value node → FinDist (Object.of Value)

/-- A finite structural causal model with a common finite value carrier.

The homogeneous carrier is an explicit first-version restriction.  Nodes may
have different mechanisms and parent sets, while heterogeneous node carriers
remain a later generalization. -/
structure FiniteCausalModel (n : Nat) (Value : Type u)
    [Fintype Value] [DecidableEq Value] where
  /-- The causal graph and its executable topological certificate. -/
  dag : FiniteDAG n
  /-- One normalized conditional mechanism at every node. -/
  mechanism : (node : Fin n) → Mechanism dag Value node

/-- A complete assignment of a common finite value type to `n` nodes. -/
abbrev Assignment (n : Nat) (Value : Type u) : Type u :=
  Fin n → Value

/-- Complete assignments bundled as an executable finite stochastic object. -/
def assignmentObject (n : Nat) (Value : Type u)
    [Fintype Value] [DecidableEq Value] : Object :=
  Object.of (Assignment n Value)

namespace FiniteCausalModel

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- Restrict a prefix assignment to the declared parents of a prefix node. -/
def prefixParentAssignment (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k ≤ n) (assignment : Assignment k Value)
    (node : Fin k) :
    model.dag.ParentAssignment Value (Fin.castLE hkn node) :=
  fun parent ↦
    assignment ⟨parent.1.val, by
      have hParent : parent.1.val < node.val := by
        simpa only [Fin.val_castLE] using
          model.dag.parent_before (Fin.castLE hkn node) parent.1 parent.2
      exact Nat.lt_trans hParent node.isLt⟩

/-- The local factor contributed by a node inside an initial topological
prefix. -/
def prefixLocalMass (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k ≤ n) (assignment : Assignment k Value)
    (node : Fin k) : ℚ≥0 :=
  ((model.mechanism (Fin.castLE hkn node)).run
      (model.prefixParentAssignment hkn assignment node)).prob (assignment node)

/-- Product of all local conditional factors in an initial topological
prefix. -/
def prefixFactorMass (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k ≤ n) (assignment : Assignment k Value) : ℚ≥0 :=
  ∏ node, model.prefixLocalMass hkn assignment node

/-- Conditional distribution for the next node after a prefix assignment. -/
def nextDistribution (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k + 1 ≤ n) (assignment : Assignment k Value) :
    FinDist (Object.of Value) :=
  (model.mechanism (Fin.castLE hkn (Fin.last k))).run fun parent ↦
    assignment ⟨parent.1.val, by
      simpa only [Fin.val_castLE, Fin.val_last] using
        model.dag.parent_before
          (Fin.castLE hkn (Fin.last k)) parent.1 parent.2⟩

/-- Appending a value does not change an earlier node's local factor. -/
theorem prefixLocalMass_snoc_castSucc (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k + 1 ≤ n) (assignment : Assignment k Value)
    (value : Value) (node : Fin k) :
    model.prefixLocalMass hkn (Fin.snoc assignment value) node.castSucc =
      model.prefixLocalMass (Nat.le_trans (Nat.le_succ k) hkn) assignment node := by
  unfold prefixLocalMass prefixParentAssignment
  congr 2
  · funext parent
    convert @Fin.snoc_castSucc k (fun _ ↦ Value) value assignment
      ⟨parent.1.val, by
        have hParent : parent.1.val < node.val := by
          simpa only [Fin.val_castLE, Fin.val_castSucc] using
            model.dag.parent_before
              (Fin.castLE hkn node.castSucc) parent.1 parent.2
        exact Nat.lt_trans hParent node.isLt⟩ using 1
    congr 1
  · exact @Fin.snoc_castSucc k (fun _ ↦ Value) value assignment node

/-- The last local factor of an extended assignment is exactly the next-node
conditional probability. -/
theorem prefixLocalMass_snoc_last (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k + 1 ≤ n) (assignment : Assignment k Value)
    (value : Value) :
    model.prefixLocalMass hkn (Fin.snoc assignment value) (Fin.last k) =
      (model.nextDistribution hkn assignment).prob value := by
  unfold prefixLocalMass prefixParentAssignment nextDistribution
  congr 2
  · funext parent
    convert @Fin.snoc_castSucc k (fun _ ↦ Value) value assignment
      ⟨parent.1.val, by
        simpa only [Fin.val_castLE, Fin.val_last] using
          model.dag.parent_before
            (Fin.castLE hkn (Fin.last k)) parent.1 parent.2⟩ using 1
    congr 1
  · exact @Fin.snoc_last k (fun _ ↦ Value) value assignment

/-- Extending a topological prefix multiplies its factor mass by the next
conditional probability. -/
theorem prefixFactorMass_snoc (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k + 1 ≤ n) (assignment : Assignment k Value)
    (value : Value) :
    model.prefixFactorMass hkn (Fin.snoc assignment value) =
      model.prefixFactorMass (Nat.le_trans (Nat.le_succ k) hkn) assignment *
        (model.nextDistribution hkn assignment).prob value := by
  rw [prefixFactorMass, Fin.prod_univ_castSucc]
  congr 1
  · apply Fintype.prod_congr
    intro node
    exact model.prefixLocalMass_snoc_castSucc hkn assignment value node
  · exact model.prefixLocalMass_snoc_last hkn assignment value

/-- The next-node conditional distribution is normalized over the concrete
value carrier. -/
theorem nextDistribution_normalized (model : FiniteCausalModel n Value)
    {k : Nat} (hkn : k + 1 ≤ n) (assignment : Assignment k Value) :
    ∑ value : Value, (model.nextDistribution hkn assignment).prob value = 1 := by
  change ∑ value : (Object.of Value),
    (model.nextDistribution hkn assignment).prob value = 1
  exact (model.nextDistribution hkn assignment).normalized

/-- Local conditional normalization implies normalization of every initial
topological prefix. -/
theorem prefixFactorMass_normalized (model : FiniteCausalModel n Value) :
    ∀ {k : Nat} (hkn : k ≤ n),
      ∑ assignment : Assignment k Value,
        model.prefixFactorMass hkn assignment = 1 := by
  intro k
  induction k with
  | zero =>
      intro hkn
      simp [prefixFactorMass]
  | succ k ih =>
      intro hkn
      let prefixBound : k ≤ n := Nat.le_trans (Nat.le_succ k) hkn
      let splitAssignments := Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Value)
      calc
        ∑ assignment : Assignment (k + 1) Value,
              model.prefixFactorMass hkn assignment =
            ∑ pair : Value × Assignment k Value,
              model.prefixFactorMass hkn (splitAssignments pair) := by
                symm
                exact splitAssignments.sum_comp
                  (fun assignment ↦ model.prefixFactorMass hkn assignment)
        _ = ∑ value : Value, ∑ assignment : Assignment k Value,
              model.prefixFactorMass prefixBound assignment *
                (model.nextDistribution hkn assignment).prob value := by
              rw [Fintype.sum_prod_type]
              apply Fintype.sum_congr
              intro value
              apply Fintype.sum_congr
              intro assignment
              change model.prefixFactorMass hkn (Fin.snoc assignment value) = _
              simpa only [prefixBound] using
                model.prefixFactorMass_snoc hkn assignment value
        _ = ∑ assignment : Assignment k Value, ∑ value : Value,
              model.prefixFactorMass prefixBound assignment *
                (model.nextDistribution hkn assignment).prob value :=
              Finset.sum_comm
        _ = ∑ assignment : Assignment k Value,
              model.prefixFactorMass prefixBound assignment *
                (∑ value : Value,
                  (model.nextDistribution hkn assignment).prob value) := by
              apply Fintype.sum_congr
              intro assignment
              exact (Finset.mul_sum Finset.univ
                (fun value : Value ↦
                  (model.nextDistribution hkn assignment).prob value)
                (model.prefixFactorMass prefixBound assignment)).symm
        _ = ∑ assignment : Assignment k Value,
              model.prefixFactorMass prefixBound assignment := by
              apply Fintype.sum_congr
              intro assignment
              rw [model.nextDistribution_normalized hkn assignment]
              simp
        _ = 1 := ih prefixBound

/-- The exact observational joint distribution generated along the certified
topological order. -/
def joint (model : FiniteCausalModel n Value) :
    FinDist (assignmentObject n Value) where
  prob assignment := model.prefixFactorMass (Nat.le_refl n) assignment
  normalized := model.prefixFactorMass_normalized (Nat.le_refl n)

/-- The observational joint distribution factors into the product of the
declared local conditional mechanisms. -/
theorem observational_factorization (model : FiniteCausalModel n Value)
    (assignment : Assignment n Value) :
    model.joint.prob assignment =
      ∏ node,
        ((model.mechanism node).run
          (fun parent ↦ assignment parent.1)).prob (assignment node) := by
  rfl

end FiniteCausalModel

end Ript.Models.Causal
