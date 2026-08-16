import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Order.RelClasses

/-!
# Executable finite directed acyclic graphs

The first causal layer uses `Fin n` as its node type and stores a topological
certificate directly: every declared parent has a smaller index than its
child.  Thus the canonical order `0, ..., n - 1` is an executable topological
order, and well-founded recursion never needs to choose an ordering.

This representation covers every finite DAG after choosing a topological
numbering.  It deliberately keeps that numbering visible because later joint
distribution construction is computational.
-/

set_option autoImplicit false

namespace Ript.Models.Causal

/-- A finite DAG whose node indices are a certified topological order. -/
structure FiniteDAG (n : Nat) where
  /-- The finite set of direct parents of each node. -/
  parents : Fin n → Finset (Fin n)
  /-- Every edge points forward in the stored topological order. -/
  parent_before : ∀ child parent, parent ∈ parents child → parent.val < child.val

namespace FiniteDAG

variable {n : Nat} (graph : FiniteDAG n)

/-- The executable canonical topological ordering carried by the node
numbering. -/
def topologicalOrder (_ : FiniteDAG n) : List (Fin n) :=
  List.ofFn fun node ↦ node

/-- Every graph node occurs in the canonical topological order. -/
@[simp]
theorem mem_topologicalOrder (node : Fin n) :
    node ∈ graph.topologicalOrder := by
  simp [topologicalOrder]

/-- The directed parent relation of a finite DAG. -/
def Parent (parent child : Fin n) : Prop :=
  parent ∈ graph.parents child

/-- Every parent precedes its child in the certified topological order. -/
theorem parent_lt {parent child : Fin n} (h : graph.Parent parent child) :
    parent.val < child.val :=
  graph.parent_before child parent h

/-- The parent relation is well-founded, so recursive evaluation may follow
parents without introducing classical choice. -/
theorem parent_wellFounded : WellFounded graph.Parent :=
  Subrelation.wf (fun h ↦ graph.parent_lt h) wellFounded_lt

/-- A nonempty directed parent path strictly increases node indices. -/
theorem parentPath_lt {parent child : Fin n}
    (path : Relation.TransGen graph.Parent parent child) :
    parent.val < child.val := by
  induction path with
  | single h => exact graph.parent_lt h
  | tail path edge ih => exact Nat.lt_trans ih (graph.parent_lt edge)

/-- The certified parent graph has no directed cycles. -/
theorem acyclic (node : Fin n) :
    ¬ Relation.TransGen graph.Parent node node := by
  intro cycle
  exact Nat.lt_irrefl node.val (graph.parentPath_lt cycle)

/-- Values supplied to a local mechanism, indexed only by its declared
parents. -/
abbrev ParentAssignment (Value : Type*) (node : Fin n) : Type _ :=
  (parent : {parent // parent ∈ graph.parents node}) → Value

end FiniteDAG

end Ript.Models.Causal
