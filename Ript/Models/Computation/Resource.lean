import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Ript.Resource.Basic

/-!
# Multidimensional resources for computation

Formal computation costs are kept separate from wall-clock time.  A resource
vector records abstract step, oracle-query, storage, and circuit-gate bounds.
All order and addition operations are pointwise, so sequential and parallel
composition can account for every component with the same generic resource
interfaces used by the rest of Ript.
-/

set_option autoImplicit false

namespace Ript.Models.Computation

/-- The four coordinates of the first computation resource model. -/
abbrev ResourceKind := Fin 4

namespace ResourceKind

/-- Coordinate zero records formal evaluation steps. -/
def steps : ResourceKind := 0

/-- Coordinate one records formal oracle queries. -/
def queries : ResourceKind := 1

/-- Coordinate two records a declared storage bound. -/
def storage : ResourceKind := 2

/-- Coordinate three records formal circuit gates. -/
def gates : ResourceKind := 3

end ResourceKind

/-- A pointwise ordered vector of formal computation resources.  These values
do not claim to measure physical runtime. -/
abbrev ComputationResource := ResourceKind → Nat

/-- Construct a computation-resource vector from its four named components. -/
def ComputationResource.of (steps queries storage gates : Nat) :
    ComputationResource :=
  ![steps, queries, storage, gates]

/-- The formal step-count coordinate. -/
def ComputationResource.steps (resource : ComputationResource) : Nat :=
  resource ResourceKind.steps

/-- The formal oracle-query coordinate. -/
def ComputationResource.queries (resource : ComputationResource) : Nat :=
  resource ResourceKind.queries

/-- The formal storage-bound coordinate. -/
def ComputationResource.storage (resource : ComputationResource) : Nat :=
  resource ResourceKind.storage

/-- The formal circuit-gate coordinate. -/
def ComputationResource.gates (resource : ComputationResource) : Nat :=
  resource ResourceKind.gates

/-- Project a multidimensional computation resource to its formal step count.
This is an ordered additive homomorphism, so it can reindex every generic Ript
cost and budget law from `ComputationResource` to the single-valued resource
algebra `Nat`. -/
def ComputationResource.stepsHom : ComputationResource →+o Nat where
  toFun := ComputationResource.steps
  map_zero' := rfl
  map_add' _ _ := rfl
  monotone' _ _ h := h ResourceKind.steps

@[simp]
theorem ComputationResource.stepsHom_apply (resource : ComputationResource) :
    ComputationResource.stepsHom resource = resource.steps :=
  rfl

@[simp]
theorem ComputationResource.stepsHom_of (steps queries storage gates : Nat) :
    ComputationResource.stepsHom
      (ComputationResource.of steps queries storage gates) = steps :=
  rfl

/-- Computation resources form the ordered additive resource algebra required
by the generic budget layer. -/
example : Ript.Resource.ResourceAlgebra ComputationResource := by
  infer_instance

/-- Componentwise comparison is decidable and therefore supports executable
budget checks. -/
def ComputationResource.within (cost budget : ComputationResource) : Bool :=
  decide (∀ kind : ResourceKind, cost kind ≤ budget kind)

/-- The Boolean budget check returns true exactly for a componentwise bound. -/
theorem ComputationResource.within_eq_true_iff
    (cost budget : ComputationResource) :
    ComputationResource.within cost budget = true ↔ cost ≤ budget := by
  change ComputationResource.within cost budget = true ↔
    ∀ kind, cost kind ≤ budget kind
  simp [ComputationResource.within]

/-- A true executable budget check yields a proof-level resource bound. -/
theorem ComputationResource.within_sound {cost budget : ComputationResource}
    (h : ComputationResource.within cost budget = true) : cost ≤ budget :=
  (ComputationResource.within_eq_true_iff cost budget).mp h

/-- Named construction exposes the step coordinate definitionally. -/
@[simp]
theorem ComputationResource.of_steps (steps queries storage gates : Nat) :
    (ComputationResource.of steps queries storage gates).steps = steps :=
  rfl

/-- Named construction exposes the query coordinate definitionally. -/
@[simp]
theorem ComputationResource.of_queries (steps queries storage gates : Nat) :
    (ComputationResource.of steps queries storage gates).queries = queries :=
  rfl

/-- Named construction exposes the storage coordinate definitionally. -/
@[simp]
theorem ComputationResource.of_storage (steps queries storage gates : Nat) :
    (ComputationResource.of steps queries storage gates).storage = storage :=
  rfl

/-- Named construction exposes the gate coordinate definitionally. -/
@[simp]
theorem ComputationResource.of_gates (steps queries storage gates : Nat) :
    (ComputationResource.of steps queries storage gates).gates = gates :=
  rfl

end Ript.Models.Computation
