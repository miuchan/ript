import Mathlib.CategoryTheory.Products.Basic
import Ript.Models.Computation.Total

/-!
# Partial computations as a costed `Option` Kleisli model

A morphism executes to `Option`: `none` represents failure and `some y`
represents successful termination.  Kleisli composition propagates failure and
adds the declared multidimensional resources.  Parallel composition succeeds
exactly when both components succeed.  A faithful-on-runtime embedding sends
every total computation to an always-successful partial computation while
preserving its formal resource vector.
-/

set_option autoImplicit false

namespace Ript.Models.Computation.Partial

open CategoryTheory
open Ript.Core
open Ript.Models.Computation
open Ript.Resource

universe u

/-- An object in the partial-computation process category. -/
structure Object where
  /-- The type of values carried by the object. -/
  carrier : Type u

namespace Object

instance : CoeSort Object (Type u) :=
  ⟨Object.carrier⟩

/-- Bundle a value type as a partial-computation object. -/
def of (X : Type u) : Object :=
  ⟨X⟩

/-- Unit object for independent partial computation. -/
def unit : Object :=
  of PUnit

/-- Cartesian interface for independent partial computation. -/
def tensor (X Y : Object) : Object :=
  of (X × Y)

end Object

/-- A possibly failing executable function with a formal resource cost. -/
@[ext]
structure Hom (X Y : Object) where
  /-- Execute the computation, returning `none` on failure. -/
  run : X → Option Y
  /-- Declared abstract computation resources. -/
  resource : ComputationResource

variable {W X Y Z : Object.{u}}

/-- Costed partial computations form the Kleisli category of `Option`. -/
instance category : Category.{u} Object where
  Hom := Hom
  id X := ⟨some, 0⟩
  comp f g := ⟨fun x ↦ (f.run x).bind g.run, f.resource + g.resource⟩
  id_comp := by
    intro X Y f
    apply Hom.ext
    · rfl
    · simp
  comp_id := by
    intro X Y f
    apply Hom.ext
    · funext x
      change (f.run x).bind some = f.run x
      cases f.run x <;> rfl
    · simp
  assoc := by
    intro V W X Y f g h
    apply Hom.ext
    · funext v
      change ((f.run v).bind g.run).bind h.run =
        (f.run v).bind (fun w ↦ (g.run w).bind h.run)
      cases f.run v <;> rfl
    · simp [add_assoc]

/-- Construct a costed partial computation. -/
def mk (run : X → Option Y) (resource : ComputationResource) : X ⟶ Y :=
  ⟨run, resource⟩

/-- Execute a partial computation on an input. -/
def apply (f : X ⟶ Y) (x : X) : Option Y :=
  f.run x

/-- Process cost is exactly the vector stored in a partial morphism. -/
instance processCost : HasProcessCost Object ComputationResource where
  cost f := f.resource
  cost_id _ := rfl
  cost_comp _ _ := le_rfl

/-- Executing a composite is `Option` Kleisli composition. -/
@[simp]
theorem run_comp (f : W ⟶ X) (g : X ⟶ Y) (w : W) :
    (f ≫ g).run w = (f.run w).bind g.run :=
  rfl

/-- Serial partial composition adds every resource coordinate exactly. -/
@[simp]
theorem resource_comp (f : W ⟶ X) (g : X ⟶ Y) :
    (f ≫ g).resource = f.resource + g.resource :=
  rfl

/-- Failure of the first computation prevents the second from running. -/
theorem run_comp_none (f : W ⟶ X) (g : X ⟶ Y) (w : W)
    (h : f.run w = none) : (f ≫ g).run w = none := by
  simp [run_comp, h]

/-- Combine two partial results, succeeding exactly when both are present. -/
def pairOptions {A B : Type u} (left : Option A) (right : Option B) :
    Option (A × B) :=
  left.bind fun a ↦ right.map fun b ↦ (a, b)

/-- Run two partial computations independently on a product input. -/
def tensor (f : W ⟶ X) (g : Y ⟶ Z) :
    Object.tensor W Y ⟶ Object.tensor X Z :=
  ⟨fun input ↦ pairOptions (f.run input.1) (g.run input.2),
    f.resource + g.resource⟩

/-- Parallel partial execution combines the two optional results. -/
@[simp]
theorem tensor_run (f : W ⟶ X) (g : Y ⟶ Z) (input : W × Y) :
    (tensor f g).run input = pairOptions (f.run input.1) (g.run input.2) :=
  rfl

/-- Parallel partial composition adds every resource coordinate exactly. -/
@[simp]
theorem tensor_resource (f : W ⟶ X) (g : Y ⟶ Z) :
    (tensor f g).resource = f.resource + g.resource :=
  rfl

/-- Parallel composition preserves partial identity computations. -/
theorem tensor_id (X Y : Object.{u}) :
    tensor (𝟙 X) (𝟙 Y) = 𝟙 (Object.tensor X Y) := by
  apply Hom.ext
  · rfl
  · change (0 : ComputationResource) + 0 = 0
    simp

/-- Parallel and Kleisli composition satisfy the interchange law. -/
theorem tensor_comp {A B C D E F : Object.{u}}
    (f : A ⟶ B) (f' : B ⟶ C) (g : D ⟶ E) (g' : E ⟶ F) :
    tensor (f ≫ f') (g ≫ g') = tensor f g ≫ tensor f' g' := by
  apply Hom.ext
  · funext input
    rcases input with ⟨a, d⟩
    change pairOptions ((f.run a).bind f'.run) ((g.run d).bind g'.run) =
      (pairOptions (f.run a) (g.run d)).bind
        (fun middle ↦ pairOptions (f'.run middle.1) (g'.run middle.2))
    cases f.run a with
    | none => simp [pairOptions]
    | some b =>
        cases g.run d with
        | none => simp [pairOptions]
        | some e =>
            cases f'.run b <;>
              cases g'.run e <;>
              simp [pairOptions]
  · simp [add_comm, add_left_comm]

/-- Independent parallel execution is a bifunctor on partial computations. -/
def tensorFunctor : Object.{u} × Object.{u} ⥤ Object.{u} where
  obj pair := Object.tensor pair.1 pair.2
  map pair := tensor pair.1 pair.2
  map_id pair := tensor_id pair.1 pair.2
  map_comp f g := tensor_comp f.1 g.1 f.2 g.2

/-- Executable componentwise budget check for a partial computation. -/
def withinBudget (budget : ComputationResource) (f : X ⟶ Y) : Bool :=
  ComputationResource.within f.resource budget

/-- A successful executable check yields the generic proof-level budget
judgment for the partial-computation category. -/
theorem withinBudget_sound {budget : ComputationResource} {f : X ⟶ Y}
    (h : withinBudget budget f = true) : WithinBudget budget f :=
  ComputationResource.within_sound h

/-- Send a total-computation object to the same carrier in the partial model. -/
def ofTotalObject (X : Total.Object.{u}) : Object.{u} :=
  Object.of X

/-- Every total computation is an always-successful partial computation with
the same formal resource vector. -/
def ofTotalHom {X Y : Total.Object.{u}} (f : X ⟶ Y) :
    ofTotalObject X ⟶ ofTotalObject Y :=
  ⟨fun x ↦ some (f.run x), f.resource⟩

/-- The always-successful embedding is a functor from total to partial
computations. -/
def ofTotal : Total.Object.{u} ⥤ Object.{u} where
  obj := ofTotalObject
  map := ofTotalHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The total-to-partial embedding preserves execution results exactly. -/
@[simp]
theorem ofTotal_run {X Y : Total.Object.{u}} (f : X ⟶ Y) (x : X) :
    (ofTotal.map f).run x = some (f.run x) :=
  rfl

/-- The total-to-partial embedding preserves all formal resource coordinates. -/
@[simp]
theorem ofTotal_resource {X Y : Total.Object.{u}} (f : X ⟶ Y) :
    (ofTotal.map f).resource = f.resource :=
  rfl

end Ript.Models.Computation.Partial
