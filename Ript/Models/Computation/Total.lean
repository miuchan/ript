import Mathlib.CategoryTheory.Products.Basic
import Ript.Models.Computation.Resource
import Ript.Resource.Budget

/-!
# Total computations with explicit multidimensional costs

Objects are arbitrary Lean types.  A morphism is a total executable function
paired with an abstract resource vector.  Composition executes functions in
sequence and adds their declared step, query, storage, and gate costs exactly.
Independent parallel execution is exposed as a bifunctor and also adds costs
exactly; no connection to wall-clock time is asserted.
-/

set_option autoImplicit false

namespace Ript.Models.Computation.Total

open CategoryTheory
open Ript.Core
open Ript.Models.Computation
open Ript.Resource

universe u

/-- An object in the total-computation process category. -/
structure Object where
  /-- The type of executable values carried by the object. -/
  carrier : Type u

namespace Object

instance : CoeSort Object (Type u) :=
  ⟨Object.carrier⟩

/-- Bundle an executable value type as a total-computation object. -/
def of (X : Type u) : Object :=
  ⟨X⟩

/-- Unit object for independent parallel computation. -/
def unit : Object :=
  of PUnit

/-- Cartesian interface for independent parallel computation. -/
def tensor (X Y : Object) : Object :=
  of (X × Y)

end Object

/-- A total executable function carrying an explicit formal resource cost. -/
@[ext]
structure Hom (X Y : Object) where
  /-- Execute the computation. -/
  run : X → Y
  /-- Declared abstract computation resources. -/
  resource : ComputationResource

variable {W X Y Z : Object.{u}}

/-- Total costed computations form a category with exact additive costs. -/
instance category : Category.{u} Object where
  Hom := Hom
  id X := ⟨id, 0⟩
  comp f g := ⟨fun x ↦ g.run (f.run x), f.resource + g.resource⟩
  id_comp := by
    intro X Y f
    apply Hom.ext
    · rfl
    · simp
  comp_id := by
    intro X Y f
    apply Hom.ext
    · rfl
    · simp
  assoc := by
    intro V W X Y f g h
    apply Hom.ext
    · rfl
    · simp [add_assoc]

/-- Construct a costed total computation. -/
def mk (run : X → Y) (resource : ComputationResource) : X ⟶ Y :=
  ⟨run, resource⟩

/-- Execute a total computation on an input. -/
def apply (f : X ⟶ Y) (x : X) : Y :=
  f.run x

/-- Process cost is exactly the resource vector stored in a total morphism. -/
instance processCost : HasProcessCost Object ComputationResource where
  cost f := f.resource
  cost_id _ := rfl
  cost_comp _ _ := le_rfl

/-- Executing a composite is ordinary function composition. -/
@[simp]
theorem run_comp (f : W ⟶ X) (g : X ⟶ Y) (w : W) :
    (f ≫ g).run w = g.run (f.run w) :=
  rfl

/-- Serial composition adds every resource coordinate exactly. -/
@[simp]
theorem resource_comp (f : W ⟶ X) (g : X ⟶ Y) :
    (f ≫ g).resource = f.resource + g.resource :=
  rfl

/-- Run two total computations independently on a product input. -/
def tensor (f : W ⟶ X) (g : Y ⟶ Z) :
    Object.tensor W Y ⟶ Object.tensor X Z :=
  ⟨fun input ↦ (f.run input.1, g.run input.2), f.resource + g.resource⟩

/-- Parallel execution applies each component to its corresponding input. -/
@[simp]
theorem tensor_run (f : W ⟶ X) (g : Y ⟶ Z) (input : W × Y) :
    (tensor f g).run input = (f.run input.1, g.run input.2) :=
  rfl

/-- Parallel composition adds every formal resource coordinate exactly. -/
@[simp]
theorem tensor_resource (f : W ⟶ X) (g : Y ⟶ Z) :
    (tensor f g).resource = f.resource + g.resource :=
  rfl

/-- Parallel composition preserves identity computations. -/
theorem tensor_id (X Y : Object.{u}) :
    tensor (𝟙 X) (𝟙 Y) = 𝟙 (Object.tensor X Y) := by
  apply Hom.ext
  · rfl
  · change (0 : ComputationResource) + 0 = 0
    simp

/-- Parallel and serial composition satisfy the interchange law. -/
theorem tensor_comp {A B C D E F : Object.{u}}
    (f : A ⟶ B) (f' : B ⟶ C) (g : D ⟶ E) (g' : E ⟶ F) :
    tensor (f ≫ f') (g ≫ g') = tensor f g ≫ tensor f' g' := by
  apply Hom.ext
  · rfl
  · simp [add_comm, add_left_comm]

/-- Independent parallel execution is a bifunctor on total computations. -/
def tensorFunctor : Object.{u} × Object.{u} ⥤ Object.{u} where
  obj pair := Object.tensor pair.1 pair.2
  map pair := tensor pair.1 pair.2
  map_id pair := tensor_id pair.1 pair.2
  map_comp f g := tensor_comp f.1 g.1 f.2 g.2

/-- Executable componentwise budget check for a total computation. -/
def withinBudget (budget : ComputationResource) (f : X ⟶ Y) : Bool :=
  ComputationResource.within f.resource budget

/-- A successful executable check yields the generic proof-level budget
judgment for the total-computation category. -/
theorem withinBudget_sound {budget : ComputationResource} {f : X ⟶ Y}
    (h : withinBudget budget f = true) : WithinBudget budget f :=
  ComputationResource.within_sound h

end Ript.Models.Computation.Total
