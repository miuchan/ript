import Mathlib.CategoryTheory.Products.Basic
import Ript.Models.Computation.Resource
import Ript.Models.FiniteStochastic
import Ript.Resource.Budget

/-!
# Exact randomized computations with multidimensional resources

Objects are finite executable value types.  A morphism combines an exact
rational stochastic kernel with a four-coordinate formal computation resource.
Sequential and independent parallel composition use the stochastic channel
laws and add resources exactly.  Thus probabilistic behavior is executable
without erasing the distinction between probability and resource-accounted
randomized computation.
-/

set_option autoImplicit false

namespace Ript.Models.Computation.Randomized

open CategoryTheory
open Ript.Core
open Ript.Models.Computation
open Ript.Models.FiniteStochastic
open Ript.Resource

universe u

/-- Finite executable interface of a randomized computation. -/
structure Object where
  /-- Exact finite carrier shared with the stochastic kernel. -/
  classical : FiniteStochastic.Object.{u}

namespace Object

instance : CoeSort Object (Type u) :=
  ⟨fun object ↦ object.classical⟩

/-- Bundle a finite executable value type. -/
abbrev of (X : Type u) [Fintype X] [DecidableEq X] : Object :=
  ⟨FiniteStochastic.Object.of X⟩

/-- Unit interface. -/
abbrev unit : Object.{u} := ⟨FiniteStochastic.Object.unit⟩

/-- Product interface for independent randomized execution. -/
abbrev tensor (X Y : Object.{u}) : Object.{u} :=
  ⟨FiniteStochastic.Object.tensor X.classical Y.classical⟩

end Object

/-- Exact randomized program with an explicit formal resource vector. -/
@[ext]
structure Hom (X Y : Object.{u}) where
  /-- Executable exact stochastic behavior. -/
  channel : FinStoch X.classical Y.classical
  /-- Declared steps, queries, storage, and gates. -/
  resource : ComputationResource

variable {V W X Y Z : Object.{u}}

/-- Resource-accounted randomized programs form a category. -/
instance category : Category.{u} Object.{u} where
  Hom := Hom
  id X := ⟨FinStoch.identity X.classical, 0⟩
  comp first second :=
    ⟨FinStoch.comp first.channel second.channel,
      first.resource + second.resource⟩
  id_comp := by
    intro X Y program
    apply Hom.ext
    · exact FinStoch.category.id_comp program.channel
    · simp
  comp_id := by
    intro X Y program
    apply Hom.ext
    · exact FinStoch.category.comp_id program.channel
    · simp
  assoc := by
    intro U V W X first second third
    apply Hom.ext
    · exact FinStoch.category.assoc first.channel second.channel third.channel
    · simp [add_assoc]

/-- Construct a randomized program from its exact channel and resource. -/
def mk (channel : FinStoch X.classical Y.classical)
    (resource : ComputationResource) : X ⟶ Y :=
  ⟨channel, resource⟩

/-- Program cost is exactly its stored resource vector. -/
instance processCost : HasProcessCost Object ComputationResource where
  cost program := program.resource
  cost_id _ := rfl
  cost_comp _ _ := le_rfl

@[simp]
theorem channel_id (X : Object.{u}) :
    (𝟙 X : X ⟶ X).channel = FinStoch.identity X.classical :=
  rfl

@[simp]
theorem channel_comp (first : V ⟶ W) (second : W ⟶ X) :
    (first ≫ second).channel =
      FinStoch.comp first.channel second.channel :=
  rfl

@[simp]
theorem resource_id (X : Object.{u}) :
    (𝟙 X : X ⟶ X).resource = 0 :=
  rfl

@[simp]
theorem resource_comp (first : V ⟶ W) (second : W ⟶ X) :
    (first ≫ second).resource = first.resource + second.resource :=
  rfl

/-- Probability of one exact randomized output. -/
def probability (program : X ⟶ Y) (input : X) (output : Y) : ℚ≥0 :=
  program.channel.prob input output

@[simp]
theorem probability_apply (program : X ⟶ Y) (input : X) (output : Y) :
    probability program input output = program.channel.prob input output :=
  rfl

/-- Independent execution tensors kernels and adds resources. -/
def tensor (first : V ⟶ W) (second : X ⟶ Y) :
    Object.tensor V X ⟶ Object.tensor W Y :=
  ⟨FinStoch.tensor first.channel second.channel,
    first.resource + second.resource⟩

@[simp]
theorem tensor_channel (first : V ⟶ W) (second : X ⟶ Y) :
    (tensor first second).channel =
      FinStoch.tensor first.channel second.channel :=
  rfl

@[simp]
theorem tensor_resource (first : V ⟶ W) (second : X ⟶ Y) :
    (tensor first second).resource = first.resource + second.resource :=
  rfl

theorem tensor_id (X Y : Object.{u}) :
    tensor (𝟙 X) (𝟙 Y) = 𝟙 (Object.tensor X Y) := by
  apply Hom.ext
  · exact FinStoch.tensor_id X.classical Y.classical
  · simp

theorem tensor_comp {A B C D E F : Object.{u}}
    (first : A ⟶ B) (first' : B ⟶ C)
    (second : D ⟶ E) (second' : E ⟶ F) :
    tensor (first ≫ first') (second ≫ second') =
      tensor first second ≫ tensor first' second' := by
  apply Hom.ext
  · exact FinStoch.tensor_comp first.channel first'.channel
      second.channel second'.channel
  · simp [add_comm, add_left_comm]

/-- Independent execution bifunctor. -/
def tensorFunctor : Object.{u} × Object.{u} ⥤ Object.{u} where
  obj pair := Object.tensor pair.1 pair.2
  map pair := tensor pair.1 pair.2
  map_id pair := tensor_id pair.1 pair.2
  map_comp first second := tensor_comp first.1 second.1 first.2 second.2

/-- Executable componentwise resource check. -/
def withinBudget (budget : ComputationResource) (program : X ⟶ Y) : Bool :=
  ComputationResource.within program.resource budget

theorem withinBudget_sound {budget : ComputationResource} {program : X ⟶ Y}
    (success : withinBudget budget program = true) :
    WithinBudget budget program :=
  ComputationResource.within_sound success

end Ript.Models.Computation.Randomized
