import Ript.Resource.Monotone
import Ript.Semantics.MonoidalTermModel

/-!
# Initiality of the resource-aware symmetric monoidal term model

Every cost-respecting interpretation of a monoidal signature extends to a
resource-nonincreasing functor out of the quotient term model.  The functor is
defined by evaluation on representatives; semantic soundness makes this
definition independent of the chosen representative.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

namespace Free

variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [HasProcessCost C R] [HasParallelProcessCost C R]
variable [HasFreeStructuralCost C R]

/-- The ordinary functor induced by a monoidal interpretation. -/
def liftFunctor (interpretation : MonoidalInterpretation signature C) :
    MonoidalTermModel signature ⥤ C where
  obj X := monoidalObjEval interpretation.wire X.object
  map {X Y} := Quotient.lift (fun expression ↦ monoidalEval interpretation expression)
    (fun _ _ derivation ↦ monoidal_soundness interpretation derivation)
  map_id X := rfl
  map_comp {X Y Z} f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The lifted functor is strong monoidal. Its unit and tensor comparison maps
are identities because object evaluation preserves the formal unit and tensor
definitionally. -/
instance liftFunctorMonoidal (interpretation : MonoidalInterpretation signature C) :
    (liftFunctor interpretation).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := fun f X' => by
        rcases X' with ⟨X'⟩
        induction f using Quotient.inductionOn with
        | _ expression =>
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          change monoidalEval interpretation expression ▷
              monoidalObjEval interpretation.wire X' =
            monoidalEval interpretation (.tensor expression (.id X'))
          simp
      μIso_hom_natural_right := fun X' f => by
        rcases X' with ⟨X'⟩
        induction f using Quotient.inductionOn with
        | _ expression =>
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          change monoidalObjEval interpretation.wire X' ◁
              monoidalEval interpretation expression =
            monoidalEval interpretation (.tensor (.id X') expression)
          simp }

/-- The lifted strong monoidal functor preserves the symmetric braiding. -/
instance liftFunctorBraided (interpretation : MonoidalInterpretation signature C) :
    (liftFunctor interpretation).Braided where
  braided X Y := by
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    change 𝟙 _ ≫ monoidalEval interpretation (.braid X Y) =
      (β_ (monoidalObjEval interpretation.wire X)
        (monoidalObjEval interpretation.wire Y)).hom ≫ 𝟙 _
    simp [monoidalEval]

/-- Every cost-respecting interpretation extends to a resource-nonincreasing
functor out of the free symmetric monoidal term model. -/
def lift (interpretation : MonoidalInterpretation signature C) :
    ResourceMonotoneFunctor (MonoidalTermModel signature) C R where
  toFunctor := liftFunctor interpretation
  map_cost_le {X Y} f := by
    induction f using Quotient.inductionOn with
    | _ expression => exact monoidalEval_cost_le interpretation expression

/-- A strict resource-aware symmetric monoidal extension of an interpretation.

The object action is fixed to recursive evaluation of the interpreted wires.
The remaining fields say explicitly that identities, composition, tensor,
coherence maps, braiding, and primitive generators are preserved.  This is the
strict morphism class in which the free lift is literally unique; for general
strong monoidal functors, the corresponding statement is uniqueness up to a
monoidal natural isomorphism. -/
structure StrictExtension (interpretation : MonoidalInterpretation signature C) where
  /-- Action on quotient morphisms. -/
  map : ∀ {X Y : MonoidalTermModel signature}, (X ⟶ Y) →
    (monoidalObjEval interpretation.wire X.object ⟶
      monoidalObjEval interpretation.wire Y.object)
  /-- Identity preservation. -/
  map_id : ∀ X : MonoidalTermModel signature,
    map (𝟙 X) = 𝟙 (monoidalObjEval interpretation.wire X.object)
  /-- Sequential composition preservation. -/
  map_comp : ∀ {X Y Z : MonoidalTermModel signature} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f ≫ map g
  /-- Parallel composition preservation. -/
  map_tensor : ∀ {X₁ Y₁ X₂ Y₂ : MonoidalTermModel signature}
      (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    map (f ⊗ₘ g) = map f ⊗ₘ map g
  /-- Preservation of the associator. -/
  map_associator : ∀ X Y Z : MonoidalTermModel signature,
    map (α_ X Y Z).hom =
      (α_ (monoidalObjEval interpretation.wire X.object)
        (monoidalObjEval interpretation.wire Y.object)
        (monoidalObjEval interpretation.wire Z.object)).hom
  /-- Preservation of the inverse associator. -/
  map_associatorInv : ∀ X Y Z : MonoidalTermModel signature,
    map (α_ X Y Z).inv =
      (α_ (monoidalObjEval interpretation.wire X.object)
        (monoidalObjEval interpretation.wire Y.object)
        (monoidalObjEval interpretation.wire Z.object)).inv
  /-- Preservation of the left unitor. -/
  map_leftUnitor : ∀ X : MonoidalTermModel signature,
    map (λ_ X).hom = (λ_ (monoidalObjEval interpretation.wire X.object)).hom
  /-- Preservation of the inverse left unitor. -/
  map_leftUnitorInv : ∀ X : MonoidalTermModel signature,
    map (λ_ X).inv = (λ_ (monoidalObjEval interpretation.wire X.object)).inv
  /-- Preservation of the right unitor. -/
  map_rightUnitor : ∀ X : MonoidalTermModel signature,
    map (ρ_ X).hom = (ρ_ (monoidalObjEval interpretation.wire X.object)).hom
  /-- Preservation of the inverse right unitor. -/
  map_rightUnitorInv : ∀ X : MonoidalTermModel signature,
    map (ρ_ X).inv = (ρ_ (monoidalObjEval interpretation.wire X.object)).inv
  /-- Preservation of the symmetric braiding. -/
  map_braid : ∀ X Y : MonoidalTermModel signature,
    map (β_ X Y).hom =
      (β_ (monoidalObjEval interpretation.wire X.object)
        (monoidalObjEval interpretation.wire Y.object)).hom
  /-- Agreement with the supplied interpretation on primitive generators. -/
  map_generator : ∀ {X Y : signature.Obj} (generator : signature.Gen X Y),
    map (MonoidalTermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator
  /-- The extension never increases resource cost. -/
  map_cost_le : ∀ {X Y : MonoidalTermModel signature} (f : X ⟶ Y),
    processCost (R := R) (map f) ≤ processCost (R := R) f

namespace StrictExtension

variable {interpretation : MonoidalInterpretation signature C}

/-- Forget a strict extension to its ordinary functor. -/
def toFunctor (extension : StrictExtension interpretation) :
    MonoidalTermModel signature ⥤ C where
  obj X := monoidalObjEval interpretation.wire X.object
  map := extension.map
  map_id := extension.map_id
  map_comp := extension.map_comp

/-- Forget a strict extension to its resource-nonincreasing functor. -/
def toResourceMonotoneFunctor (extension : StrictExtension interpretation) :
    ResourceMonotoneFunctor (MonoidalTermModel signature) C R where
  toFunctor := extension.toFunctor
  map_cost_le := extension.map_cost_le

omit [ResourceAlgebra R] [HasParallelProcessCost C R] [HasFreeStructuralCost C R] in
/-- A strict extension is forced to evaluate every raw expression
recursively. -/
theorem map_quote_eq_eval (extension : StrictExtension interpretation)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    extension.map (MonoidalTermModel.quote signature expression) =
      monoidalEval interpretation expression := by
  induction expression with
  | gen generator => exact extension.map_generator generator
  | id X => exact extension.map_id ⟨X⟩
  | comp f g ihf ihg =>
      rw [MonoidalTermModel.quote_comp, extension.map_comp, ihf, ihg]
      rfl
  | tensor f g ihf ihg =>
      rw [MonoidalTermModel.quote_tensor, extension.map_tensor, ihf, ihg]
      rfl
  | associator X Y Z => exact extension.map_associator ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | associatorInv X Y Z => exact extension.map_associatorInv ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | leftUnitor X => exact extension.map_leftUnitor ⟨X⟩
  | leftUnitorInv X => exact extension.map_leftUnitorInv ⟨X⟩
  | rightUnitor X => exact extension.map_rightUnitor ⟨X⟩
  | rightUnitorInv X => exact extension.map_rightUnitorInv ⟨X⟩
  | braid X Y => exact extension.map_braid ⟨X⟩ ⟨Y⟩

end StrictExtension

/-- The universal lift, bundled with its strict preservation laws. -/
def strictExtension (interpretation : MonoidalInterpretation signature C) :
    StrictExtension interpretation where
  map := (lift interpretation).toFunctor.map
  map_id X := (lift interpretation).toFunctor.map_id X
  map_comp f g := (lift interpretation).toFunctor.map_comp f g
  map_tensor f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl
  map_associator _ _ _ := rfl
  map_associatorInv _ _ _ := rfl
  map_leftUnitor _ := rfl
  map_leftUnitorInv _ := rfl
  map_rightUnitor _ := rfl
  map_rightUnitorInv _ := rfl
  map_braid _ _ := rfl
  map_generator _ := rfl
  map_cost_le := (lift interpretation).map_cost_le

/-- **Uniqueness of the free lift.** Every strict resource-aware symmetric
monoidal extension agreeing with an interpretation on generators has the same
action as `lift` on every quotient morphism. -/
theorem lift_unique (interpretation : MonoidalInterpretation signature C)
    (extension : StrictExtension interpretation)
    {X Y : MonoidalTermModel signature} (f : X ⟶ Y) :
    extension.map f = (lift interpretation).toFunctor.map f := by
  induction f using Quotient.inductionOn with
  | _ expression => exact extension.map_quote_eq_eval expression

@[simp]
theorem lift_obj (interpretation : MonoidalInterpretation signature C)
    (X : MonoidalTermModel signature) :
    (lift interpretation).toFunctor.obj X =
      monoidalObjEval interpretation.wire X.object :=
  rfl

@[simp]
theorem lift_map_quote (interpretation : MonoidalInterpretation signature C)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    (lift interpretation).toFunctor.map (MonoidalTermModel.quote signature expression) =
      monoidalEval interpretation expression :=
  rfl

/-- The universal lift agrees with the supplied interpretation on every
primitive generator. -/
theorem lift_on_generator (interpretation : MonoidalInterpretation signature C)
    {X Y : signature.Obj} (generator : signature.Gen X Y) :
    (lift interpretation).toFunctor.map
        (MonoidalTermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator :=
  rfl

/-- The universal lift never increases resource cost. -/
theorem lift_preserves_cost (interpretation : MonoidalInterpretation signature C)
    {X Y : MonoidalTermModel signature} (f : X ⟶ Y) :
    processCost (R := R) ((lift interpretation).toFunctor.map f) ≤
      processCost (R := R) f :=
  (lift interpretation).map_cost_le f

end Free

end Ript.Semantics
