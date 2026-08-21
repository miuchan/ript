import Ript.Core.ResourceChange
import Ript.Semantics.MonoidalTermModel
import Ript.Semantics.ResourceChangingInterpretation

/-!
# Initiality of the symmetric monoidal term model across resource algebras

Every heterogeneous symmetric monoidal interpretation of an `R`-costed
signature in an `S`-costed model extends directly from the original free term
model.  The extension is strong symmetric monoidal and changes costs only
along the advertised ordered additive map `φ : R →+o S`.
-/

set_option autoImplicit false

namespace Ript.Semantics.ResourceChangingMonoidalFree

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [PartialOrder S] [ResourceAlgebra S]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C]
variable [SymmetricCategory C] [HasProcessCost C S]
variable [HasParallelProcessCost C S] [HasFreeStructuralCost C S]
variable {φ : R →+o S}

/-- The ordinary functor induced by a heterogeneous monoidal interpretation. -/
def liftFunctor
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    MonoidalTermModel signature ⥤ C where
  obj X := monoidalObjEval interpretation.wire X.object
  map {X Y} := Quotient.lift
    (fun expression ↦
      ResourceChangingMonoidalInterpretation.eval interpretation expression)
    (fun _ _ derivation ↦
      ResourceChangingMonoidalInterpretation.soundness interpretation derivation)
  map_id _ := rfl
  map_comp {X Y Z} left right := by
    induction left using Quotient.inductionOn with
    | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The heterogeneous lift is strong monoidal with identity comparison maps. -/
instance liftFunctorMonoidal
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    (liftFunctor interpretation).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := fun morphism X' => by
        rcases X' with ⟨X'⟩
        induction morphism using Quotient.inductionOn with
        | _ expression =>
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          change
            ResourceChangingMonoidalInterpretation.eval interpretation expression ▷
                monoidalObjEval interpretation.wire X' =
              ResourceChangingMonoidalInterpretation.eval interpretation
                (.tensor expression (.id X'))
          simp [ResourceChangingMonoidalInterpretation.eval,
            ResourceChangingMonoidalInterpretation.toMappedCost,
            MonoidalExpr.mapCost]
      μIso_hom_natural_right := fun X' morphism => by
        rcases X' with ⟨X'⟩
        induction morphism using Quotient.inductionOn with
        | _ expression =>
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          change
            monoidalObjEval interpretation.wire X' ◁
                ResourceChangingMonoidalInterpretation.eval interpretation expression =
              ResourceChangingMonoidalInterpretation.eval interpretation
                (.tensor (.id X') expression)
          simp [ResourceChangingMonoidalInterpretation.eval,
            ResourceChangingMonoidalInterpretation.toMappedCost,
            MonoidalExpr.mapCost] }

/-- The heterogeneous lift preserves the symmetric braiding. -/
instance liftFunctorBraided
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    (liftFunctor interpretation).Braided where
  braided X Y := by
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    change 𝟙 _ ≫
        ResourceChangingMonoidalInterpretation.eval interpretation (.braid X Y) =
      (β_ (monoidalObjEval interpretation.wire X)
        (monoidalObjEval interpretation.wire Y)).hom ≫ 𝟙 _
    simp [ResourceChangingMonoidalInterpretation.eval,
      ResourceChangingMonoidalInterpretation.toMappedCost, monoidalEval,
      MonoidalExpr.mapCost]
    exact Category.id_comp _

/-- **Heterogeneous monoidal free lift.** The target cost of every mapped
process is bounded by `φ` of its exact source cost. -/
def lift
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    ResourceChangeFunctor (MonoidalTermModel signature) C R S φ where
  toFunctor := liftFunctor interpretation
  map_cost_le {X Y} morphism := by
    induction morphism using Quotient.inductionOn with
    | _ expression =>
      exact ResourceChangingMonoidalInterpretation.eval_cost_le
        interpretation expression

/-- A strict resource-changing symmetric monoidal extension. -/
structure StrictExtension
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) where
  /-- Action on quotient morphisms. -/
  map : ∀ {X Y : MonoidalTermModel signature}, (X ⟶ Y) →
    (monoidalObjEval interpretation.wire X.object ⟶
      monoidalObjEval interpretation.wire Y.object)
  /-- Identity preservation. -/
  map_id : ∀ X : MonoidalTermModel signature,
    map (𝟙 X) = 𝟙 (monoidalObjEval interpretation.wire X.object)
  /-- Sequential composition preservation. -/
  map_comp : ∀ {X Y Z : MonoidalTermModel signature} (left : X ⟶ Y)
    (right : Y ⟶ Z), map (left ≫ right) = map left ≫ map right
  /-- Parallel composition preservation. -/
  map_tensor : ∀ {X₁ Y₁ X₂ Y₂ : MonoidalTermModel signature}
    (left : X₁ ⟶ Y₁) (right : X₂ ⟶ Y₂),
    map (left ⊗ₘ right) = map left ⊗ₘ map right
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
  /-- Agreement on primitive generators. -/
  map_generator : ∀ {X Y : signature.Obj} (generator : signature.Gen X Y),
    map (MonoidalTermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator
  /-- Translated resource-cost bound. -/
  map_cost_le : ∀ {X Y : MonoidalTermModel signature} (morphism : X ⟶ Y),
    processCost (R := S) (map morphism) ≤
      φ (processCost (R := R) morphism)

namespace StrictExtension

variable {interpretation : ResourceChangingMonoidalInterpretation.Interpretation
  (signature := signature) (C := C) φ}

omit [ResourceAlgebra S] [HasParallelProcessCost C S]
  [HasFreeStructuralCost C S] in
/-- Strict extensions are determined by their morphism action. -/
@[ext]
theorem ext (left right : StrictExtension interpretation)
    (map_eq : @left.map = @right.map) : left = right := by
  cases left
  cases right
  cases map_eq
  rfl

/-- Forget to the ordinary functor. -/
def toFunctor (extension : StrictExtension interpretation) :
    MonoidalTermModel signature ⥤ C where
  obj X := monoidalObjEval interpretation.wire X.object
  map := extension.map
  map_id := extension.map_id
  map_comp := extension.map_comp

/-- Forget to the resource-changing functor. -/
def toResourceChangeFunctor (extension : StrictExtension interpretation) :
    ResourceChangeFunctor (MonoidalTermModel signature) C R S φ where
  toFunctor := extension.toFunctor
  map_cost_le := extension.map_cost_le

omit [ResourceAlgebra S] [HasParallelProcessCost C S]
  [HasFreeStructuralCost C S] in
/-- Every strict extension is forced to evaluate all raw monoidal syntax. -/
theorem map_quote_eq_eval (extension : StrictExtension interpretation)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    extension.map (MonoidalTermModel.quote signature expression) =
      ResourceChangingMonoidalInterpretation.eval interpretation expression := by
  induction expression with
  | gen generator => exact extension.map_generator generator
  | id X => exact extension.map_id ⟨X⟩
  | comp left right leftIH rightIH =>
      rw [MonoidalTermModel.quote_comp, extension.map_comp, leftIH, rightIH]
      rfl
  | tensor left right leftIH rightIH =>
      rw [MonoidalTermModel.quote_tensor, extension.map_tensor, leftIH, rightIH]
      rfl
  | associator X Y Z => exact extension.map_associator ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | associatorInv X Y Z => exact extension.map_associatorInv ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  | leftUnitor X => exact extension.map_leftUnitor ⟨X⟩
  | leftUnitorInv X => exact extension.map_leftUnitorInv ⟨X⟩
  | rightUnitor X => exact extension.map_rightUnitor ⟨X⟩
  | rightUnitorInv X => exact extension.map_rightUnitorInv ⟨X⟩
  | braid X Y => exact extension.map_braid ⟨X⟩ ⟨Y⟩

end StrictExtension

/-- The canonical heterogeneous monoidal lift as a strict extension. -/
def strictExtension
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    StrictExtension interpretation where
  map := (lift interpretation).toFunctor.map
  map_id X := (lift interpretation).toFunctor.map_id X
  map_comp left right := (lift interpretation).toFunctor.map_comp left right
  map_tensor left right := by
    induction left using Quotient.inductionOn with
    | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => rfl
  map_associator _ _ _ := rfl
  map_associatorInv _ _ _ := rfl
  map_leftUnitor _ := rfl
  map_leftUnitorInv _ := rfl
  map_rightUnitor _ := rfl
  map_rightUnitorInv _ := rfl
  map_braid _ _ := rfl
  map_generator _ := rfl
  map_cost_le := (lift interpretation).map_cost_le

/-- **Uniqueness of the heterogeneous monoidal free lift.** -/
theorem lift_unique
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (extension : StrictExtension interpretation)
    {X Y : MonoidalTermModel signature} (morphism : X ⟶ Y) :
    extension.map morphism = (lift interpretation).toFunctor.map morphism := by
  induction morphism using Quotient.inductionOn with
  | _ expression => exact extension.map_quote_eq_eval expression

/-- Every strict extension equals the canonical one as structured data. -/
theorem strictExtension_unique
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (extension : StrictExtension interpretation) :
    extension = strictExtension interpretation := by
  apply StrictExtension.ext
  funext X Y morphism
  exact lift_unique interpretation extension morphism

/-- **Contractible heterogeneous monoidal universal property.** -/
def strictExtensionEquivPUnit
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    StrictExtension interpretation ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := strictExtension interpretation
  left_inv extension := (strictExtension_unique interpretation extension).symm
  right_inv point := by cases point; rfl

@[simp]
theorem lift_map_quote
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    (lift interpretation).toFunctor.map
        (MonoidalTermModel.quote signature expression) =
      ResourceChangingMonoidalInterpretation.eval interpretation expression :=
  rfl

/-- The free lift agrees with every supplied generator. -/
theorem lift_on_generator
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (generator : signature.Gen X Y) :
    (lift interpretation).toFunctor.map
        (MonoidalTermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator :=
  rfl

/-- The free lift obeys the translated cost bound on every morphism. -/
theorem lift_preserves_translated_cost
    (interpretation : ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : MonoidalTermModel signature} (morphism : X ⟶ Y) :
    processCost (R := S) ((lift interpretation).toFunctor.map morphism) ≤
      φ (processCost (R := R) morphism) :=
  (lift interpretation).map_cost_le morphism

end Ript.Semantics.ResourceChangingMonoidalFree
