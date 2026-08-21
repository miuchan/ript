import Ript.Core.ResourceChange
import Ript.Semantics.ResourceChangingInterpretation
import Ript.Semantics.SequentialInitiality

/-!
# Initiality across resource algebras

A heterogeneous interpretation of an `R`-costed sequential signature in an
`S`-costed category extends uniquely from the original quotient term model.
The extension is a `ResourceChangeFunctor`: semantic cost is bounded by the
ordered additive image of the exact free-model cost.
-/

set_option autoImplicit false

namespace Ript.Semantics.ResourceChangingSequentialFree

open CategoryTheory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [PartialOrder S] [ResourceAlgebra S]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C S]
variable {φ : R →+o S}

/-- The ordinary functor induced by a heterogeneous interpretation. -/
def liftFunctor
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    CategoryTheory.Functor (TermModel signature) C where
  obj X := interpretation.obj X
  map {X Y} := Quotient.lift
    (fun expression ↦ ResourceChangingInterpretation.eval interpretation expression)
    (fun _ _ derivation ↦
      ResourceChangingInterpretation.soundness interpretation derivation)
  map_id _ := rfl
  map_comp {X Y Z} left right := by
    induction left using Quotient.inductionOn with
    | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => rfl

/-- **Heterogeneous free lift.** Every resource-changing interpretation
extends from the original term model along its explicit resource map. -/
def lift
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    ResourceChangeFunctor (TermModel signature) C R S φ where
  toFunctor := liftFunctor interpretation
  map_cost_le {X Y} morphism := by
    induction morphism using Quotient.inductionOn with
    | _ expression =>
      exact ResourceChangingInterpretation.eval_cost_le interpretation expression

/-- A strict heterogeneous extension with fixed object and generator action. -/
structure StrictExtension
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) where
  /-- Action on quotient morphisms. -/
  map : ∀ {X Y : TermModel signature}, (X ⟶ Y) →
    (interpretation.obj X ⟶ interpretation.obj Y)
  /-- Identity preservation. -/
  map_id : ∀ X : TermModel signature,
    map (𝟙 X) = 𝟙 (interpretation.obj X)
  /-- Composition preservation. -/
  map_comp : ∀ {X Y Z : TermModel signature} (left : X ⟶ Y)
    (right : Y ⟶ Z), map (left ≫ right) = map left ≫ map right
  /-- Agreement with the heterogeneous generator interpretation. -/
  map_generator : ∀ {X Y : TermModel signature} (generator : signature.Gen X Y),
    map (TermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator
  /-- Cost changes only through the advertised ordered additive map. -/
  map_cost_le : ∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
    processCost (R := S) (map morphism) ≤
      φ (processCost (R := R) morphism)

namespace StrictExtension

variable {interpretation : ResourceChangingInterpretation.Interpretation
  (signature := signature) (C := C) φ}

omit [ResourceAlgebra S] in
/-- Heterogeneous strict extensions are determined by their morphism action. -/
@[ext]
theorem ext (left right : StrictExtension interpretation)
    (map_eq : @left.map = @right.map) : left = right := by
  cases left
  cases right
  cases map_eq
  rfl

/-- Forget a strict heterogeneous extension to an ordinary functor. -/
def toFunctor (extension : StrictExtension interpretation) :
    CategoryTheory.Functor (TermModel signature) C where
  obj X := interpretation.obj X
  map := extension.map
  map_id := extension.map_id
  map_comp := extension.map_comp

/-- Forget to the bundled resource-changing functor. -/
def toResourceChangeFunctor (extension : StrictExtension interpretation) :
    ResourceChangeFunctor (TermModel signature) C R S φ where
  toFunctor := extension.toFunctor
  map_cost_le := extension.map_cost_le

omit [ResourceAlgebra S] in
/-- A strict heterogeneous extension is recursively forced on all syntax. -/
theorem map_quote_eq_eval (extension : StrictExtension interpretation)
    {X Y : TermModel signature} (expression : Expr signature X Y) :
    extension.map (TermModel.quote signature expression) =
      ResourceChangingInterpretation.eval interpretation expression := by
  induction expression with
  | gen generator => exact extension.map_generator generator
  | id X => exact extension.map_id X
  | comp left right leftIH rightIH =>
      change extension.map
          (TermModel.quote signature left ≫ TermModel.quote signature right) =
        ResourceChangingInterpretation.eval interpretation left ≫
          ResourceChangingInterpretation.eval interpretation right
      rw [extension.map_comp, leftIH, rightIH]

end StrictExtension

/-- The heterogeneous lift bundled as a strict extension. -/
def strictExtension
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    StrictExtension interpretation where
  map := (lift interpretation).toFunctor.map
  map_id X := (lift interpretation).toFunctor.map_id X
  map_comp left right := (lift interpretation).toFunctor.map_comp left right
  map_generator _ := rfl
  map_cost_le := (lift interpretation).map_cost_le

/-- **Heterogeneous free-model uniqueness.** Every strict extension with the
same resource map and generator action is equal to evaluation on morphisms. -/
theorem lift_unique
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (extension : StrictExtension interpretation)
    {X Y : TermModel signature} (morphism : X ⟶ Y) :
    extension.map morphism = (lift interpretation).toFunctor.map morphism := by
  induction morphism using Quotient.inductionOn with
  | _ expression => exact extension.map_quote_eq_eval expression

/-- Every heterogeneous strict extension equals the canonical lift as
structured data. -/
theorem strictExtension_unique
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (extension : StrictExtension interpretation) :
    extension = strictExtension interpretation := by
  apply StrictExtension.ext
  funext X Y morphism
  exact lift_unique interpretation extension morphism

/-- **Contractible heterogeneous universal-property witness.** The type of
strict extensions along a fixed resource map is equivalent to one point. -/
def strictExtensionEquivPUnit
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    StrictExtension interpretation ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := strictExtension interpretation
  left_inv extension := (strictExtension_unique interpretation extension).symm
  right_inv point := by cases point; rfl

/-! ## Classification across resource algebras -/

/-- Restrict a resource-changing functor from the free term model to a
heterogeneous interpretation of the primitive signature. -/
def interpretationOfResourceChangeFunctor
    (functor : ResourceChangeFunctor (TermModel signature) C R S φ) :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ where
  obj X := functor.toFunctor.obj X
  mapGen generator :=
    functor.toFunctor.map (TermModel.quote signature (.gen generator))
  mapGen_cost generator := by
    calc
      processCost (R := S)
          (functor.toFunctor.map
            (TermModel.quote signature (.gen generator))) ≤
          φ (processCost (R := R)
            (TermModel.quote signature (.gen generator))) :=
        functor.map_cost_le _
      _ = φ (signature.cost generator) := rfl

omit [ResourceAlgebra S] in
/-- Heterogeneous evaluation restricted from a resource-changing functor is
exactly that functor's action on quotation. -/
theorem eval_interpretationOfResourceChangeFunctor
    (functor : ResourceChangeFunctor (TermModel signature) C R S φ)
    {X Y : signature.Obj} (expression : Expr signature X Y) :
    ResourceChangingInterpretation.eval
        (interpretationOfResourceChangeFunctor functor) expression =
      functor.toFunctor.map (TermModel.quote signature expression) := by
  induction expression with
  | gen generator => rfl
  | id X => exact (functor.toFunctor.map_id X).symm
  | comp left right leftIH rightIH =>
    change
      ResourceChangingInterpretation.eval
          (interpretationOfResourceChangeFunctor functor) left ≫
        ResourceChangingInterpretation.eval
          (interpretationOfResourceChangeFunctor functor) right = _
    rw [TermModel.quote_comp, functor.toFunctor.map_comp, leftIH, rightIH]
    rfl

/-- Restricting the heterogeneous free lift recovers the original
interpretation. -/
theorem interpretationOfResourceChangeFunctor_lift
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) :
    interpretationOfResourceChangeFunctor (lift interpretation) =
      interpretation := by
  cases interpretation
  rfl

/-- Every resource-changing functor from the free term model is recovered from
its primitive-generator interpretation. -/
theorem lift_interpretationOfResourceChangeFunctor
    (functor : ResourceChangeFunctor (TermModel signature) C R S φ) :
    lift (interpretationOfResourceChangeFunctor functor) = functor := by
  apply ResourceChangeFunctor.ext
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro X Y morphism
  induction morphism using Quotient.inductionOn with
  | _ expression =>
    exact heq_of_eq
      (eval_interpretationOfResourceChangeFunctor functor expression)

/-- **Heterogeneous interpretation classification theorem.** Interpreting an
`R`-costed signature in an `S`-costed category along `φ` is equivalent to
giving a `ResourceChangeFunctor` from the original free term model. -/
def interpretationEquivResourceChangeFunctor :
    ResourceChangingInterpretation.Interpretation
        (signature := signature) (C := C) φ ≃
      ResourceChangeFunctor (TermModel signature) C R S φ where
  toFun := lift
  invFun := interpretationOfResourceChangeFunctor
  left_inv := interpretationOfResourceChangeFunctor_lift
  right_inv := lift_interpretationOfResourceChangeFunctor

@[simp]
theorem lift_map_quote
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : TermModel signature} (expression : Expr signature X Y) :
    (lift interpretation).toFunctor.map (TermModel.quote signature expression) =
      ResourceChangingInterpretation.eval interpretation expression :=
  rfl

/-- The heterogeneous lift agrees with every interpreted generator. -/
theorem lift_on_generator
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : TermModel signature} (generator : signature.Gen X Y) :
    (lift interpretation).toFunctor.map
        (TermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator :=
  rfl

/-- The heterogeneous lift satisfies the translated cost bound. -/
theorem lift_preserves_translated_cost
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : TermModel signature} (morphism : X ⟶ Y) :
    processCost (R := S) ((lift interpretation).toFunctor.map morphism) ≤
      φ (processCost (R := R) morphism) :=
  (lift interpretation).map_cost_le morphism

end Ript.Semantics.ResourceChangingSequentialFree
