import Mathlib.CategoryTheory.EqToHom
import Ript.Resource.Monotone
import Ript.Semantics.Soundness
import Ript.Semantics.TermModel

/-!
# Initiality of the resource-aware sequential term model

Every cost-respecting interpretation of a sequential signature extends to a
resource-nonincreasing functor out of the quotient term model.  Evaluation on
representatives defines the extension, semantic soundness makes it
well-defined, and structural induction proves strict uniqueness among
extensions that agree on objects and primitive generators.
-/

set_option autoImplicit false

namespace Ript.Semantics.SequentialFree

open CategoryTheory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C R]

/-- The ordinary functor induced by a sequential interpretation. -/
def liftFunctor (interpretation : Interpretation signature C) :
    CategoryTheory.Functor (TermModel signature) C where
  obj X := interpretation.obj X
  map {X Y} := Quotient.lift (fun expression ↦ eval interpretation expression)
    (fun _ _ derivation ↦ soundness interpretation derivation)
  map_id _ := rfl
  map_comp {X Y Z} left right := by
    induction left using Quotient.inductionOn with
    | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => rfl

/-- Every cost-respecting sequential interpretation has a canonical
resource-nonincreasing extension from the free term model. -/
def lift (interpretation : Interpretation signature C) :
    ResourceMonotoneFunctor (TermModel signature) C R where
  toFunctor := liftFunctor interpretation
  map_cost_le {X Y} morphism := by
    induction morphism using Quotient.inductionOn with
    | _ expression => exact eval_cost_le interpretation expression

/-- A strict resource-aware extension whose object action is fixed by the
interpretation.  These are the morphisms for which the free lift is literally
unique, rather than merely naturally isomorphic. -/
structure StrictExtension (interpretation : Interpretation signature C) where
  /-- Action on quotient morphisms. -/
  map : ∀ {X Y : TermModel signature}, (X ⟶ Y) →
    (interpretation.obj X ⟶ interpretation.obj Y)
  /-- Identity preservation. -/
  map_id : ∀ X : TermModel signature,
    map (𝟙 X) = 𝟙 (interpretation.obj X)
  /-- Composition preservation. -/
  map_comp : ∀ {X Y Z : TermModel signature} (left : X ⟶ Y)
    (right : Y ⟶ Z), map (left ≫ right) = map left ≫ map right
  /-- Agreement with the supplied interpretation on generators. -/
  map_generator : ∀ {X Y : TermModel signature} (generator : signature.Gen X Y),
    map (TermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator
  /-- The extension never increases resource cost. -/
  map_cost_le : ∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
    processCost (R := R) (map morphism) ≤ processCost (R := R) morphism

namespace StrictExtension

variable {interpretation : Interpretation signature C}

omit [ResourceAlgebra R] in
/-- Strict extensions are determined by their action on morphisms; all law
fields are propositions and hence proof-irrelevant. -/
@[ext]
theorem ext (left right : StrictExtension interpretation)
    (map_eq : @left.map = @right.map) : left = right := by
  cases left
  cases right
  cases map_eq
  rfl

/-- Forget a strict extension to its ordinary functor. -/
def toFunctor (extension : StrictExtension interpretation) :
    CategoryTheory.Functor (TermModel signature) C where
  obj X := interpretation.obj X
  map := extension.map
  map_id := extension.map_id
  map_comp := extension.map_comp

/-- Forget a strict extension to its resource-nonincreasing functor. -/
def toResourceMonotoneFunctor (extension : StrictExtension interpretation) :
    ResourceMonotoneFunctor (TermModel signature) C R where
  toFunctor := extension.toFunctor
  map_cost_le := extension.map_cost_le

omit [ResourceAlgebra R] in
/-- Any strict extension is forced to evaluate every expression recursively. -/
theorem map_quote_eq_eval (extension : StrictExtension interpretation)
    {X Y : TermModel signature} (expression : Expr signature X Y) :
    extension.map (TermModel.quote signature expression) =
      eval interpretation expression := by
  induction expression with
  | gen generator => exact extension.map_generator generator
  | id X => exact extension.map_id X
  | comp left right leftIH rightIH =>
      change extension.map
          (TermModel.quote signature left ≫ TermModel.quote signature right) =
        eval interpretation left ≫ eval interpretation right
      rw [extension.map_comp, leftIH, rightIH]

end StrictExtension

/-- The canonical lift bundled with its strict preservation laws. -/
def strictExtension (interpretation : Interpretation signature C) :
    StrictExtension interpretation where
  map := (lift interpretation).toFunctor.map
  map_id X := (lift interpretation).toFunctor.map_id X
  map_comp left right := (lift interpretation).toFunctor.map_comp left right
  map_generator _ := rfl
  map_cost_le := (lift interpretation).map_cost_le

/-- **Sequential free-model uniqueness.** Every strict resource-aware
extension agreeing with an interpretation on generators has the same action
as the canonical lift on every quotient morphism. -/
theorem lift_unique (interpretation : Interpretation signature C)
    (extension : StrictExtension interpretation)
    {X Y : TermModel signature} (morphism : X ⟶ Y) :
    extension.map morphism = (lift interpretation).toFunctor.map morphism := by
  induction morphism using Quotient.inductionOn with
  | _ expression => exact extension.map_quote_eq_eval expression

/-- Every strict extension is the canonical free extension as structured
data, not only pointwise on morphisms. -/
theorem strictExtension_unique (interpretation : Interpretation signature C)
    (extension : StrictExtension interpretation) :
    extension = strictExtension interpretation := by
  apply StrictExtension.ext
  funext X Y morphism
  exact lift_unique interpretation extension morphism

/-- **Contractible universal-property witness.** For a fixed interpretation,
the type of strict resource-aware sequential extensions is equivalent to the
one-point type. -/
def strictExtensionEquivPUnit (interpretation : Interpretation signature C) :
    StrictExtension interpretation ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := strictExtension interpretation
  left_inv extension := (strictExtension_unique interpretation extension).symm
  right_inv point := by cases point; rfl

/-! ## Classification of all interpretations -/

/-- Restrict a resource-nonincreasing functor from the free term model to the
signature objects and primitive generators. -/
def interpretationOfResourceMonotoneFunctor
    (functor : ResourceMonotoneFunctor (TermModel signature) C R) :
    Interpretation signature C where
  obj X := functor.toFunctor.obj X
  mapGen generator :=
    functor.toFunctor.map (TermModel.quote signature (.gen generator))
  mapGen_cost generator := by
    calc
      processCost (R := R)
          (functor.toFunctor.map
            (TermModel.quote signature (.gen generator))) ≤
          processCost (R := R)
            (TermModel.quote signature (.gen generator)) :=
        functor.map_cost_le _
      _ = signature.cost generator := rfl

omit [ResourceAlgebra R] in
/-- Evaluation in the interpretation restricted from a functor is exactly
that functor's action on the quoted expression. -/
theorem eval_interpretationOfResourceMonotoneFunctor
    (functor : ResourceMonotoneFunctor (TermModel signature) C R)
    {X Y : signature.Obj} (expression : Expr signature X Y) :
    eval (interpretationOfResourceMonotoneFunctor functor) expression =
      functor.toFunctor.map (TermModel.quote signature expression) := by
  induction expression with
  | gen generator => rfl
  | id X => exact (functor.toFunctor.map_id X).symm
  | comp left right leftIH rightIH =>
    change
      eval (interpretationOfResourceMonotoneFunctor functor) left ≫
          eval (interpretationOfResourceMonotoneFunctor functor) right = _
    rw [TermModel.quote_comp, functor.toFunctor.map_comp, leftIH, rightIH]
    rfl

/-- Restricting the canonical lift recovers the original interpretation. -/
theorem interpretationOfResourceMonotoneFunctor_lift
    (interpretation : Interpretation signature C) :
    interpretationOfResourceMonotoneFunctor (lift interpretation) =
      interpretation := by
  cases interpretation
  rfl

/-- Every resource-nonincreasing functor from the free term model is recovered
from its action on primitive generators. -/
theorem lift_interpretationOfResourceMonotoneFunctor
  (functor : ResourceMonotoneFunctor (TermModel signature) C R) :
    lift (interpretationOfResourceMonotoneFunctor functor) = functor := by
  apply ResourceMonotoneFunctor.ext
  refine Functor.hext (fun _ ↦ rfl) ?_
  intro X Y morphism
  induction morphism using Quotient.inductionOn with
  | _ expression =>
    exact heq_of_eq
      (eval_interpretationOfResourceMonotoneFunctor functor expression)

/-- **Sequential interpretation classification theorem.** Giving a legal
interpretation of a signature is equivalent to giving a
resource-nonincreasing functor from its free quotient term model. -/
def interpretationEquivResourceMonotoneFunctor :
    Interpretation signature C ≃
      ResourceMonotoneFunctor (TermModel signature) C R where
  toFun := lift
  invFun := interpretationOfResourceMonotoneFunctor
  left_inv := interpretationOfResourceMonotoneFunctor_lift
  right_inv := lift_interpretationOfResourceMonotoneFunctor

@[simp]
theorem lift_obj (interpretation : Interpretation signature C)
    (X : TermModel signature) :
    (lift interpretation).toFunctor.obj X = interpretation.obj X :=
  rfl

@[simp]
theorem lift_map_quote (interpretation : Interpretation signature C)
    {X Y : TermModel signature} (expression : Expr signature X Y) :
    (lift interpretation).toFunctor.map (TermModel.quote signature expression) =
      eval interpretation expression :=
  rfl

/-- The universal lift agrees with the interpretation on every generator. -/
theorem lift_on_generator (interpretation : Interpretation signature C)
    {X Y : TermModel signature} (generator : signature.Gen X Y) :
    (lift interpretation).toFunctor.map
        (TermModel.quote signature (.gen generator)) =
      interpretation.mapGen generator :=
  rfl

/-- The universal lift never increases process cost. -/
theorem lift_preserves_cost (interpretation : Interpretation signature C)
    {X Y : TermModel signature} (morphism : X ⟶ Y) :
    processCost (R := R) ((lift interpretation).toFunctor.map morphism) ≤
      processCost (R := R) morphism :=
  (lift interpretation).map_cost_le morphism

end Ript.Semantics.SequentialFree
