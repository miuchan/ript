import Ript.Core.StructuralCost
import Ript.Semantics.MonoidalSoundness

/-!
# The free symmetric monoidal term model

Objects are free monoidal trees and morphisms are monoidal expressions modulo
the explicit derivation relation. The quotient is confined to this proof
model; unquotiented syntax remains executable.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Syntax

universe u w

/-- Object type of the free symmetric monoidal term model. The wrapper keeps
its category instance distinct from Mathlib's category on raw free-monoidal
object trees. -/
structure MonoidalTermModel {R : Type w} (signature : MonoidalSignature.{u, w} R) where
  /-- The object tree represented by a term-model object. -/
  object : signature.Obj

namespace MonoidalTermModel

variable {R : Type w} (signature : MonoidalSignature.{u, w} R)

/-- Category structure induced by sequential expression composition. -/
instance category : Category.{u} (MonoidalTermModel signature) where
  Hom X Y := Quotient (monoidalDerivesSetoid signature X.object Y.object)
  id X := ⟦MonoidalExpr.id X.object⟧
  comp := Quotient.map₂ MonoidalExpr.comp fun _ _ hf _ _ hg ↦
    MonoidalDerives.comp_congr hf hg
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (MonoidalDerives.id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (MonoidalDerives.comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (MonoidalDerives.assoc f g h)

/-- Raw monoidal operations and coherence isomorphisms on the quotient model. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (MonoidalTermModel signature) where
  tensorObj X Y := ⟨FreeMonoidalCategory.tensor X.object Y.object⟩
  whiskerLeft X _ _ f := Quotient.map
    (fun g ↦ MonoidalExpr.tensor (.id X.object) g)
    (fun _ _ h ↦ MonoidalDerives.tensor_congr (MonoidalDerives.refl _) h) f
  whiskerRight f Y := Quotient.map
    (fun g ↦ MonoidalExpr.tensor g (.id Y.object))
    (fun _ _ h ↦ MonoidalDerives.tensor_congr h (MonoidalDerives.refl _)) f
  tensorHom := Quotient.map₂ MonoidalExpr.tensor fun _ _ hf _ _ hg ↦
    MonoidalDerives.tensor_congr hf hg
  tensorUnit := ⟨FreeMonoidalCategory.unit⟩
  associator X Y Z :=
    { hom := ⟦MonoidalExpr.associator X.object Y.object Z.object⟧
      inv := ⟦MonoidalExpr.associatorInv X.object Y.object Z.object⟧
      hom_inv_id := Quotient.sound
        (MonoidalDerives.associator_hom_inv X.object Y.object Z.object)
      inv_hom_id := Quotient.sound
        (MonoidalDerives.associator_inv_hom X.object Y.object Z.object) }
  leftUnitor X :=
    { hom := ⟦MonoidalExpr.leftUnitor X.object⟧
      inv := ⟦MonoidalExpr.leftUnitorInv X.object⟧
      hom_inv_id := Quotient.sound (MonoidalDerives.leftUnitor_hom_inv X.object)
      inv_hom_id := Quotient.sound (MonoidalDerives.leftUnitor_inv_hom X.object) }
  rightUnitor X :=
    { hom := ⟦MonoidalExpr.rightUnitor X.object⟧
      inv := ⟦MonoidalExpr.rightUnitorInv X.object⟧
      hom_inv_id := Quotient.sound (MonoidalDerives.rightUnitor_hom_inv X.object)
      inv_hom_id := Quotient.sound (MonoidalDerives.rightUnitor_inv_hom X.object) }

/-- The quotient operations satisfy all monoidal category laws. -/
instance monoidalCategory : MonoidalCategory (MonoidalTermModel signature) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      exact Quotient.sound (MonoidalDerives.tensor_id X.object Y.object))
    (id_tensorHom := by
      rintro X Y₁ Y₂ ⟨f⟩
      rfl)
    (tensorHom_id := by
      rintro X₁ X₂ ⟨f⟩ Y
      rfl)
    (tensorHom_comp_tensorHom := by
      rintro X₁ Y₁ Z₁ X₂ Y₂ Z₂ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
      exact Quotient.sound (MonoidalDerives.interchange f₁ f₂ g₁ g₂))
    (associator_naturality := by
      rintro X₁ X₂ X₃ Y₁ Y₂ Y₃ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
      exact Quotient.sound (MonoidalDerives.associator_naturality f₁ f₂ f₃))
    (leftUnitor_naturality := by
      rintro X Y ⟨f⟩
      exact Quotient.sound (MonoidalDerives.leftUnitor_naturality f))
    (rightUnitor_naturality := by
      rintro X Y ⟨f⟩
      exact Quotient.sound (MonoidalDerives.rightUnitor_naturality f))
    (pentagon := by
      intro W X Y Z
      exact Quotient.sound
        (MonoidalDerives.pentagon W.object X.object Y.object Z.object))
    (triangle := by
      intro X Y
      exact Quotient.sound (MonoidalDerives.triangle X.object Y.object))

/-- The quotient model carries the specified symmetric braiding. -/
instance symmetricCategory : SymmetricCategory (MonoidalTermModel signature) where
  braiding X Y :=
    { hom := ⟦MonoidalExpr.braid X.object Y.object⟧
      inv := ⟦MonoidalExpr.braid Y.object X.object⟧
      hom_inv_id := Quotient.sound (MonoidalDerives.braid_symmetry X.object Y.object)
      inv_hom_id := Quotient.sound (MonoidalDerives.braid_symmetry Y.object X.object) }
  braiding_naturality_right X := by
    rintro Y Z ⟨f⟩
    exact Quotient.sound (MonoidalDerives.braid_naturality_right X.object f)
  braiding_naturality_left := by
    rintro X Y ⟨f⟩ Z
    exact Quotient.sound (MonoidalDerives.braid_naturality_left f Z.object)
  hexagon_forward X Y Z :=
    Quotient.sound (MonoidalDerives.hexagon_forward X.object Y.object Z.object)
  hexagon_reverse X Y Z :=
    Quotient.sound (MonoidalDerives.hexagon_reverse X.object Y.object Z.object)
  symmetry X Y :=
    Quotient.sound (MonoidalDerives.braid_symmetry X.object Y.object)

/-- Evaluating free object syntax back into the free term model reconstructs
the original object tree. -/
@[simp]
theorem monoidalObjEval_self (X : signature.Obj) :
    monoidalObjEval (C := MonoidalTermModel signature)
      (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) X = ⟨X⟩ := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor X Y ihX ihY =>
      change
        { object :=
            (monoidalObjEval (C := MonoidalTermModel signature)
              (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) X).object.tensor
            (monoidalObjEval (C := MonoidalTermModel signature)
              (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) Y).object } =
          ({ object := X.tensor Y } : MonoidalTermModel signature)
      rw [ihX, ihY]

/-- Embed a raw monoidal expression into the hom type selected by recursive
object evaluation. -/
def quote {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    (⟨X⟩ : MonoidalTermModel signature) ⟶ ⟨Y⟩ :=
  Quotient.mk (monoidalDerivesSetoid signature X Y) expression

/-- Quotation preserves identity expressions exactly. -/
@[simp]
theorem quote_id (X : signature.Obj) :
    quote signature (.id X) = 𝟙 (⟨X⟩ : MonoidalTermModel signature) :=
  rfl

/-- Quotation preserves sequential composition exactly. -/
@[simp]
theorem quote_comp {X Y Z : signature.Obj}
    (f : MonoidalExpr signature X Y) (g : MonoidalExpr signature Y Z) :
    quote signature (.comp f g) = quote signature f ≫ quote signature g :=
  rfl

/-- Quotation preserves parallel composition exactly. -/
@[simp]
theorem quote_tensor {X₁ Y₁ X₂ Y₂ : signature.Obj}
    (f : MonoidalExpr signature X₁ Y₁) (g : MonoidalExpr signature X₂ Y₂) :
    quote signature (.tensor f g) = quote signature f ⊗ₘ quote signature g :=
  rfl

@[simp]
theorem quote_associator (X Y Z : signature.Obj) :
    quote signature (.associator X Y Z) =
      (α_ (⟨X⟩ : MonoidalTermModel signature) ⟨Y⟩ ⟨Z⟩).hom :=
  rfl

@[simp]
theorem quote_associatorInv (X Y Z : signature.Obj) :
    quote signature (.associatorInv X Y Z) =
      (α_ (⟨X⟩ : MonoidalTermModel signature) ⟨Y⟩ ⟨Z⟩).inv :=
  rfl

@[simp]
theorem quote_leftUnitor (X : signature.Obj) :
    quote signature (.leftUnitor X) =
      (λ_ (⟨X⟩ : MonoidalTermModel signature)).hom :=
  rfl

@[simp]
theorem quote_leftUnitorInv (X : signature.Obj) :
    quote signature (.leftUnitorInv X) =
      (λ_ (⟨X⟩ : MonoidalTermModel signature)).inv :=
  rfl

@[simp]
theorem quote_rightUnitor (X : signature.Obj) :
    quote signature (.rightUnitor X) =
      (ρ_ (⟨X⟩ : MonoidalTermModel signature)).hom :=
  rfl

@[simp]
theorem quote_rightUnitorInv (X : signature.Obj) :
    quote signature (.rightUnitorInv X) =
      (ρ_ (⟨X⟩ : MonoidalTermModel signature)).inv :=
  rfl

@[simp]
theorem quote_braid (X Y : signature.Obj) :
    quote signature (.braid X Y) =
      (β_ (⟨X⟩ : MonoidalTermModel signature) ⟨Y⟩).hom :=
  rfl

/-- Canonical comparison from recursively evaluated objects to wrapped syntax objects. -/
def comparison : (X : signature.Obj) →
    monoidalObjEval (C := MonoidalTermModel signature)
        (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) X ⟶ ⟨X⟩
  | .of _ => 𝟙 _
  | .unit => 𝟙 _
  | .tensor X Y => comparison X ⊗ₘ comparison Y

/-- Inverse canonical comparison for recursively evaluated objects. -/
def comparisonInv : (X : signature.Obj) →
    (⟨X⟩ : MonoidalTermModel signature) ⟶
      monoidalObjEval (C := MonoidalTermModel signature)
        (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) X
  | .of _ => 𝟙 _
  | .unit => 𝟙 _
  | .tensor X Y => comparisonInv X ⊗ₘ comparisonInv Y

@[simp, reassoc (attr := simp)]
theorem comparison_hom_inv (X : signature.Obj) :
    comparison signature X ≫ comparisonInv signature X = 𝟙 _ := by
  induction X with
  | of _ => simp [comparison, comparisonInv]
  | unit => simp [comparison, comparisonInv]
  | tensor X Y ihX ihY =>
      simp [comparison, comparisonInv, MonoidalCategory.tensorHom_comp_tensorHom,
        ihX, ihY]

@[simp, reassoc (attr := simp)]
theorem comparison_inv_hom (X : signature.Obj) :
    comparisonInv signature X ≫ comparison signature X = 𝟙 _ := by
  induction X with
  | of _ => simp [comparison, comparisonInv]
  | unit => simp [comparison, comparisonInv]
  | tensor X Y ihX ihY =>
      change
        (comparisonInv signature X ⊗ₘ comparisonInv signature Y) ≫
            (comparison signature X ⊗ₘ comparison signature Y) =
          𝟙 ((⟨X⟩ : MonoidalTermModel signature) ⊗ ⟨Y⟩)
      rw [MonoidalCategory.tensorHom_comp_tensorHom, ihX, ihY,
        MonoidalCategory.id_tensorHom_id]

/-- The canonical comparisons are natural with respect to associators. -/
theorem comparison_associator (X Y Z : signature.Obj) :
    comparison signature ((X ⊗ Y) ⊗ Z) ≫
        (α_ (⟨X⟩ : MonoidalTermModel signature) ⟨Y⟩ ⟨Z⟩).hom =
      (α_ (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)
        (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) Y)
        (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) Z)).hom ≫
        comparison signature (X ⊗ (Y ⊗ Z)) := by
  change
    ((comparison signature X ⊗ₘ comparison signature Y) ⊗ₘ comparison signature Z) ≫ _ =
      _ ≫ (comparison signature X ⊗ₘ
        (comparison signature Y ⊗ₘ comparison signature Z))
  exact MonoidalCategory.associator_naturality
    (comparison signature X) (comparison signature Y) (comparison signature Z)

theorem comparison_associatorInv (X Y Z : signature.Obj) :
    comparison signature (X ⊗ (Y ⊗ Z)) ≫
        (α_ (⟨X⟩ : MonoidalTermModel signature) ⟨Y⟩ ⟨Z⟩).inv =
      (α_ (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)
        (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) Y)
        (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) Z)).inv ≫
        comparison signature ((X ⊗ Y) ⊗ Z) := by
  change
    (comparison signature X ⊗ₘ
        (comparison signature Y ⊗ₘ comparison signature Z)) ≫ _ =
      _ ≫ ((comparison signature X ⊗ₘ comparison signature Y) ⊗ₘ
        comparison signature Z)
  exact MonoidalCategory.associator_inv_naturality
    (comparison signature X) (comparison signature Y) (comparison signature Z)

theorem comparison_leftUnitor (X : signature.Obj) :
    comparison signature (.unit ⊗ X) ≫
        (λ_ (⟨X⟩ : MonoidalTermModel signature)).hom =
      (λ_ (monoidalObjEval
        (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)).hom ≫
        comparison signature X := by
  change
    (𝟙 (𝟙_ (MonoidalTermModel signature)) ⊗ₘ comparison signature X) ≫ _ =
      _ ≫ comparison signature X
  simpa only [MonoidalCategory.id_tensorHom] using
    (MonoidalCategory.leftUnitor_naturality (comparison signature X))

theorem comparison_leftUnitorInv (X : signature.Obj) :
    comparison signature X ≫ (λ_ (⟨X⟩ : MonoidalTermModel signature)).inv =
      (λ_ (monoidalObjEval
        (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)).inv ≫
        comparison signature (.unit ⊗ X) := by
  change comparison signature X ≫ _ =
    _ ≫ (𝟙 (𝟙_ (MonoidalTermModel signature)) ⊗ₘ comparison signature X)
  simpa only [MonoidalCategory.id_tensorHom] using
    (MonoidalCategory.leftUnitor_inv_naturality (comparison signature X))

theorem comparison_rightUnitor (X : signature.Obj) :
    comparison signature (X ⊗ .unit) ≫
        (ρ_ (⟨X⟩ : MonoidalTermModel signature)).hom =
      (ρ_ (monoidalObjEval
        (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)).hom ≫
        comparison signature X := by
  change
    (comparison signature X ⊗ₘ 𝟙 (𝟙_ (MonoidalTermModel signature))) ≫ _ =
      _ ≫ comparison signature X
  simpa only [MonoidalCategory.tensorHom_id] using
    (MonoidalCategory.rightUnitor_naturality (comparison signature X))

theorem comparison_rightUnitorInv (X : signature.Obj) :
    comparison signature X ≫ (ρ_ (⟨X⟩ : MonoidalTermModel signature)).inv =
      (ρ_ (monoidalObjEval
        (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)).inv ≫
        comparison signature (X ⊗ .unit) := by
  change comparison signature X ≫ _ =
    _ ≫ (comparison signature X ⊗ₘ 𝟙 (𝟙_ (MonoidalTermModel signature)))
  simpa only [MonoidalCategory.tensorHom_id] using
    (MonoidalCategory.rightUnitor_inv_naturality (comparison signature X))

theorem comparison_braid (X Y : signature.Obj) :
    comparison signature (X ⊗ Y) ≫
        (β_ (⟨X⟩ : MonoidalTermModel signature) ⟨Y⟩).hom =
      (β_ (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X)
        (monoidalObjEval
          (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) Y)).hom ≫
        comparison signature (Y ⊗ X) := by
  change (comparison signature X ⊗ₘ comparison signature Y) ≫ _ =
    _ ≫ (comparison signature Y ⊗ₘ comparison signature X)
  exact BraidedCategory.braiding_naturality
    (comparison signature X) (comparison signature Y)

theorem comparison_hom_inv_cancel {W : MonoidalTermModel signature}
    {X : signature.Obj}
    (f : W ⟶ monoidalObjEval
      (fun w ↦ (⟨FreeMonoidalCategory.of w⟩ : MonoidalTermModel signature)) X) :
    (f ≫ comparison signature X) ≫ comparisonInv signature X = f := by
  rw [Category.assoc, comparison_hom_inv, Category.comp_id]

theorem comparison_inv_hom_chain {X : signature.Obj}
    {W : MonoidalTermModel signature} (f : (⟨X⟩ : MonoidalTermModel signature) ⟶ W) :
    comparisonInv signature X ≫ (comparison signature X ≫ f) = f := by
  rw [← Category.assoc, comparison_inv_hom, Category.id_comp]

theorem comparison_inv_hom_cancel {W : MonoidalTermModel signature}
    {X : signature.Obj} (f : W ⟶ (⟨X⟩ : MonoidalTermModel signature)) :
    (f ≫ comparisonInv signature X) ≫ comparison signature X = f := by
  rw [Category.assoc, comparison_inv_hom, Category.comp_id]

/-- Quote a raw expression at the recursively evaluated canonical object types. -/
def canonicalQuote {X Y : signature.Obj} (e : MonoidalExpr signature X Y) :
    monoidalObjEval (C := MonoidalTermModel signature)
        (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) X ⟶
      monoidalObjEval (C := MonoidalTermModel signature)
        (fun wire ↦ ⟨FreeMonoidalCategory.of wire⟩) Y :=
  comparison signature X ≫ quote signature e ≫ comparisonInv signature Y

@[simp]
theorem canonicalQuote_comp {X Y Z : signature.Obj}
    (f : MonoidalExpr signature X Y) (g : MonoidalExpr signature Y Z) :
    canonicalQuote signature f ≫ canonicalQuote signature g =
      canonicalQuote signature (.comp f g) := by
  unfold canonicalQuote
  rw [quote_comp]
  simp only [Category.assoc, comparison_inv_hom_chain]

/-- Canonical quotation is injective up to equality in the quotient hom type. -/
theorem canonicalQuote_injective {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y}
    (h : canonicalQuote signature f = canonicalQuote signature g) :
    quote signature f = quote signature g := by
  have cancelSource := congrArg (fun k ↦ comparisonInv signature X ≫ k) h
  have cancelTarget := congrArg (fun k ↦ k ≫ comparison signature Y) cancelSource
  simpa only [canonicalQuote, comparison_inv_hom_chain,
    comparison_inv_hom_cancel] using cancelTarget

variable [AddCommMonoid R] [Preorder R]

/-- Cost of a quotient morphism, well-defined because derivations preserve syntax cost. -/
def cost {X Y : MonoidalTermModel signature} (f : X ⟶ Y) : R :=
  Quotient.lift MonoidalExpr.syntaxCost
    (fun _ _ h ↦ MonoidalDerives.syntaxCost_eq h) f

/-- Sequential costs in the term model are represented exactly by syntax cost. -/
instance hasProcessCost : HasProcessCost (MonoidalTermModel signature) R where
  cost := cost signature
  cost_id _ := rfl
  cost_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    exact le_rfl

/-- Parallel costs in the term model are represented exactly by additive syntax cost. -/
instance hasParallelProcessCost : HasParallelProcessCost (MonoidalTermModel signature) R where
  cost_tensor := by
    rintro X₁ Y₁ X₂ Y₂ ⟨f⟩ ⟨g⟩
    exact le_rfl

/-- All structural morphisms have their declared zero cost in the term model. -/
instance hasFreeStructuralCost : HasFreeStructuralCost (MonoidalTermModel signature) R where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

/-- Term-model composition has exactly additive cost. -/
@[simp]
theorem cost_comp_exact {X Y Z : MonoidalTermModel signature}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    processCost (R := R) (f ≫ g) =
      processCost (R := R) f + processCost (R := R) g := by
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  rfl

/-- Term-model tensor products have exactly additive cost. -/
@[simp]
theorem cost_tensor_exact {X₁ Y₁ X₂ Y₂ : MonoidalTermModel signature}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    processCost (R := R) (f ⊗ₘ g) =
      processCost (R := R) f + processCost (R := R) g := by
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  rfl

/-- A quoted representative has exactly its computed syntax cost. -/
@[simp]
theorem cost_quote {X Y : signature.Obj} (e : MonoidalExpr signature X Y) :
    processCost (R := R) (quote signature e) = e.syntaxCost := by
  rfl

@[simp]
theorem cost_comparison (X : signature.Obj) :
    processCost (R := R) (comparison signature X) = 0 := by
  induction X with
  | of _ => simp [comparison]
  | unit => simp [comparison]
  | tensor X Y ihX ihY => simp [comparison, ihX, ihY]

@[simp]
theorem cost_comparisonInv (X : signature.Obj) :
    processCost (R := R) (comparisonInv signature X) = 0 := by
  induction X with
  | of _ => simp [comparisonInv]
  | unit => simp [comparisonInv]
  | tensor X Y ihX ihY => simp [comparisonInv, ihX, ihY]

/-- Canonical quotation preserves computed syntax cost exactly. -/
@[simp]
theorem cost_canonicalQuote {X Y : signature.Obj} (e : MonoidalExpr signature X Y) :
    processCost (R := R) (canonicalQuote signature e) = e.syntaxCost := by
  simp [canonicalQuote]

/-- Canonical interpretation of a signature in its symmetric monoidal term model. -/
def interpretation : MonoidalInterpretation signature (MonoidalTermModel signature) where
  wire X := ⟨FreeMonoidalCategory.of X⟩
  mapGen g := canonicalQuote signature (.gen g)
  mapGen_cost g := by
    rw [cost_canonicalQuote]
    exact le_rfl

/-- Evaluation in the canonical term model returns the derivation class of the expression. -/
theorem eval_interpretation {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    monoidalEval (interpretation signature) expression =
      canonicalQuote signature expression := by
  induction expression with
  | gen _ => rfl
  | id _ => simp [interpretation, canonicalQuote]
  | comp f g ihf ihg =>
      change monoidalEval (interpretation signature) f ≫
        monoidalEval (interpretation signature) g = _
      rw [ihf, ihg]
      exact canonicalQuote_comp signature f g
  | tensor f g ihf ihg =>
      change monoidalEval (interpretation signature) f ⊗ₘ
        monoidalEval (interpretation signature) g = _
      rw [ihf, ihg]
      simp [interpretation, canonicalQuote, comparison, comparisonInv,
        MonoidalCategory.tensorHom_comp_tensorHom]
  | associator X Y Z =>
      change (α_ _ _ _).hom = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_associator]
      symm
      rw [← Category.assoc]
      erw [comparison_associator]
      exact comparison_hom_inv_cancel signature _
  | associatorInv X Y Z =>
      change (α_ _ _ _).inv = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_associatorInv]
      symm
      rw [← Category.assoc]
      erw [comparison_associatorInv]
      exact comparison_hom_inv_cancel signature _
  | leftUnitor X =>
      change (λ_ _).hom = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_leftUnitor]
      symm
      rw [← Category.assoc]
      erw [comparison_leftUnitor]
      exact comparison_hom_inv_cancel signature _
  | leftUnitorInv X =>
      change (λ_ _).inv = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_leftUnitorInv]
      symm
      rw [← Category.assoc]
      erw [comparison_leftUnitorInv]
      exact comparison_hom_inv_cancel signature _
  | rightUnitor X =>
      change (ρ_ _).hom = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_rightUnitor]
      symm
      rw [← Category.assoc]
      erw [comparison_rightUnitor]
      exact comparison_hom_inv_cancel signature _
  | rightUnitorInv X =>
      change (ρ_ _).inv = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_rightUnitorInv]
      symm
      rw [← Category.assoc]
      erw [comparison_rightUnitorInv]
      exact comparison_hom_inv_cancel signature _
  | braid X Y =>
      change (β_ _ _).hom = _
      dsimp only [interpretation]
      unfold canonicalQuote
      rw [quote_braid]
      symm
      rw [← Category.assoc]
      erw [comparison_braid]
      exact comparison_hom_inv_cancel signature _

omit [Preorder R] in
/-- The quotient representative has exactly its computed monoidal syntax cost. -/
theorem cost_mk {X Y : MonoidalTermModel signature}
    (expression : MonoidalExpr signature X.object Y.object) :
    cost signature (Quotient.mk _ expression : X ⟶ Y) = expression.syntaxCost :=
  rfl

end MonoidalTermModel

end Ript.Semantics
