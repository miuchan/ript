import Ript.Examples.HigherLocalization
import Ript.Higher.CostExactZigzag

/-!
# A formal inverse word for the concrete noninvertible cost-exact embedding

The zero-cost discrete embedding from the one-object model to the natural-
number model is cost-exact but not a bicategorical equivalence.  The
cost-exact zigzag syntax now gives it an explicit one-step reverse word.  This
is concrete evidence that the higher-localization construction changes the
1-cell language rather than reusing the source bicategory unchanged.

The free-2-cell quotient now supplies an actual presented bicategory: the
formal reverse and its unit/counit local isomorphisms adjointify to a genuine
equivalence there. The example therefore proves that the new target really
inverts an arrow that was not an equivalence in the source. Proving the full
universal property of that target remains separate.
-/

set_option autoImplicit false

namespace Ript.Examples.CostExactFormalInverse

open CategoryTheory
open CategoryTheory.Bicategory
open Ript.Higher
open Ript.Examples.HigherLocalization

/-- The concrete zero-cost embedding belongs to the saturated bicategorical
cost-exact marking. -/
theorem unitToNat_costExact : costExactArrows Nat unitToNatModelHom :=
  costReflectingArrows_le_costExactArrows unitToNatModelHom (by
    change CostReflecting unitToNatModelHom
    infer_instance)

/-- The explicit formal reverse of the concrete zero-cost embedding. -/
def unitToNatFormalReverse :
    CostExactZigzag.Word
      (discreteZeroCostModel (Multiplicative Nat))
      (discreteZeroCostModel (Multiplicative PUnit.{1})) :=
  CostExactZigzag.backwardCostReflecting unitToNatModelHom (by
    change CostReflecting unitToNatModelHom
    infer_instance)

/-- The formal reverse is one oriented step. -/
@[simp]
theorem unitToNatFormalReverse_length :
    CostExactZigzag.length unitToNatFormalReverse = 1 :=
  rfl

/-- The forward word followed by its formal reverse is the two-step source
of the future unit cancellation 2-cell. -/
def unitCancellationWord :
    CostExactZigzag.Word
      (discreteZeroCostModel (Multiplicative PUnit.{1}))
      (discreteZeroCostModel (Multiplicative PUnit.{1})) :=
  CostExactZigzag.append
    (CostExactZigzag.forward unitToNatModelHom)
    unitToNatFormalReverse

/-- The unit-cancellation boundary has exactly the expected two steps. -/
@[simp]
theorem unitCancellationWord_length :
    CostExactZigzag.length unitCancellationWord = 2 := by
  simp [unitCancellationWord]

/-- The raw unit 2-cell generator attached to the concrete formal reverse. -/
def unitToNatRawUnit :
    CostExactZigzag.Cell
      (.nil (discreteZeroCostModel (Multiplicative PUnit.{1})))
      unitCancellationWord :=
  CostExactZigzag.unitCellCostReflecting unitToNatModelHom (by
    change CostReflecting unitToNatModelHom
    infer_instance)

/-- The reverse word followed by the original embedding, forming the source
of the raw counit generator. -/
def counitCancellationWord :
    CostExactZigzag.Word
      (discreteZeroCostModel (Multiplicative Nat))
      (discreteZeroCostModel (Multiplicative Nat)) :=
  CostExactZigzag.append unitToNatFormalReverse
    (CostExactZigzag.forward unitToNatModelHom)

/-- The raw counit 2-cell generator attached to the concrete formal reverse. -/
def unitToNatRawCounit :
    CostExactZigzag.Cell counitCancellationWord
      (.nil (discreteZeroCostModel (Multiplicative Nat))) :=
  CostExactZigzag.counitCellCostReflecting unitToNatModelHom (by
    change CostReflecting unitToNatModelHom
    infer_instance)

/-- Both two-dimensional cancellation generators now exist around the new
formal reverse, before imposing the localization quotient relations. -/
theorem rawCancellationGenerators_exist :
    Nonempty (CostExactZigzag.Cell
      (.nil (discreteZeroCostModel (Multiplicative PUnit.{1})))
      unitCancellationWord) ∧
      Nonempty (CostExactZigzag.Cell counitCancellationWord
        (.nil (discreteZeroCostModel (Multiplicative Nat)))) :=
  ⟨⟨unitToNatRawUnit⟩, ⟨unitToNatRawCounit⟩⟩

/-- The raw unit becomes an actual isomorphism in the quotient local
hom-category. -/
def unitToNatPresentedUnitIso :
    (CategoryTheory.Bicategory.MarkedZigzag.Word.nil
        (discreteZeroCostModel (Multiplicative PUnit.{1})) :
      CostExactZigzag.Word
        (discreteZeroCostModel (Multiplicative PUnit.{1}))
        (discreteZeroCostModel (Multiplicative PUnit.{1}))) ≅
      unitCancellationWord :=
  CostExactZigzag.markedUnitIso unitToNatModelHom (by
    exact costReflectingArrows_le_costExactArrows unitToNatModelHom (by
      change CostReflecting unitToNatModelHom
      infer_instance))

/-- The raw counit becomes an actual isomorphism in the quotient local
hom-category. -/
def unitToNatPresentedCounitIso :
    counitCancellationWord ≅
      (CategoryTheory.Bicategory.MarkedZigzag.Word.nil
        (discreteZeroCostModel (Multiplicative Nat)) :
      CostExactZigzag.Word
        (discreteZeroCostModel (Multiplicative Nat))
        (discreteZeroCostModel (Multiplicative Nat))) :=
  CostExactZigzag.markedCounitIso unitToNatModelHom (by
    exact costReflectingArrows_le_costExactArrows unitToNatModelHom (by
      change CostReflecting unitToNatModelHom
      infer_instance))

/-- The concrete formal reverse now has invertible unit and counit boundaries
inside genuine quotient local categories. The remaining adjoint-equivalence
obligation is precisely the two triangle relations of the future bicategory
presentation. -/
theorem presentedCancellationIsos_exist :
    Nonempty ((CategoryTheory.Bicategory.MarkedZigzag.Word.nil
        (discreteZeroCostModel (Multiplicative PUnit.{1})) :
      CostExactZigzag.Word
        (discreteZeroCostModel (Multiplicative PUnit.{1}))
        (discreteZeroCostModel (Multiplicative PUnit.{1}))) ≅
      unitCancellationWord) ∧
      Nonempty (counitCancellationWord ≅
        (CategoryTheory.Bicategory.MarkedZigzag.Word.nil
          (discreteZeroCostModel (Multiplicative Nat)) :
        CostExactZigzag.Word
          (discreteZeroCostModel (Multiplicative Nat))
          (discreteZeroCostModel (Multiplicative Nat)))) :=
  ⟨⟨unitToNatPresentedUnitIso⟩, ⟨unitToNatPresentedCounitIso⟩⟩

/-- The formal reverse, unit, and counit now package as a genuine adjoint
equivalence in the presented cost-exact zigzag bicategory. -/
noncomputable def unitToNatLocalizedEquivalence :
    (CategoryTheory.Bicategory.MarkedZigzag.Presented.Localization.mk
        (discreteZeroCostModel (Multiplicative PUnit.{1})) :
      CostExactZigzag.Localization (R := Nat)) ≌
      CategoryTheory.Bicategory.MarkedZigzag.Presented.Localization.mk
        (discreteZeroCostModel (Multiplicative Nat)) :=
  CostExactZigzag.markedEquivalence unitToNatModelHom unitToNat_costExact

/-- The presented target genuinely turns the previously non-equivalent source
arrow into an adjoint equivalence. -/
theorem inclusion_genuinely_inverts_unitToNat :
    (¬ IsEquivalence
        (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom) ∧
      IsEquivalence
        ((CostExactZigzag.inclusion (R := Nat)).map unitToNatModelHom) :=
  ⟨unitToNatModelHom_not_isEquivalence,
    CostExactZigzag.inclusion_inverts unitToNatModelHom unitToNat_costExact⟩

/-- A new reverse word now exists even though the original marked embedding
is provably not an adjoint equivalence in the source bicategory. -/
theorem formalReverse_exists_beyond_sourceEquivalence :
    (∃ reverse : CostExactZigzag.Word
        (discreteZeroCostModel (Multiplicative Nat))
        (discreteZeroCostModel (Multiplicative PUnit.{1})),
      CostExactZigzag.length reverse = 1) ∧
      ¬ IsEquivalence
        (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom :=
  ⟨⟨unitToNatFormalReverse, unitToNatFormalReverse_length⟩,
    unitToNatModelHom_not_isEquivalence⟩

end Ript.Examples.CostExactFormalInverse
