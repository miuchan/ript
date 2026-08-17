import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Ript.Higher.Localization
import Ript.Models.FiniteFunction.Monoidal

/-!
# A noninvertible 2-cell between process-model morphisms

The model bicategory genuinely has noninvertible 2-cells.  On the zero-cost
finite deterministic model, the cartesian discard maps form a monoidal natural
transformation from the identity model morphism to the constant-terminal model
morphism.  Its component on `Bool` is not invertible.

Consequently, the canonical pseudofunctor used before ordinary localization
must start from `Pith`: the homotopy category identifies 1-morphisms only along
invertible 2-cells, so it cannot map this 2-cell into a locally discrete target.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Examples.HigherNoninvertibleTwoCell

open CategoryTheory
open CategoryTheory.Limits
open Ript.Core
open Ript.Higher
open Ript.Models.FiniteFunction

/-- Zero cost for all finite deterministic processes makes every structural
map free as well. -/
theorem zeroStructuralCost : HasFreeStructuralCost FintypeCat.{0} Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

/-- Finite deterministic functions with the cartesian tensor and constantly
zero process cost, packaged as a process model. -/
def finiteZeroCostModel : ProcessModel.{1, 0, 0} Nat where
  Carrier := FintypeCat.{0}
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := zeroCost
  parallelCost := inferInstance
  structuralCost := zeroStructuralCost

/-- The endofunctor that sends every finite type to the chosen terminal
one-element finite type. -/
noncomputable def constantUnitFunctor : FintypeCat.{0} ⥤ FintypeCat.{0} :=
  (Functor.const FintypeCat.{0}).obj FintypeCartesian.unit

/-- The constant-terminal functor is lax braided.  All of its comparison maps
are the unique functions between one-element finite types. -/
noncomputable local instance constantUnitLaxBraided :
    constantUnitFunctor.LaxBraided where
  ε := FintypeCat.homMk fun _ ↦ PUnit.unit
  μ _ _ := FintypeCat.homMk fun _ ↦ PUnit.unit
  μ_natural_left _ _ := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl
  μ_natural_right _ _ := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl
  associativity _ _ _ := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl
  left_unitality _ := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl
  right_unitality _ := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl
  braided _ _ := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl

/-- The constant-terminal model morphism. -/
noncomputable def constantUnitModelHom :
    ModelHom finiteZeroCostModel finiteZeroCostModel where
  toLaxBraided :=
    { toFunctor := constantUnitFunctor
      laxBraided := constantUnitLaxBraided }
  unit_isIso := by
    change IsIso (Functor.LaxMonoidal.ε constantUnitFunctor)
    refine ⟨FintypeCat.homMk (fun _ ↦ PUnit.unit), ?_, ?_⟩
    · apply FintypeCat.hom_ext
      intro value
      cases value
      rfl
    · apply FintypeCat.hom_ext
      intro value
      cases value
      rfl
  tensor_isIso := by
    intro X Y
    change IsIso (Functor.LaxMonoidal.μ constantUnitFunctor X Y)
    refine ⟨FintypeCat.homMk (fun _ ↦ (PUnit.unit, PUnit.unit)), ?_, ?_⟩
    · apply FintypeCat.hom_ext
      intro value
      rcases value with ⟨⟨⟩, ⟨⟩⟩
      rfl
    · apply FintypeCat.hom_ext
      intro value
      cases value
      rfl
  map_cost_le _ := by
    change 0 ≤ 0
    exact le_rfl

/-- Cartesian discard gives a natural transformation from the identity
functor to the constant-terminal functor. -/
noncomputable def discardNatTrans :
    (ModelHom.id finiteZeroCostModel).toFunctor ⟶
      constantUnitModelHom.toFunctor where
  app _ := FintypeCat.homMk fun _ ↦ PUnit.unit
  naturality := by
    intro X Y f
    apply FintypeCat.hom_ext
    intro value
    rfl

noncomputable local instance discardNatTrans_isMonoidal :
    NatTrans.IsMonoidal discardNatTrans where
  unit := by
    apply FintypeCat.hom_ext
    intro value
    cases value
    rfl
  tensor _ _ := by
    apply FintypeCat.hom_ext
    intro value
    rfl

/-- The discard transformation as a 2-cell in the process-model bicategory. -/
noncomputable def discardTwoCell :
    ModelHom.id finiteZeroCostModel ⟶ constantUnitModelHom :=
  ModelTransformation.ofNatTrans discardNatTrans

/-- The identity and constant-terminal model morphisms are not related by any
invertible 2-cell: an isomorphism would make its `Bool` component injective
into a one-element type. -/
theorem identity_not_isomorphic_constant :
    ¬ Nonempty (ModelHom.id finiteZeroCostModel ≅ constantUnitModelHom) := by
  rintro ⟨i⟩
  let e := ModelTransformation.toNatIso i
  let d : FintypeCat.of Bool ⟶ FintypeCartesian.unit :=
    (e.app (FintypeCat.of Bool)).hom
  have hd : IsIso d := by
    dsimp [d]
    exact (e.app (FintypeCat.of Bool)).isIso_hom
  let _ : IsIso d := hd
  have hInjective := ConcreteCategory.bijective_of_isIso
    d |>.1
  have hEq : (true : Bool) = false := hInjective (Subsingleton.elim _ _)
  exact (by decide : (true : Bool) ≠ false) hEq

/-- The component of discard on `Bool` is not an isomorphism, so the model
2-cell itself is genuinely noninvertible. -/
theorem discardTwoCell_not_isIso : ¬ IsIso discardTwoCell := by
  intro h
  let _ : IsIso discardTwoCell := h
  exact identity_not_isomorphic_constant ⟨asIso discardTwoCell⟩

/-- The endpoints of the noninvertible 2-cell remain distinct in the
homotopy 1-category. -/
theorem homotopy_classes_ne :
    CategoryTheory.Bicategory.HomotopyCategory.homMk
        (B := ProcessModel.{1, 0, 0} Nat) (ModelHom.id finiteZeroCostModel) ≠
      CategoryTheory.Bicategory.HomotopyCategory.homMk constantUnitModelHom := by
  intro h
  exact identity_not_isomorphic_constant
    ((CategoryTheory.Bicategory.HomotopyCategory.homMk_eq_iff _ _).1 h)

end Ript.Examples.HigherNoninvertibleTwoCell
