import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Ript.Higher.Localization
import Ript.Higher.TotalModelSimplicial
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

The same witness is now lifted to the total resource-model bicategory and
encoded in its full local mapping nerve. Exact decoding recovers the total
2-cell, and a separate theorem proves that it remains noninvertible. Thus the
simplicial mapping bridge retains data that the ordinary `Pith` bridge must
discard.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Examples.HigherNoninvertibleTwoCell

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open Ript.Core
open Ript.Higher
open Ript.Models.FiniteFunction

universe u v

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

/-! ## The same noninvertible 2-cell in the total-model mapping nerve -/

/-- Bundle the zero-cost deterministic model as an object of the total
resource-model bicategory. -/
def finiteZeroCostResourceModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := finiteZeroCostModel

/-- The constant-terminal morphism as a total-model 1-cell over the identity
resource translation. -/
noncomputable def totalConstantUnitModelHom :
    finiteZeroCostResourceModel ⟶ finiteZeroCostResourceModel where
  resourceMap := OrderAddMonoidHom.id Nat
  modelMap := ResourceChangeModelHom.ofModelHom constantUnitModelHom

/-- Cartesian discard as a 2-cell in the total resource-model bicategory. -/
noncomputable def totalDiscardTwoCell :
    ResourceModelHom.id finiteZeroCostResourceModel ⟶
      totalConstantUnitModelHom where
  resource_eq := rfl
  toNatTrans := discardNatTrans
  isMonoidal := discardNatTrans_isMonoidal

/-- The local mapping-nerve edge that retains the total discard 2-cell. -/
noncomputable def totalDiscardMappingEdge :=
  TotalModelSimplicial.mappingNerveTransformationEdge totalDiscardTwoCell

@[simp]
theorem totalDiscardMappingEdge_decodes :
    TotalModelSimplicial.mappingNerveEdgeEquiv
        (ResourceModelHom.id finiteZeroCostResourceModel)
        totalConstantUnitModelHom totalDiscardMappingEdge =
      totalDiscardTwoCell :=
  TotalModelSimplicial.mappingNerveEdgeEquiv_transformationEdge _

/-- Total-model packaging does not make discard invertible. -/
theorem totalDiscardTwoCell_not_isIso : ¬ IsIso totalDiscardTwoCell := by
  intro invertible
  let _ : IsIso totalDiscardTwoCell := invertible
  let inverse := inv totalDiscardTwoCell
  have homInv :
      totalDiscardTwoCell.toNatTrans ≫ inverse.toNatTrans =
        𝟙 (ResourceModelHom.id finiteZeroCostResourceModel).toFunctor := by
    have equality := congrArg ResourceModelTransformation.toNatTrans
      (IsIso.hom_inv_id totalDiscardTwoCell)
    simpa only [ResourceModelTransformation.comp_toNatTrans,
      ResourceModelTransformation.id_toNatTrans] using equality
  have invHom :
      inverse.toNatTrans ≫ totalDiscardTwoCell.toNatTrans =
        𝟙 totalConstantUnitModelHom.toFunctor := by
    have equality := congrArg ResourceModelTransformation.toNatTrans
      (IsIso.inv_hom_id totalDiscardTwoCell)
    simpa only [ResourceModelTransformation.comp_toNatTrans,
      ResourceModelTransformation.id_toNatTrans] using equality
  let equivalence :
      (ModelHom.id finiteZeroCostModel).toFunctor ≅
        constantUnitModelHom.toFunctor :=
    { hom := totalDiscardTwoCell.toNatTrans
      inv := inverse.toNatTrans
      hom_inv_id := homInv
      inv_hom_id := invHom }
  let component : FintypeCat.of Bool ⟶ FintypeCartesian.unit :=
    equivalence.hom.app (FintypeCat.of Bool)
  have componentIso : IsIso component := by
    dsimp [component]
    exact (equivalence.app (FintypeCat.of Bool)).isIso_hom
  let _ : IsIso component := componentIso
  have injective := ConcreteCategory.bijective_of_isIso component |>.1
  have equal : (true : Bool) = false := injective (Subsingleton.elim _ _)
  exact (by decide : (true : Bool) ≠ false) equal

/-- The simplicial mapping edge decodes to a genuinely noninvertible model
2-cell, so the local nerve has not silently groupoid-completed it. -/
theorem totalDiscardMappingEdge_decodes_noninvertible :
    ¬ IsIso
      (show ResourceModelHom.id finiteZeroCostResourceModel ⟶
          totalConstantUnitModelHom from
        TotalModelSimplicial.mappingNerveEdgeEquiv
          (ResourceModelHom.id finiteZeroCostResourceModel)
          totalConstantUnitModelHom totalDiscardMappingEdge) := by
  simpa using totalDiscardTwoCell_not_isIso

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

/-- Every pseudofunctor from the full process-model bicategory to a locally
discrete target identifies the two endpoints of discard.  This is the precise
2-dimensional obstruction hidden by the ordinary bridge: a locally discrete
target cannot retain the noninvertible discard 2-cell as nontrivial data. -/
theorem locallyDiscrete_map_identifies_discard
    {C : Type u} [Category.{v} C]
    (F : ProcessModel.{1, 0, 0} Nat ⥤ᵖ LocallyDiscrete C) :
    F.map (ModelHom.id finiteZeroCostModel) =
      F.map constantUnitModelHom :=
  LocallyDiscrete.eq_of_hom (F.map₂ discardTwoCell)

end Ript.Examples.HigherNoninvertibleTwoCell
