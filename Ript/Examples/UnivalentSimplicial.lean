import Ript.Examples.UnivalentPresheaf
import Ript.Univalent.Simplicial

/-!
# Simplicial evidence for the Boolean internal interface groupoid

This example realizes Boolean tensor symmetry as an edge of the internal
simplicial nerve.  Its inverse and their composition form an explicit
2-simplex whose outer faces are the two directions of tensor symmetry and
whose middle face is reflexivity.  The Segal equivalence reconstructs that
2-simplex exactly from its spine.

The example also keeps the external boundary visible: an edge connects the
two tensor presentations while their raw Lean code trees remain unequal.
-/

set_option autoImplicit false

namespace Ript.Examples.UnivalentSimplicial

open CategoryTheory
open Ript.Univalent
open Ript.Examples.UnivalentCompletion
open Ript.Examples.UnivalentProcessUniverse
open SSet
open Simplicial

/-- Boolean tensor symmetry as an edge of the internal interface nerve. -/
def swapEdge :
    model.InterfaceNerve.Edge
      (UniverseModel.interfaceNerveVertex model bitTensorUnit)
      (UniverseModel.interfaceNerveVertex model unitTensorBit) :=
  UniverseModel.interfaceNerveIdentityEdge model swapIdentity

/-- Decoding the simplicial edge recovers the original internal identity. -/
theorem swapEdge_decodes :
    UniverseModel.interfaceNerveEdgeEquiv model _ _ swapEdge = swapIdentity :=
  UniverseModel.interfaceNerveEdgeEquiv_identityEdge model swapIdentity

/-- Reading the same edge through internal univalence recovers the original
structural tensor equivalence. -/
theorem swapEdge_decodes_equiv :
    UniverseModel.interfaceNerveEquivEdgeEquiv model _ _ swapEdge = swapEquiv := by
  change UniverseModel.internalUnivalence model _ _
      (UniverseModel.interfaceNerveEdgeEquiv model _ _ swapEdge) = swapEquiv
  rw [swapEdge_decodes]
  exact (UniverseModel.internalUnivalence model _ _).apply_symm_apply swapEquiv

/-- The 2-simplex consisting of tensor symmetry followed by its inverse. -/
def swapCancellationSimplex : model.InterfaceNerve _⦋2⦌ :=
  UniverseModel.interfaceNerveInverseCompositionSimplex model swapIdentity

/-- The three faces of the cancellation 2-simplex are the forward symmetry,
its inverse, and reflexivity. -/
theorem swapCancellation_faces :
    model.InterfaceNerve.δ 2 swapCancellationSimplex =
        ComposableArrows.mk₁ swapIdentity ∧
      model.InterfaceNerve.δ 0 swapCancellationSimplex =
        ComposableArrows.mk₁ (UniverseModel.Identity.symm model swapIdentity) ∧
      model.InterfaceNerve.δ 1 swapCancellationSimplex =
        ComposableArrows.mk₁
          (UniverseModel.Identity.refl model bitTensorUnit) := by
  constructor
  · simpa [swapCancellationSimplex,
      UniverseModel.interfaceNerveInverseCompositionSimplex] using
      (UniverseModel.interfaceNerveComposition_first model swapIdentity
        (UniverseModel.Identity.symm model swapIdentity))
  constructor
  · simpa [swapCancellationSimplex,
      UniverseModel.interfaceNerveInverseCompositionSimplex] using
      (UniverseModel.interfaceNerveComposition_second model swapIdentity
        (UniverseModel.Identity.symm model swapIdentity))
  · simpa [swapCancellationSimplex] using
      (UniverseModel.interfaceNerveInverseComposition_composite model swapIdentity)

/-- Strict Segal reconstruction loses no information about the Boolean
cancellation 2-simplex. -/
theorem swapCancellation_segal_roundTrip :
    (UniverseModel.interfaceNerveSegalEquiv model 2).symm
        ((UniverseModel.interfaceNerveSegalEquiv model 2)
          swapCancellationSimplex) =
      swapCancellationSimplex :=
  (UniverseModel.interfaceNerveSegalEquiv model 2).symm_apply_apply _

/-- A simplicial edge between the two tensor presentations coexists with
strict inequality of their external code syntax. -/
theorem simplicialEdgeDoesNotReflectCodeEquality :
    Nonempty
        (model.InterfaceNerve.Edge
          (UniverseModel.interfaceNerveVertex model bitTensorUnit)
          (UniverseModel.interfaceNerveVertex model unitTensorBit)) ∧
      bitTensorUnit ≠ unitTensorBit :=
  ⟨⟨swapEdge⟩, bitTensorUnit_ne_unitTensorBit⟩

/-- The already proved invariant confirms that the connected presentations
still have the same finite semantic cardinality. -/
theorem swapEdge_preserves_cardinality :
    codeCardinality bitTensorUnit = codeCardinality unitTensorBit :=
  codeCardinality_equiv (.tensorSwap bitCode .unit)

#eval decide (codeCardinality bitTensorUnit = codeCardinality unitTensorBit)

end Ript.Examples.UnivalentSimplicial
