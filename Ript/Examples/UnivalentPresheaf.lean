import Ript.Examples.UnivalentCompletion
import Ript.Univalent.Presheaf

/-!
# Yoneda evidence for the Boolean internal interface groupoid

This example sends the nontrivial tensor-symmetry identity from the Boolean
universe into the presheaf semantics.  Its natural transformation is evaluated
at the source identity and shown to recover the original internal path.  The
same path produces an isomorphism between the corresponding objects of the
Yoneda envelope, while the underlying raw interface codes remain provably
unequal.

The final `#eval` is only executable evidence for the already proved general
cardinality-invariance theorem; it is not used as a proof of Yoneda
faithfulness or of the categorical statements.
-/

set_option autoImplicit false

namespace Ript.Examples.UnivalentPresheaf

open CategoryTheory
open Ript.Univalent
open Ript.Examples.UnivalentCompletion
open Ript.Examples.UnivalentProcessUniverse

/-- The natural transformation of representables induced by Boolean tensor
symmetry. -/
def swapTransformation :
    UniverseModel.representablePresheaf model bitTensorUnit ⟶
      UniverseModel.representablePresheaf model unitTensorBit :=
  UniverseModel.representableTransformationEquiv model _ _ swapIdentity

/-- Evaluating the Yoneda image of tensor symmetry at the source identity
recovers the original internal identity. -/
theorem swapTransformation_component :
    swapTransformation.app
        (Opposite.op (⟨bitTensorUnit⟩ : model.Object))
        (UniverseModel.Identity.refl model bitTensorUnit) =
      swapIdentity := by
  change (𝟙 (⟨bitTensorUnit⟩ : model.Object)) ≫ swapIdentity = swapIdentity
  simp

/-- Full faithfulness recovers tensor symmetry from its natural
transformation without losing identity information. -/
theorem yonedaRecoversSwap :
    (UniverseModel.representableTransformationEquiv model _ _).symm
        swapTransformation =
      swapIdentity :=
  (UniverseModel.representableTransformationEquiv model _ _).symm_apply_apply
    swapIdentity

/-- The tensor-symmetry path as a natural isomorphism of representable
presheaves. -/
def swapNaturalIso :
    UniverseModel.representablePresheaf model bitTensorUnit ≅
      UniverseModel.representablePresheaf model unitTensorBit :=
  UniverseModel.representableNaturalIsoEquiv model _ _ swapIdentity

/-- The Yoneda-envelope object represented by `bit tensor unit`. -/
def bitTensorUnitEnvelope : model.YonedaEnvelope :=
  (UniverseModel.toYonedaEnvelope model).obj
    (⟨bitTensorUnit⟩ : model.Object)

/-- The Yoneda-envelope object represented by `unit tensor bit`. -/
def unitTensorBitEnvelope : model.YonedaEnvelope :=
  (UniverseModel.toYonedaEnvelope model).obj
    (⟨unitTensorBit⟩ : model.Object)

/-- Tensor symmetry induces an isomorphism between the two Yoneda-envelope
presentations. -/
def envelopeSwapIso : bitTensorUnitEnvelope ≅ unitTensorBitEnvelope :=
  (UniverseModel.toYonedaEnvelope model).mapIso
    ((Groupoid.isoEquivHom
      (⟨bitTensorUnit⟩ : model.Object)
      (⟨unitTensorBit⟩ : model.Object)).symm swapIdentity)

/-- Isomorphism in the representable-presheaf envelope coexists with strict
inequality of the original external code syntax. -/
theorem envelopeIsoDoesNotReflectCodeEquality :
    Nonempty (bitTensorUnitEnvelope ≅ unitTensorBitEnvelope) ∧
      bitTensorUnit ≠ unitTensorBit :=
  ⟨⟨envelopeSwapIso⟩, bitTensorUnit_ne_unitTensorBit⟩

/-- The general structural-invariance theorem proves that the two
tensor-symmetric presentations have equal finite cardinality. -/
theorem swap_preserves_cardinality :
    codeCardinality bitTensorUnit = codeCardinality unitTensorBit :=
  codeCardinality_equiv (.tensorSwap bitCode .unit)

#eval decide (codeCardinality bitTensorUnit = codeCardinality unitTensorBit)

end Ript.Examples.UnivalentPresheaf
