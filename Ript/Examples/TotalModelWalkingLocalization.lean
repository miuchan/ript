import Ript.Examples.ParallelBitHigherModels
import Ript.Examples.TwoDimensionalWalkingLocalization

/-!
# The walking localization in the total resource-model bicategory

The parameterized walking localization is quantified over arbitrary target
bicategories.  This file records the important heterogeneous-resource
specialization: its target may be `ResourceModel`, whose objects include the
probability, quantum, causal, computation, semantic-information, and thermal
models used by the six-model examples.

The premise remains essential.  A total-model-valued source diagram must
actually send the marked walking arrow to an adjoint equivalence.  The six
interpretation one-cells out of shared syntax are not asserted to be
equivalences merely to fit this theorem.
-/

set_option autoImplicit false

namespace Ript.Examples.TotalModelWalkingLocalization

open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
open Ript.Higher
open Ript.Examples.TwoDimensionalWalkingLocalization

universe u v w

/-- Extend a marking-inverting diagram of heterogeneous resource models
across the freely adjoined walking inverse. -/
noncomputable def lift
    (F : Source ⥤ᵖ ResourceModel.{u, v, w})
    (hF : marking.IsInvertedBy F) :
    Target ⥤ᵖ ResourceModel.{u, v, w} :=
  generalLiftPseudofunctor F hF

/-- The total-model lift restricts to a diagram adjoint equivalent to the
original marking-inverting source diagram. -/
noncomputable def restrictionEquivalence
    (F : Source ⥤ᵖ ResourceModel.{u, v, w})
    (hF : marking.IsInvertedBy F) :
    inclusion.comp (lift F hF) ≌ F :=
  generalLiftFactorization F hF

/-- Every marking-inverting total-model-valued source diagram factors through
the parameterized walking completion. -/
theorem factorsThrough
    (F : Source ⥤ᵖ ResourceModel.{u, v, w})
    (hF : marking.IsInvertedBy F) :
    inclusion.FactorsThrough F :=
  ⟨lift F hF, ⟨restrictionEquivalence F hF⟩⟩

/-- Precomposition recovers all strong transformations and modifications
between total-model-valued target diagrams. -/
theorem localPrecompositionIsEquivalence
    (F G : Target ⥤ᵖ ResourceModel.{u, v, w}) :
    (inclusion.localPrecomposition F G).IsEquivalence :=
  inclusion_localPrecomposition_isEquivalence F G

/-- The complete walking universal property specializes to the total
resource-model bicategory without any fixed-resource or local-thinness
assumption. -/
theorem universalProperty
    (F : Source ⥤ᵖ ResourceModel.{u, v, w})
    (hF : marking.IsInvertedBy F) :
    ∃ G : Target ⥤ᵖ ResourceModel.{u, v, w},
      Nonempty (inclusion.comp G ≌ F) :=
  inclusion_isBicategoricalLocalization.lift
    ResourceModel.{u, v, w} F hF

end Ript.Examples.TotalModelWalkingLocalization
