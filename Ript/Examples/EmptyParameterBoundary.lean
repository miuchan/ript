import Ript.Models.Decision.Separation

/-!
# Empty hidden-state boundary for Blackwell comparison

This file records why the general finite Blackwell converse must require a
nonempty hidden-state carrier.  With no hidden states there is no normalized
prior and hence no decision problem, so the universal decision order is
vacuously true.  Nevertheless, a channel from a nonempty observation carrier
to an empty one cannot exist, so the corresponding Blackwell garbling fails.

The example is not a defect in finite decision theory.  It identifies the
precise nonemptiness condition under which the intended theorem is stated.
-/

set_option autoImplicit false

namespace Ript.Examples.EmptyParameterBoundary

open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.Separation
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

/-- Executable empty hidden-state and observation carrier. -/
abbrev emptyCarrier : Object :=
  Object.of Empty

/-- There is a unique stochastic experiment out of the empty carrier, since
its normalization obligation has no input rows. -/
def emptyExperiment (Z : Object) : FinStoch emptyCarrier Z where
  prob state := nomatch state
  normalized state := nomatch state

/-- Source experiment with one observation and no hidden states. -/
def unitObservationExperiment : FinStoch emptyCarrier Object.unit :=
  emptyExperiment Object.unit

/-- Target experiment with no observations and no hidden states. -/
def emptyObservationExperiment : FinStoch emptyCarrier emptyCarrier :=
  emptyExperiment emptyCarrier

/-- No garbling can map the nonempty unit observation carrier to the empty
target observation carrier. -/
theorem unit_not_dominates_empty :
    ¬BlackwellDominates unitObservationExperiment emptyObservationExperiment := by
  rintro ⟨garbling, _⟩
  obtain ⟨state⟩ :=
    (channelToKleisli garbling PUnit.unit).carrier_nonempty
  exact state.elim

/-- With an empty hidden-state carrier, the universal decision comparison is
vacuously true because an exact normalized prior on `Empty` cannot exist. -/
theorem vacuous_finiteDecisionOrder :
    FiniteDecisionOrder unitObservationExperiment emptyObservationExperiment := by
  intro _ problem
  obtain ⟨state⟩ := problem.prior.carrier_nonempty
  exact state.elim

/-- The pairwise converse is false without the nonempty-hidden-state
hypothesis used by `FiniteBlackwellShermanStein`. -/
theorem converse_fails_without_nonempty :
    ¬BlackwellShermanSteinConverse
      unitObservationExperiment emptyObservationExperiment := by
  intro hconverse
  exact unit_not_dominates_empty
    (hconverse vacuous_finiteDecisionOrder)

end Ript.Examples.EmptyParameterBoundary
