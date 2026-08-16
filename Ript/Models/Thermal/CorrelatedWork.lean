import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Ript.Models.Thermal.Correlation
import Ript.Models.Thermal.Work

/-!
# Work-assisted transitions with correlated endpoints

Unlike `WorkAssistedTransition`, this module does not require the system and
battery to be independent at either endpoint.  The declared initial and final
states are arbitrary exact joint distributions.  Their executable marginals
define the local system and battery states, while the entropy deficit of each
joint state records correlation free energy.

Joint free-energy monotonicity then gives the correlation-corrected Landauer
bound: system free-energy increase plus correlation free-energy increase is
paid by battery free-energy decrease.  Under an explicit entropy-neutrality
hypothesis on the battery marginals, the right side is its mean-energy
decrease.  No transition existence or saturation claim is made.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

noncomputable section

/-- A Gibbs-preserving system+battery transition with arbitrary exact joint
states at its endpoints.  Source, target, and battery share one inverse
temperature. -/
structure CorrelatedWorkAssistedTransition
    (source target battery : GibbsThermalObject.{u}) where
  /-- The source system and battery have the same inverse temperature. -/
  sourceTemperature : source.gibbs.inverseTemperature =
    battery.gibbs.inverseTemperature
  /-- The target system and battery have the same inverse temperature. -/
  targetTemperature : target.gibbs.inverseTemperature =
    battery.gibbs.inverseTemperature
  /-- Arbitrary exact initial joint state of system and battery. -/
  initialJoint : FinDist
    (Object.tensor source.thermal.system battery.thermal.system)
  /-- Arbitrary exact final joint state of system and battery. -/
  finalJoint : FinDist
    (Object.tensor target.thermal.system battery.thermal.system)
  /-- Free joint process on system and battery. -/
  process : GibbsPreserving
    (source.tensor battery sourceTemperature).thermal
    (target.tensor battery targetTemperature).thermal
  /-- The free process realizes the declared joint-state transition. -/
  evolves : initialJoint.push process.channel = finalJoint

namespace CorrelatedWorkAssistedTransition

/-- Initial system marginal of a correlated transition. -/
def initialSystem {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) :
    FinDist source.thermal.system :=
  transition.initialJoint.leftMarginal

/-- Final system marginal of a correlated transition. -/
def finalSystem {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) :
    FinDist target.thermal.system :=
  transition.finalJoint.leftMarginal

/-- Initial battery marginal of a correlated transition. -/
def initialBattery {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) :
    FinDist battery.thermal.system :=
  transition.initialJoint.rightMarginal

/-- Final battery marginal of a correlated transition. -/
def finalBattery {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) :
    FinDist battery.thermal.system :=
  transition.finalJoint.rightMarginal

/-- Increase of the system marginal's excess Helmholtz free energy. -/
def systemFreeEnergyIncrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) : ℝ :=
  target.freeEnergyGap transition.finalSystem -
    source.freeEnergyGap transition.initialSystem

/-- Decrease of the battery marginal's excess Helmholtz free energy. -/
def batteryFreeEnergyDecrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) : ℝ :=
  battery.freeEnergyGap transition.initialBattery -
    battery.freeEnergyGap transition.finalBattery

/-- Increase in system--battery correlation free energy between the two
endpoints.  It may be negative when correlations are consumed. -/
def correlationFreeEnergyIncrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) : ℝ :=
  target.correlationFreeEnergy battery transition.targetTemperature
      transition.finalJoint -
    source.correlationFreeEnergy battery transition.sourceTemperature
      transition.initialJoint

/-- Decrease of the battery marginal's mean energy.  It is interpreted as
supplied work only under entropy neutrality of the battery marginals. -/
def batteryEnergyDecrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) : ℝ :=
  battery.meanEnergy transition.initialBattery -
    battery.meanEnergy transition.finalBattery

/-- **Correlation-corrected finite Landauer bound.** For arbitrary joint
endpoint states, the battery free-energy decrease pays both the system
free-energy increase and any increase in correlation free energy. -/
theorem landauer_freeEnergy_bound
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery) :
    transition.systemFreeEnergyIncrease +
        transition.correlationFreeEnergyIncrease ≤
      transition.batteryFreeEnergyDecrease := by
  have hmonotone :
      (target.tensor battery transition.targetTemperature).freeEnergyGap
          (transition.initialJoint.push transition.process.channel) ≤
        (source.tensor battery transition.sourceTemperature).freeEnergyGap
          transition.initialJoint := by
    exact GibbsThermalObject.freeEnergyGap_monotone
      (X := source.tensor battery transition.sourceTemperature)
      (Y := target.tensor battery transition.targetTemperature)
      (transition.targetTemperature.trans transition.sourceTemperature.symm)
      transition.process transition.initialJoint
  rw [transition.evolves,
    GibbsThermalObject.freeEnergyGap_eq_marginals_add_correlation
      target battery transition.targetTemperature transition.finalJoint,
    GibbsThermalObject.freeEnergyGap_eq_marginals_add_correlation
      source battery transition.sourceTemperature transition.initialJoint]
      at hmonotone
  unfold systemFreeEnergyIncrease batteryFreeEnergyDecrease
    correlationFreeEnergyIncrease initialSystem finalSystem
    initialBattery finalBattery
  linarith

/-- If the battery marginals have equal entropy, their excess-free-energy
decrease is exactly their mean-energy decrease. -/
theorem batteryFreeEnergyDecrease_eq_energyDecrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    transition.batteryFreeEnergyDecrease =
      transition.batteryEnergyDecrease := by
  unfold initialBattery finalBattery at hEntropy
  unfold batteryFreeEnergyDecrease batteryEnergyDecrease
    initialBattery finalBattery GibbsThermalObject.freeEnergyGap
    GibbsThermalObject.nonequilibriumFreeEnergy
  rw [hEntropy]
  ring

/-- **Correlation-corrected finite Landauer work bound.** For an
entropy-neutral battery marginal, system and correlation free-energy gains
are bounded by the mean energy supplied by the battery. -/
theorem landauer_work_bound
    {source target battery : GibbsThermalObject.{u}}
    (transition : CorrelatedWorkAssistedTransition source target battery)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    transition.systemFreeEnergyIncrease +
        transition.correlationFreeEnergyIncrease ≤
      transition.batteryEnergyDecrease := by
  calc
    transition.systemFreeEnergyIncrease +
          transition.correlationFreeEnergyIncrease ≤
        transition.batteryFreeEnergyDecrease :=
      transition.landauer_freeEnergy_bound
    _ = transition.batteryEnergyDecrease :=
      transition.batteryFreeEnergyDecrease_eq_energyDecrease hEntropy

end CorrelatedWorkAssistedTransition

namespace WorkAssistedTransition

/-- Regard a product-endpoint transition as a correlated-endpoint transition.
The resulting endpoint correlation free energies are definitionally proved
zero by the tensor marginal and entropy laws. -/
def toCorrelated {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery) :
    CorrelatedWorkAssistedTransition source target battery where
  sourceTemperature := transition.sourceTemperature
  targetTemperature := transition.targetTemperature
  initialJoint := transition.initialSystem.tensor transition.initialBattery
  finalJoint := transition.finalSystem.tensor transition.finalBattery
  process := transition.process
  evolves := transition.evolves

/-- The correlation correction vanishes for a product-endpoint transition. -/
@[simp]
theorem toCorrelated_correlationFreeEnergyIncrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery) :
    transition.toCorrelated.correlationFreeEnergyIncrease = 0 := by
  simp [toCorrelated,
    CorrelatedWorkAssistedTransition.correlationFreeEnergyIncrease]

end WorkAssistedTransition

end

end Ript.Models.Thermal
