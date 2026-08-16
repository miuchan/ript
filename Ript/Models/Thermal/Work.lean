import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Ript.Models.Thermal.FreeEnergy

/-!
# Work-assisted finite thermal transitions

This module states the finite Landauer accounting principle at the exact
boundary supported by Ript's thermal model.  A `WorkAssistedTransition`
records a Gibbs-preserving channel on a system and an explicit battery, with
independent exact product states at the two endpoints.  The channel may create
correlations during the process; only its certified endpoint equation is used.

Free-energy monotonicity and tensor additivity imply that any increase in the
system's excess Helmholtz free energy is paid for by a decrease in the
battery's excess free energy.  A separate entropy-neutrality hypothesis is
required before that battery free-energy decrease is identified with its mean
energy decrease and interpreted as supplied work.  Thus the work theorem does
not silently treat arbitrary nonequilibrium battery consumption as mechanical
work, and it does not assert existence of a transition that meets the bound.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

noncomputable section

/-- A Gibbs-preserving system+battery transition whose exact initial and final
states are independent products.  Source, target, and battery are all at one
common inverse temperature. -/
structure WorkAssistedTransition
    (source target battery : GibbsThermalObject.{u}) where
  /-- The source system and battery have the same inverse temperature. -/
  sourceTemperature : source.gibbs.inverseTemperature =
    battery.gibbs.inverseTemperature
  /-- The target system and battery have the same inverse temperature. -/
  targetTemperature : target.gibbs.inverseTemperature =
    battery.gibbs.inverseTemperature
  /-- Exact initial state of the system. -/
  initialSystem : FinDist source.thermal.system
  /-- Exact final state of the system. -/
  finalSystem : FinDist target.thermal.system
  /-- Exact initial state of the battery. -/
  initialBattery : FinDist battery.thermal.system
  /-- Exact final state of the battery. -/
  finalBattery : FinDist battery.thermal.system
  /-- Free joint process on system and battery. -/
  process : GibbsPreserving
    (source.tensor battery sourceTemperature).thermal
    (target.tensor battery targetTemperature).thermal
  /-- The free process realizes the declared product-to-product transition. -/
  evolves :
    (initialSystem.tensor initialBattery).push process.channel =
      finalSystem.tensor finalBattery

namespace WorkAssistedTransition

/-- Increase of the system's excess Helmholtz free energy. -/
def systemFreeEnergyIncrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery) : ℝ :=
  target.freeEnergyGap transition.finalSystem -
    source.freeEnergyGap transition.initialSystem

/-- Decrease of the battery's excess Helmholtz free energy. -/
def batteryFreeEnergyDecrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery) : ℝ :=
  battery.freeEnergyGap transition.initialBattery -
    battery.freeEnergyGap transition.finalBattery

/-- Decrease of the battery's mean energy.  This is identified with supplied
work only when the battery's entropy is unchanged. -/
def batteryEnergyDecrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery) : ℝ :=
  battery.meanEnergy transition.initialBattery -
    battery.meanEnergy transition.finalBattery

/-- **Finite Landauer free-energy bound.** A Gibbs-preserving joint transition
cannot increase the system's excess free energy by more than the battery's
excess free-energy decrease. -/
theorem landauer_freeEnergy_bound
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery) :
    transition.systemFreeEnergyIncrease ≤
      transition.batteryFreeEnergyDecrease := by
  have hmonotone :
      (target.tensor battery transition.targetTemperature).freeEnergyGap
          ((transition.initialSystem.tensor transition.initialBattery).push
            transition.process.channel) ≤
        (source.tensor battery transition.sourceTemperature).freeEnergyGap
          (transition.initialSystem.tensor transition.initialBattery) := by
    exact GibbsThermalObject.freeEnergyGap_monotone
      (X := source.tensor battery transition.sourceTemperature)
      (Y := target.tensor battery transition.targetTemperature)
      (transition.targetTemperature.trans transition.sourceTemperature.symm)
      transition.process
      (transition.initialSystem.tensor transition.initialBattery)
  rw [transition.evolves,
    GibbsThermalObject.freeEnergyGap_tensor target battery
      transition.targetTemperature transition.finalSystem
      transition.finalBattery,
    GibbsThermalObject.freeEnergyGap_tensor source battery
      transition.sourceTemperature transition.initialSystem
      transition.initialBattery] at hmonotone
  unfold systemFreeEnergyIncrease batteryFreeEnergyDecrease
  linarith

/-- If the battery entropy is unchanged, its excess-free-energy decrease is
exactly its mean-energy decrease. -/
theorem batteryFreeEnergyDecrease_eq_energyDecrease
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    transition.batteryFreeEnergyDecrease =
      transition.batteryEnergyDecrease := by
  unfold batteryFreeEnergyDecrease batteryEnergyDecrease
    GibbsThermalObject.freeEnergyGap
    GibbsThermalObject.nonequilibriumFreeEnergy
  rw [hEntropy]
  ring

/-- **Finite Landauer work bound.** For an entropy-neutral battery, the
system's free-energy increase is bounded by the mean energy supplied by the
battery. -/
theorem landauer_work_bound
    {source target battery : GibbsThermalObject.{u}}
    (transition : WorkAssistedTransition source target battery)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    transition.systemFreeEnergyIncrease ≤
      transition.batteryEnergyDecrease := by
  calc
    transition.systemFreeEnergyIncrease ≤
        transition.batteryFreeEnergyDecrease :=
      transition.landauer_freeEnergy_bound
    _ = transition.batteryEnergyDecrease :=
      transition.batteryFreeEnergyDecrease_eq_energyDecrease hEntropy

end WorkAssistedTransition

end

end Ript.Models.Thermal
