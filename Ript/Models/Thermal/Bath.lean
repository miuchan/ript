import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Ript.Models.Thermal.Work

/-!
# Finite bath-assisted thermal transitions

This module makes the external thermal bath explicit.  A
`BathAssistedTransition` evolves a product state of system, bath, and battery
through one Gibbs-preserving channel on the full finite composite.  The bath
and battery have separate exact endpoint states, so neither contribution is
silently discarded from the free-energy accounting.

The main theorem charges every system free-energy increase to the combined
free-energy decrease of bath and battery.  If the bath returns to exactly the
same state, its contribution vanishes.  If the battery is additionally
entropy-neutral, the remaining battery contribution is its mean-energy
decrease.  These are consequences of the supplied global process certificate;
the structure itself does not assert that an arbitrary requested transition
exists.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution

universe u

noncomputable section

/-- A Gibbs-preserving transition on an explicit finite system, bath, and
battery.  All endpoint states are independent products, while the process may
create correlations internally. -/
structure BathAssistedTransition
    (source target bath battery : GibbsThermalObject.{u}) where
  /-- The source system and bath have the same inverse temperature. -/
  sourceBathTemperature : source.gibbs.inverseTemperature =
    bath.gibbs.inverseTemperature
  /-- The target system and bath have the same inverse temperature. -/
  targetBathTemperature : target.gibbs.inverseTemperature =
    bath.gibbs.inverseTemperature
  /-- The source system+bath composite and battery have the same inverse
  temperature. -/
  sourceBatteryTemperature :
    (source.tensor bath sourceBathTemperature).gibbs.inverseTemperature =
    battery.gibbs.inverseTemperature
  /-- The target system+bath composite and battery have the same inverse
  temperature. -/
  targetBatteryTemperature :
    (target.tensor bath targetBathTemperature).gibbs.inverseTemperature =
    battery.gibbs.inverseTemperature
  /-- Exact initial state of the system. -/
  initialSystem : FinDist source.thermal.system
  /-- Exact final state of the system. -/
  finalSystem : FinDist target.thermal.system
  /-- Exact initial state of the bath. -/
  initialBath : FinDist bath.thermal.system
  /-- Exact final state of the bath. -/
  finalBath : FinDist bath.thermal.system
  /-- Exact initial state of the battery. -/
  initialBattery : FinDist battery.thermal.system
  /-- Exact final state of the battery. -/
  finalBattery : FinDist battery.thermal.system
  /-- Free global process on `(system × bath) × battery`. -/
  process : GibbsPreserving
    (((source.tensor bath sourceBathTemperature).tensor battery
      sourceBatteryTemperature).thermal)
    (((target.tensor bath targetBathTemperature).tensor battery
      targetBatteryTemperature).thermal)
  /-- The global process realizes the declared product-to-product endpoint
  transition. -/
  evolves :
    ((initialSystem.tensor initialBath).tensor initialBattery).push
        process.channel =
      (finalSystem.tensor finalBath).tensor finalBattery

namespace BathAssistedTransition

/-- Increase of the system's excess Helmholtz free energy. -/
def systemFreeEnergyIncrease
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery) : ℝ :=
  target.freeEnergyGap transition.finalSystem -
    source.freeEnergyGap transition.initialSystem

/-- Decrease of the bath's excess Helmholtz free energy. -/
def bathFreeEnergyDecrease
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery) : ℝ :=
  bath.freeEnergyGap transition.initialBath -
    bath.freeEnergyGap transition.finalBath

/-- Decrease of the battery's excess Helmholtz free energy. -/
def batteryFreeEnergyDecrease
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery) : ℝ :=
  battery.freeEnergyGap transition.initialBattery -
    battery.freeEnergyGap transition.finalBattery

/-- Decrease of the battery's mean energy.  It is interpreted as supplied
work only when the battery entropy is unchanged. -/
def batteryEnergyDecrease
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery) : ℝ :=
  battery.meanEnergy transition.initialBattery -
    battery.meanEnergy transition.finalBattery

/-- **Bath-resolved finite Landauer bound.** Every system free-energy increase
is paid by the combined free-energy decrease of the explicit bath and
battery. -/
theorem landauer_freeEnergy_bound
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery) :
    transition.systemFreeEnergyIncrease ≤
      transition.bathFreeEnergyDecrease +
        transition.batteryFreeEnergyDecrease := by
  have hmonotone :
      ((target.tensor bath transition.targetBathTemperature).tensor battery
          transition.targetBatteryTemperature).freeEnergyGap
          (((transition.initialSystem.tensor transition.initialBath).tensor
            transition.initialBattery).push transition.process.channel) ≤
        ((source.tensor bath transition.sourceBathTemperature).tensor battery
          transition.sourceBatteryTemperature).freeEnergyGap
          ((transition.initialSystem.tensor transition.initialBath).tensor
            transition.initialBattery) := by
    exact GibbsThermalObject.freeEnergyGap_monotone
      (X := (source.tensor bath transition.sourceBathTemperature).tensor
        battery transition.sourceBatteryTemperature)
      (Y := (target.tensor bath transition.targetBathTemperature).tensor
        battery transition.targetBatteryTemperature)
      (transition.targetBatteryTemperature.trans
        transition.sourceBatteryTemperature.symm)
      transition.process
      ((transition.initialSystem.tensor transition.initialBath).tensor
        transition.initialBattery)
  rw [transition.evolves] at hmonotone
  have hFinalOuter :
      ((target.tensor bath transition.targetBathTemperature).tensor battery
        transition.targetBatteryTemperature).freeEnergyGap
          ((transition.finalSystem.tensor transition.finalBath).tensor
            transition.finalBattery) =
        (target.tensor bath transition.targetBathTemperature).freeEnergyGap
            (transition.finalSystem.tensor transition.finalBath) +
          battery.freeEnergyGap transition.finalBattery := by
    simpa only [GibbsThermalObject.tensor] using
      (GibbsThermalObject.freeEnergyGap_tensor
      (target.tensor bath transition.targetBathTemperature) battery
      transition.targetBatteryTemperature
      (transition.finalSystem.tensor transition.finalBath)
      transition.finalBattery)
  have hFinalInner :
      (target.tensor bath transition.targetBathTemperature).freeEnergyGap
          (transition.finalSystem.tensor transition.finalBath) =
        target.freeEnergyGap transition.finalSystem +
          bath.freeEnergyGap transition.finalBath := by
    simpa only [GibbsThermalObject.tensor] using
      (GibbsThermalObject.freeEnergyGap_tensor target bath
        transition.targetBathTemperature transition.finalSystem
        transition.finalBath)
  have hInitialOuter :
      ((source.tensor bath transition.sourceBathTemperature).tensor battery
        transition.sourceBatteryTemperature).freeEnergyGap
          ((transition.initialSystem.tensor transition.initialBath).tensor
            transition.initialBattery) =
        (source.tensor bath transition.sourceBathTemperature).freeEnergyGap
            (transition.initialSystem.tensor transition.initialBath) +
          battery.freeEnergyGap transition.initialBattery := by
    simpa only [GibbsThermalObject.tensor] using
      (GibbsThermalObject.freeEnergyGap_tensor
      (source.tensor bath transition.sourceBathTemperature) battery
      transition.sourceBatteryTemperature
      (transition.initialSystem.tensor transition.initialBath)
      transition.initialBattery)
  have hInitialInner :
      (source.tensor bath transition.sourceBathTemperature).freeEnergyGap
          (transition.initialSystem.tensor transition.initialBath) =
        source.freeEnergyGap transition.initialSystem +
          bath.freeEnergyGap transition.initialBath := by
    simpa only [GibbsThermalObject.tensor] using
      (GibbsThermalObject.freeEnergyGap_tensor source bath
        transition.sourceBathTemperature transition.initialSystem
        transition.initialBath)
  rw [hFinalOuter, hFinalInner, hInitialOuter, hInitialInner] at hmonotone
  unfold systemFreeEnergyIncrease bathFreeEnergyDecrease
    batteryFreeEnergyDecrease
  linarith

/-- Exact bath return makes the bath free-energy contribution vanish. -/
theorem bathFreeEnergyDecrease_eq_zero_of_returns
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery)
    (hBath : transition.finalBath = transition.initialBath) :
    transition.bathFreeEnergyDecrease = 0 := by
  unfold bathFreeEnergyDecrease
  rw [hBath]
  ring

/-- If the explicit bath returns exactly, the battery alone pays the system's
free-energy increase. -/
theorem landauer_freeEnergy_bound_of_bath_returns
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery)
    (hBath : transition.finalBath = transition.initialBath) :
    transition.systemFreeEnergyIncrease ≤
      transition.batteryFreeEnergyDecrease := by
  have hbound := transition.landauer_freeEnergy_bound
  rw [transition.bathFreeEnergyDecrease_eq_zero_of_returns hBath,
    zero_add] at hbound
  exact hbound

/-- Entropy-neutral battery endpoints identify battery free-energy decrease
with mean-energy decrease. -/
theorem batteryFreeEnergyDecrease_eq_energyDecrease
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    transition.batteryFreeEnergyDecrease =
      transition.batteryEnergyDecrease := by
  unfold batteryFreeEnergyDecrease batteryEnergyDecrease
    GibbsThermalObject.freeEnergyGap
    GibbsThermalObject.nonequilibriumFreeEnergy
  rw [hEntropy]
  ring

/-- **Bath-assisted finite Landauer work bound.** When the bath returns exactly
and the battery entropy is unchanged, the system's free-energy increase is
bounded by the battery's supplied mean energy. -/
theorem landauer_work_bound_of_bath_returns
    {source target bath battery : GibbsThermalObject.{u}}
    (transition : BathAssistedTransition source target bath battery)
    (hBath : transition.finalBath = transition.initialBath)
    (hEntropy : battery.entropy transition.initialBattery =
      battery.entropy transition.finalBattery) :
    transition.systemFreeEnergyIncrease ≤
      transition.batteryEnergyDecrease := by
  calc
    transition.systemFreeEnergyIncrease ≤
        transition.batteryFreeEnergyDecrease :=
      transition.landauer_freeEnergy_bound_of_bath_returns hBath
    _ = transition.batteryEnergyDecrease :=
      transition.batteryFreeEnergyDecrease_eq_energyDecrease hEntropy

end BathAssistedTransition

end

end Ript.Models.Thermal
