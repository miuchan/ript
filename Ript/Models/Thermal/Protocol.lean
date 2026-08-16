import Ript.Models.Thermal.GibbsPreserving

/-!
# Finite closed thermal protocols

A `FiniteClosedProtocol X` is an executable finite list of Gibbs-preserving
endomorphisms of one thermal object.  The list has two equivalent semantics:

* `run` evolves a state one step at a time;
* `process` composes all steps into one Gibbs-preserving channel.

The equivalence between these semantics is proved below.  In particular,
every finite closed protocol fixes the distinguished equilibrium state.  This
gives a reusable no-go theorem: a target distinct from equilibrium cannot be
reached from equilibrium without leaving the closed Gibbs-preserving model.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open CategoryTheory
open Ript.Models.FiniteDistribution

universe u

/-- A finite protocol whose every step is a Gibbs-preserving endomorphism of
the same thermal object.  Restricting to one object makes the word "closed"
precise: no explicit bath or work-storage system is introduced or discarded
between steps. -/
structure FiniteClosedProtocol (X : ThermalObject.{u}) where
  /-- The ordered list of protocol steps. -/
  steps : List (GibbsPreserving X X)

namespace FiniteClosedProtocol

variable {X : ThermalObject.{u}}

/-- Compose an ordered list of closed thermal steps. -/
def composeSteps (X : ThermalObject.{u}) :
    List (GibbsPreserving X X) → GibbsPreserving X X
  | [] => GibbsPreserving.identity X
  | step :: rest => GibbsPreserving.comp step (composeSteps X rest)

/-- Execute an ordered list of closed thermal steps on an exact state. -/
def runSteps (X : ThermalObject.{u}) :
    List (GibbsPreserving X X) → FinDist X.system → FinDist X.system
  | [], state => state
  | step :: rest, state => runSteps X rest (state.push step.channel)

/-- Record the initial state and every successive state of a protocol run. -/
def traceSteps (X : ThermalObject.{u}) :
    List (GibbsPreserving X X) → FinDist X.system → List (FinDist X.system)
  | [], state => [state]
  | step :: rest, state =>
      state :: traceSteps X rest (state.push step.channel)

/-- The single Gibbs-preserving process denoted by a finite protocol. -/
def process (protocol : FiniteClosedProtocol X) : GibbsPreserving X X :=
  composeSteps X protocol.steps

/-- Execute a finite protocol one step at a time. -/
def run (protocol : FiniteClosedProtocol X) (state : FinDist X.system) :
    FinDist X.system :=
  runSteps X protocol.steps state

/-- Return the complete finite state trajectory, including both endpoints. -/
def trace (protocol : FiniteClosedProtocol X) (state : FinDist X.system) :
    List (FinDist X.system) :=
  traceSteps X protocol.steps state

@[simp]
theorem composeSteps_nil (X : ThermalObject.{u}) :
    composeSteps X [] = GibbsPreserving.identity X :=
  rfl

@[simp]
theorem composeSteps_cons (step : GibbsPreserving X X)
    (rest : List (GibbsPreserving X X)) :
    composeSteps X (step :: rest) =
      GibbsPreserving.comp step (composeSteps X rest) :=
  rfl

@[simp]
theorem runSteps_nil (X : ThermalObject.{u}) (state : FinDist X.system) :
    runSteps X [] state = state :=
  rfl

@[simp]
theorem runSteps_cons (step : GibbsPreserving X X)
    (rest : List (GibbsPreserving X X)) (state : FinDist X.system) :
    runSteps X (step :: rest) state =
      runSteps X rest (state.push step.channel) :=
  rfl

/-- Stepwise execution agrees exactly with pushing through the composite
Gibbs-preserving process. -/
theorem runSteps_eq_push_composeSteps
    (steps : List (GibbsPreserving X X)) (state : FinDist X.system) :
    runSteps X steps state = state.push (composeSteps X steps).channel := by
  induction steps generalizing state with
  | nil =>
      exact (FinDist.push_identity state).symm
  | cons step rest ih =>
      rw [runSteps_cons, ih, composeSteps_cons,
        GibbsPreserving.comp_channel, FinDist.push_comp]

/-- Concatenating step lists agrees with serial composition of their denoted
thermal processes. -/
theorem composeSteps_append (first second : List (GibbsPreserving X X)) :
    composeSteps X (first ++ second) =
      GibbsPreserving.comp (composeSteps X first) (composeSteps X second) := by
  induction first with
  | nil =>
      simp only [List.nil_append, composeSteps_nil]
      change composeSteps X second =
        (𝟙 X : GibbsPreserving X X) ≫ composeSteps X second
      rw [Category.id_comp]
  | cons step rest ih =>
      rw [List.cons_append, composeSteps_cons, composeSteps_cons, ih]
      apply GibbsPreserving.ext
      apply Ript.Models.FiniteStochastic.FinStoch.ext
      intro input output
      simp only [GibbsPreserving.comp_channel,
        Ript.Models.FiniteStochastic.FinStoch.comp]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [mul_assoc]

/-- Run one closed protocol and then another on the same thermal object. -/
def andThen (first second : FiniteClosedProtocol X) : FiniteClosedProtocol X where
  steps := first.steps ++ second.steps

/-- Sequential protocol composition denotes serial process composition. -/
theorem process_andThen (first second : FiniteClosedProtocol X) :
    (first.andThen second).process =
      GibbsPreserving.comp first.process second.process :=
  composeSteps_append first.steps second.steps

/-- Protocol execution agrees with its single composite process. -/
theorem run_eq_push_process (protocol : FiniteClosedProtocol X)
    (state : FinDist X.system) :
    protocol.run state = state.push protocol.process.channel :=
  runSteps_eq_push_composeSteps protocol.steps state

/-- Sequential protocol composition executes its two components in order. -/
theorem run_andThen (first second : FiniteClosedProtocol X)
    (state : FinDist X.system) :
    (first.andThen second).run state = second.run (first.run state) := by
  rw [run_eq_push_process, process_andThen, GibbsPreserving.comp_channel,
    FinDist.push_comp, run_eq_push_process, run_eq_push_process]

/-- A trace contains exactly one more state than there are process steps. -/
theorem traceSteps_length (steps : List (GibbsPreserving X X))
    (state : FinDist X.system) :
    (traceSteps X steps state).length = steps.length + 1 := by
  induction steps generalizing state with
  | nil => rfl
  | cons step rest ih =>
      simp only [traceSteps, List.length_cons, List.length_cons]
      rw [ih]

/-- A protocol trace contains its initial state and one state per step. -/
theorem trace_length (protocol : FiniteClosedProtocol X)
    (state : FinDist X.system) :
    (protocol.trace state).length = protocol.steps.length + 1 :=
  traceSteps_length protocol.steps state

/-- A certified pair of mutually returning state transitions has the expected
three-state trace when packaged as a two-step closed protocol. -/
theorem trace_twoSteps (first second : GibbsPreserving X X)
    (initial middle : FinDist X.system)
    (hFirst : initial.push first.channel = middle)
    (hSecond : middle.push second.channel = initial) :
    ({ steps := [first, second] } : FiniteClosedProtocol X).trace initial =
      [initial, middle, initial] := by
  change initial :: (initial.push first.channel) ::
    ((initial.push first.channel).push second.channel) :: [] = _
  rw [hFirst, hSecond]

/-- A certified pair of mutually returning state transitions returns the
initial state when packaged as a two-step closed protocol. -/
theorem run_twoSteps (first second : GibbsPreserving X X)
    (initial middle : FinDist X.system)
    (hFirst : initial.push first.channel = middle)
    (hSecond : middle.push second.channel = initial) :
    ({ steps := [first, second] } : FiniteClosedProtocol X).run initial =
      initial := by
  change (initial.push first.channel).push second.channel = initial
  rw [hFirst, hSecond]

/-- Every finite closed thermal protocol fixes the distinguished equilibrium
state, regardless of the number or internal ordering of its steps. -/
theorem run_equilibrium (protocol : FiniteClosedProtocol X) :
    protocol.run X.equilibrium = X.equilibrium := by
  rw [run_eq_push_process]
  exact protocol.process.preserves_equilibrium

/-- Closed Gibbs-preserving protocols cannot take equilibrium to a distinct
target state.  Any such transition therefore requires a model with an
explicit external system, such as a bath or work-storage device. -/
theorem cannot_reach_from_equilibrium (target : FinDist X.system)
    (hTarget : target ≠ X.equilibrium) :
    ¬ ∃ protocol : FiniteClosedProtocol X,
      protocol.run X.equilibrium = target := by
  rintro ⟨protocol, hRun⟩
  apply hTarget
  rw [← hRun]
  exact protocol.run_equilibrium

end FiniteClosedProtocol

end Ript.Models.Thermal
