import Ript.Models.Decision.FiniteRisk

/-!
# Finite Blackwell decision separation

This module states the unresolved stochastic direction of the finite
Blackwell--Sherman--Stein theorem exactly and isolates its missing geometric
content.

`FiniteDecisionOrder P Q` says that `P` has no larger executable Bayes risk
than `Q` in every exact finite decision problem.  The already-proved forward
theorem shows that Blackwell dominance implies this order.

A `DecisionSeparationCertificate P Q` is concrete finite data: an action
carrier, a decision problem, and a deterministic rule for `Q` whose risk is
strictly below the optimal risk available from `P`.  Such a certificate
refutes both the universal decision order and every putative garbling.

The exact stochastic converse is recorded as the proposition
`FiniteBlackwellShermanStein`.  It is proved equivalent to completeness of
these certificates.  What remains is therefore a precise finite convex
separation problem, rather than an informal or weakened theorem claim.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.Separation

open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.FiniteStochastic

universe u

variable {Θ X Y : Object.{u}}

/-- Universal exact finite decision order: `P` is no worse than `Q` for every
finite action carrier, exact prior, and exact nonnegative-rational loss. -/
def FiniteDecisionOrder (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  ∀ (A : Object.{u}) (problem : DecisionProblem Θ A),
    finiteBayesRisk problem P ≤ finiteBayesRisk problem Q

/-- Concrete evidence separating `Q` from every decision rule based on `P`.
The supplied rule for `Q` need not be optimal; a strict advantage over the
optimal `P`-risk is already enough. -/
structure DecisionSeparationCertificate
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) where
  /-- Finite carrier of available actions. -/
  action : Object.{u}
  /-- Exact finite decision problem exposing the separation. -/
  problem : DecisionProblem Θ action
  /-- A concrete deterministic rule using observations from `Q`. -/
  decision : Y → action
  /-- The displayed `Q`-rule strictly beats every rule based on `P`. -/
  separates :
    deterministicDecisionRisk problem Q decision < finiteBayesRisk problem P

/-- The exact unresolved converse for a particular pair of finite stochastic
experiments. -/
def BlackwellShermanSteinConverse
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  FiniteDecisionOrder P Q → BlackwellDominates P Q

/-- The full universe-polymorphic exact finite
Blackwell--Sherman--Stein converse.  This is a proposition, not a theorem or an
assumed axiom. -/
def FiniteBlackwellShermanStein : Prop :=
  ∀ (Θ X Y : Object.{u}) (P : FinStoch Θ X) (Q : FinStoch Θ Y),
    BlackwellShermanSteinConverse P Q

/-- Completeness of concrete decision-separation certificates for a given
pair of experiments. -/
def DecisionSeparationComplete
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  ¬BlackwellDominates P Q →
    Nonempty (DecisionSeparationCertificate P Q)

/-- The proved forward Blackwell theorem supplies the universal finite
decision order. -/
theorem finiteDecisionOrder_of_dominates
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellDominates P Q) : FiniteDecisionOrder P Q := by
  intro A problem
  exact finiteBayesRisk_mono hPQ problem

/-- A concrete separation certificate refutes the universal finite decision
order. -/
theorem DecisionSeparationCertificate.not_finiteDecisionOrder
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (certificate : DecisionSeparationCertificate P Q) :
    ¬FiniteDecisionOrder P Q := by
  intro horder
  have hP_le_Q := horder certificate.action certificate.problem
  have hQ_le_decision :=
    finiteBayesRisk_le_deterministicDecisionRisk certificate.problem Q
      certificate.decision
  exact certificate.separates.not_ge (hP_le_Q.trans hQ_le_decision)

/-- A concrete decision separation certificate rules out every stochastic
post-processing witness from `P` to `Q`. -/
theorem DecisionSeparationCertificate.not_dominates
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (certificate : DecisionSeparationCertificate P Q) :
    ¬BlackwellDominates P Q := by
  intro hdominates
  exact certificate.not_finiteDecisionOrder
    (finiteDecisionOrder_of_dominates hdominates)

/-- Failure of the universal finite decision order is equivalent to existence
of a concrete finite separation certificate. -/
theorem not_finiteDecisionOrder_iff_certificate
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    ¬FiniteDecisionOrder P Q ↔
      Nonempty (DecisionSeparationCertificate P Q) := by
  classical
  constructor
  · intro horder
    rw [FiniteDecisionOrder] at horder
    push Not at horder
    obtain ⟨A, problem, hseparates⟩ := horder
    obtain ⟨decision, hdecision⟩ := exists_optimalDecision problem Q
    refine ⟨⟨A, problem, decision, ?_⟩⟩
    rw [hdecision]
    exact hseparates
  · rintro ⟨certificate⟩
    exact certificate.not_finiteDecisionOrder

/-- The stochastic Blackwell converse for `P` and `Q` is exactly completeness
of finite decision-separation certificates for that pair. -/
theorem blackwellShermanSteinConverse_iff_separationComplete
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    BlackwellShermanSteinConverse P Q ↔
      DecisionSeparationComplete P Q := by
  constructor
  · intro hconverse hnotDominates
    apply (not_finiteDecisionOrder_iff_certificate P Q).mp
    intro horder
    exact hnotDominates (hconverse horder)
  · intro hcomplete horder
    by_contra hnotDominates
    obtain ⟨certificate⟩ := hcomplete hnotDominates
    exact certificate.not_finiteDecisionOrder horder

/-- Assuming certificate completeness for one pair, Blackwell dominance and
the universal exact finite decision order coincide for that pair. -/
theorem dominates_iff_finiteDecisionOrder_of_separationComplete
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hcomplete : DecisionSeparationComplete P Q) :
    BlackwellDominates P Q ↔ FiniteDecisionOrder P Q := by
  constructor
  · exact finiteDecisionOrder_of_dominates
  · exact
      (blackwellShermanSteinConverse_iff_separationComplete P Q).mpr
        hcomplete

/-- The full exact finite stochastic converse is equivalent to uniform
completeness of concrete decision-separation certificates. -/
theorem finiteBlackwellShermanStein_iff_certificateComplete :
    FiniteBlackwellShermanStein.{u} ↔
      ∀ (Θ X Y : Object.{u}) (P : FinStoch Θ X) (Q : FinStoch Θ Y),
        DecisionSeparationComplete P Q := by
  constructor
  · intro hconverse Θ X Y P Q
    exact
      (blackwellShermanSteinConverse_iff_separationComplete P Q).mp
        (hconverse Θ X Y P Q)
  · intro hcomplete Θ X Y P Q
    exact
      (blackwellShermanSteinConverse_iff_separationComplete P Q).mpr
        (hcomplete Θ X Y P Q)

end Ript.Models.Decision.Separation
