import Ript.Univalent.Boundary
import Ript.Univalent.Process

/-!
# A nontrivial internally univalent process-interface example

This example interprets one atomic bit interface.  The codes `bit ⊗ unit` and
`unit ⊗ bit` are provably different syntax trees in Lean, but tensor symmetry
supplies an internal equivalence and hence an internal identity between them.
The identity transports a Boolean toggle between the two deterministic process
spaces and is observed identically by an invariant proposition.
-/

set_option autoImplicit false

namespace Ript.Examples.UnivalentProcessUniverse

open CategoryTheory
open Ript.Univalent

/-- The sole atomic process interface in the example. -/
inductive Atom where
  /-- A classical bit wire. -/
  | bit
  deriving DecidableEq, Repr

/-- Interpret the atomic bit wire as `Bool`. -/
def atomSemantics : Atom → Type
  | .bit => Bool

/-- The concrete small universe model. -/
def model : UniverseModel Atom :=
  ⟨atomSemantics⟩

/-- The atomic bit interface code. -/
abbrev bitCode : Code Atom := .atom .bit

/-- A bit tensored with the unit on the right. -/
abbrev bitTensorUnit : Code Atom := .tensor bitCode .unit

/-- A bit tensored with the unit on the left. -/
abbrev unitTensorBit : Code Atom := .tensor .unit bitCode

/-- The two tensor presentations remain different Lean syntax trees. -/
theorem bitTensorUnit_ne_unitTensorBit : bitTensorUnit ≠ unitTensorBit := by
  decide

/-- Tensor symmetry as a raw internal equivalence expression. -/
def swapExpr : EquivExpr bitTensorUnit unitTensorBit :=
  .tensorSwap bitCode .unit

/-- Tensor symmetry in the quotient type of internal equivalences. -/
def swapEquiv : model.InternalEquiv bitTensorUnit unitTensorBit :=
  UniverseModel.InternalEquiv.mk model swapExpr

/-- Internal univalence turns tensor symmetry into internal identity. -/
def swapIdentity : model.Identity bitTensorUnit unitTensorBit :=
  (UniverseModel.internalUnivalence model bitTensorUnit unitTensorBit).symm swapEquiv

/-- The internal identity has the expected set-level interpretation. -/
theorem swapIdentity_apply (bit : Bool) :
    UniverseModel.Identity.interpret model swapIdentity (bit, PUnit.unit) =
      (PUnit.unit, bit) :=
  rfl

/-- Boolean negation as a deterministic process on `bit ⊗ unit`. -/
def toggleRightUnit : model.FunctionProcess bitTensorUnit bitTensorUnit
  | (bit, _) => (!bit, PUnit.unit)

/-- Transport the process along the internally univalent tensor symmetry. -/
def toggleLeftUnit : model.FunctionProcess unitTensorBit unitTensorBit :=
  UniverseModel.functionProcessStructureIdentity model swapIdentity swapIdentity
    toggleRightUnit

/-- Transported negation acts on the same bit in the alternate presentation. -/
theorem toggleLeftUnit_false :
    toggleLeftUnit (PUnit.unit, false) = (PUnit.unit, true) :=
  rfl

/-- The primitive signature contains Boolean negation. -/
inductive Generator : Code Atom → Code Atom → Type where
  /-- Negate the atomic bit. -/
  | not : Generator bitCode bitCode

/-- Typed signature for the deep process example. -/
def signature : ProcessSignature Atom :=
  ⟨Generator⟩

/-- Interpret the primitive negation generator as `Bool.not`. -/
def processInterpretation : ProcessInterpretation signature model where
  generator
    | .not => Bool.not

/-- Deep syntax for primitive Boolean negation. -/
def notExpr : ProcessExpr signature bitCode bitCode :=
  .generator .not

/-- First reindex negation from `bit` to `bit ⊗ unit`. -/
def notRightUnitExpr : ProcessExpr signature bitTensorUnit bitTensorUnit :=
  .reindex (.symm (.tensorUnitRight bitCode))
    (.symm (.tensorUnitRight bitCode)) notExpr

/-- Then reindex it across tensor symmetry to `unit ⊗ bit`. -/
def notLeftUnitExpr : ProcessExpr signature unitTensorBit unitTensorBit :=
  .reindex swapExpr swapExpr notRightUnitExpr

/-- The deeply embedded and twice-reindexed process evaluates exactly. -/
theorem notLeftUnitExpr_false :
    notLeftUnitExpr.eval processInterpretation (PUnit.unit, false) =
      (PUnit.unit, true) :=
  rfl

#eval (notLeftUnitExpr.eval processInterpretation (PUnit.unit, false)).2

/-- The two successive reindexings agree semantically with reindexing by the
composite endpoint equivalence. -/
theorem reindex_not_sound :
    notLeftUnitExpr.eval processInterpretation =
      (ProcessExpr.reindex
        (.trans (.symm (.tensorUnitRight bitCode)) swapExpr)
        (.trans (.symm (.tensorUnitRight bitCode)) swapExpr)
        notExpr).eval processInterpretation :=
  ProcessDerives.soundness processInterpretation
    (.reindex_trans (.symm (.tensorUnitRight bitCode)) swapExpr
      (.symm (.tensorUnitRight bitCode)) swapExpr notExpr)

/-- Inhabitedness as an equivalence-invariant internal proposition. -/
def inhabitedPredicate : model.InternalPredicate where
  holds code := Nonempty (Code.denote model.atomSemantics code)
  respects equiv := by
    constructor
    · rintro ⟨value⟩
      exact ⟨UniverseModel.InternalEquiv.interpret model equiv value⟩
    · rintro ⟨value⟩
      exact ⟨(UniverseModel.InternalEquiv.interpret model equiv).symm value⟩

/-- The two externally distinct codes are indistinguishable by the invariant
inhabitedness proposition. -/
theorem swapIdentity_inhabited_iff :
    inhabitedPredicate.holds bitTensorUnit ↔
      inhabitedPredicate.holds unitTensorBit :=
  UniverseModel.InternalPredicate.identity_indistinguishable model
    inhabitedPredicate swapIdentity

/-- The first endpoint as an object of the interpreted groupoid. -/
def sourceObject : model.Object :=
  ⟨bitTensorUnit⟩

/-- The second endpoint as an object of the interpreted groupoid. -/
def targetObject : model.Object :=
  ⟨unitTensorBit⟩

/-- The univalent identity is a genuine morphism in the model groupoid. -/
def swapMorphism : sourceObject ⟶ targetObject :=
  swapIdentity

/-- The groupoid inverse of the swap composes back to identity. -/
theorem swapMorphism_inv_comp :
    Groupoid.inv swapMorphism ≫ swapMorphism = 𝟙 targetObject :=
  Groupoid.inv_comp swapMorphism

end Ript.Examples.UnivalentProcessUniverse
