import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic

/-!
# Optional process capabilities

The common Ript core deliberately does not assume that systems can be copied
or discarded.  This module adds the weakest coherent discarding capability
needed by causal models and bridges Mathlib's stronger
`CopyDiscardCategory` interface into it.  Classical copying itself remains
Mathlib's commutative-comonoid structure, so Ript does not duplicate its laws.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory
open MonoidalCategory
open ComonObj

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A process theory with a coherent choice of discarding map for every
system.  Unlike a copy-discard category, this capability does not imply that a
system can be copied. -/
class DiscardingProcess (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  /-- Discard the entire system. -/
  discard (X : C) : X ⟶ 𝟙_ C
  /-- Discarding a parallel system discards both components. -/
  discard_tensor (X Y : C) :
    discard (X ⊗ Y) =
      (discard X ⊗ₘ discard Y) ≫ (λ_ (𝟙_ C)).hom
  /-- Discarding the tensor unit is its identity. -/
  discard_unit : discard (𝟙_ C) = 𝟙 (𝟙_ C)

namespace DiscardingProcess

/-- Mathlib's stronger copy-discard capability supplies Ript's standalone
discarding capability by forgetting copy. -/
@[instance_reducible]
instance (priority := low) ofCopyDiscard [CopyDiscardCategory C] :
    DiscardingProcess C where
  discard X := ε[X]
  discard_tensor X Y := CopyDiscardCategory.discard_tensor X Y
  discard_unit := CopyDiscardCategory.discard_unit

end DiscardingProcess

/-- Ript's name for Mathlib's coherent classical copying capability.  The
alias exposes no new axioms or laws: a classical copying process theory is
exactly a `CopyDiscardCategory`. -/
abbrev ClassicalCopyingProcess (C : Type u) [Category.{v} C]
    [MonoidalCategory C] := CopyDiscardCategory C

/-- A process is causal when discarding its output is the same as discarding
its input immediately. -/
def CausalProcess [DiscardingProcess C] {X Y : C} (f : X ⟶ Y) : Prop :=
  f ≫ DiscardingProcess.discard Y = DiscardingProcess.discard X

namespace CausalProcess

variable [DiscardingProcess C]

/-- Identity processes are causal. -/
theorem id (X : C) : CausalProcess (𝟙 X) := by
  simp [CausalProcess]

/-- Serial composition of causal processes is causal. -/
theorem comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : CausalProcess f) (hg : CausalProcess g) : CausalProcess (f ≫ g) := by
  simp only [CausalProcess, Category.assoc]
  rw [hg, hf]

end CausalProcess

section CopyDiscard

variable [CopyDiscardCategory C]

/-- Every deterministic morphism in a copy-discard category is causal. -/
theorem causal_of_deterministic {X Y : C} (f : X ⟶ Y)
    [Deterministic f] : CausalProcess f := by
  change f ≫ ε[Y] = ε[X]
  exact Deterministic.discard_natural f

end CopyDiscard

end Ript.Core
