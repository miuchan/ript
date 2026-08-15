import Ript.Core.ParallelCost
import Ript.Resource.Basic

/-!
# Process simulation by post-processing

This module defines the qualitative and resource-bounded simulation relations
shared by information orders.  A process `f` simulates `g` when `g` is obtained
by post-processing the output of `f`.  The definition assumes only a category;
parallel compatibility and resource accounting are separate optional layers.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory
open MonoidalCategory
open Ript.Resource

universe u v w

section Qualitative

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}

/-- `f` simulates `g` when a post-processing channel turns `f` into `g`.
The two processes have the same input but may have different outputs. -/
def Simulates (f : W ⟶ X) (g : W ⟶ Y) : Prop :=
  ∃ postprocess : X ⟶ Y, f ≫ postprocess = g

namespace Simulates

/-- Every process simulates itself using identity post-processing. -/
theorem refl (f : W ⟶ X) : Simulates f f := by
  exact ⟨𝟙 X, Category.comp_id f⟩

/-- Simulation is transitive: post-processings compose. -/
theorem trans {f : W ⟶ X} {g : W ⟶ Y} {h : W ⟶ Z}
    (hfg : Simulates f g) (hgh : Simulates g h) : Simulates f h := by
  rcases hfg with ⟨k, hk⟩
  rcases hgh with ⟨l, hl⟩
  refine ⟨k ≫ l, ?_⟩
  calc
    f ≫ k ≫ l = (f ≫ k) ≫ l := by rw [Category.assoc]
    _ = g ≫ l := congrArg (fun q ↦ q ≫ l) hk
    _ = h := hl

/-- Every explicit post-processing produces a simulated process. -/
theorem postprocess (f : W ⟶ X) (k : X ⟶ Y) : Simulates f (f ≫ k) :=
  ⟨k, rfl⟩

/-- Precomposing both experiments preserves simulation. -/
theorem precomp {f : W ⟶ X} {g : W ⟶ Y} (hfg : Simulates f g)
    (e : Z ⟶ W) : Simulates (e ≫ f) (e ≫ g) := by
  rcases hfg with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [Category.assoc, hk]

/-- A simulated process can be post-processed further without recovering
information that the source did not already contain. -/
theorem postcomp {f : W ⟶ X} {g : W ⟶ Y} (hfg : Simulates f g)
    (l : Y ⟶ Z) : Simulates f (g ≫ l) :=
  hfg.trans (postprocess g l)

end Simulates

/-- Two processes are informationally equivalent when each can simulate the
other by post-processing. -/
def InformationEquivalent (f : W ⟶ X) (g : W ⟶ Y) : Prop :=
  Simulates f g ∧ Simulates g f

namespace InformationEquivalent

/-- Information equivalence is reflexive. -/
theorem refl (f : W ⟶ X) : InformationEquivalent f f :=
  ⟨Simulates.refl f, Simulates.refl f⟩

/-- Information equivalence is symmetric. -/
theorem symm {f : W ⟶ X} {g : W ⟶ Y}
    (h : InformationEquivalent f g) : InformationEquivalent g f :=
  ⟨h.2, h.1⟩

/-- Information equivalence is transitive. -/
theorem trans {f : W ⟶ X} {g : W ⟶ Y} {h : W ⟶ Z}
    (hfg : InformationEquivalent f g)
    (hgh : InformationEquivalent g h) : InformationEquivalent f h :=
  ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

end InformationEquivalent

section Tensor

variable [MonoidalCategory C]
variable {W₁ X₁ Y₁ W₂ X₂ Y₂ : C}

/-- Independent parallel composition preserves simulation in each component. -/
theorem Simulates.tensor {f₁ : W₁ ⟶ X₁} {g₁ : W₁ ⟶ Y₁}
    {f₂ : W₂ ⟶ X₂} {g₂ : W₂ ⟶ Y₂}
    (h₁ : Simulates f₁ g₁) (h₂ : Simulates f₂ g₂) :
    Simulates (f₁ ⊗ₘ f₂) (g₁ ⊗ₘ g₂) := by
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  refine ⟨k₁ ⊗ₘ k₂, ?_⟩
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hk₁, hk₂]

end Tensor

end Qualitative

section ResourceBounded

variable {C : Type u} [Category.{v} C]
variable {R : Type w} [AddCommMonoid R] [PartialOrder R]
variable [HasProcessCost C R]
variable {W X Y Z : C} {r s t : R}

/-- `f` simulates `g` within budget `r` when the required post-processing has
cost at most `r`. -/
def SimulatesWithin (r : R) (f : W ⟶ X) (g : W ⟶ Y) : Prop :=
  ∃ postprocess : X ⟶ Y,
    processCost (R := R) postprocess ≤ r ∧ f ≫ postprocess = g

namespace SimulatesWithin

/-- A resource-bounded simulation is also an ordinary simulation. -/
theorem simulates {f : W ⟶ X} {g : W ⟶ Y}
    (h : SimulatesWithin r f g) : Simulates f g := by
  rcases h with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

/-- Increasing a resource budget preserves feasibility. -/
theorem weaken {f : W ⟶ X} {g : W ⟶ Y}
    (h : SimulatesWithin r f g) (hrs : r ≤ s) : SimulatesWithin s f g := by
  rcases h with ⟨k, hk, hkg⟩
  exact ⟨k, hk.trans hrs, hkg⟩

/-- Every process simulates itself with zero post-processing budget. -/
theorem refl (f : W ⟶ X) : SimulatesWithin (0 : R) f f := by
  refine ⟨𝟙 X, ?_, Category.comp_id f⟩
  simp

/-- An explicit post-processing realizes a simulation at every budget that
bounds its cost. -/
theorem postprocess (f : W ⟶ X) (k : X ⟶ Y)
    (hk : processCost (R := R) k ≤ r) : SimulatesWithin r f (f ≫ k) :=
  ⟨k, hk, rfl⟩

/-- Precomposing both experiments preserves the post-processing budget. -/
theorem precomp {f : W ⟶ X} {g : W ⟶ Y}
    (h : SimulatesWithin r f g) (e : Z ⟶ W) :
    SimulatesWithin r (e ≫ f) (e ≫ g) := by
  rcases h with ⟨k, hk, hkg⟩
  refine ⟨k, hk, ?_⟩
  rw [Category.assoc, hkg]

/-- Resource budgets add when simulation post-processings are composed. -/
theorem trans {f : W ⟶ X} {g : W ⟶ Y} {h : W ⟶ Z}
    [ResourceAlgebra R]
    (hfg : SimulatesWithin r f g) (hgh : SimulatesWithin s g h) :
    SimulatesWithin (r + s) f h := by
  rcases hfg with ⟨k, hk, hkg⟩
  rcases hgh with ⟨l, hl, hlh⟩
  refine ⟨k ≫ l, ?_, ?_⟩
  · exact (processCost_comp k l).trans (add_le_add hk hl)
  · calc
      f ≫ k ≫ l = (f ≫ k) ≫ l := by rw [Category.assoc]
      _ = g ≫ l := congrArg (fun q ↦ q ≫ l) hkg
      _ = h := hlh

end SimulatesWithin

section Tensor

variable [ResourceAlgebra R] [MonoidalCategory C] [HasParallelProcessCost C R]
variable {W₁ X₁ Y₁ W₂ X₂ Y₂ : C}

/-- Parallel resource-bounded simulations compose with the sum of their
budgets. -/
theorem SimulatesWithin.tensor
    {f₁ : W₁ ⟶ X₁} {g₁ : W₁ ⟶ Y₁}
    {f₂ : W₂ ⟶ X₂} {g₂ : W₂ ⟶ Y₂}
    (h₁ : SimulatesWithin r f₁ g₁) (h₂ : SimulatesWithin s f₂ g₂) :
    SimulatesWithin (r + s) (f₁ ⊗ₘ f₂) (g₁ ⊗ₘ g₂) := by
  rcases h₁ with ⟨k₁, hk₁, hkg₁⟩
  rcases h₂ with ⟨k₂, hk₂, hkg₂⟩
  refine ⟨k₁ ⊗ₘ k₂, ?_, ?_⟩
  · exact (processCost_tensor k₁ k₂).trans (add_le_add hk₁ hk₂)
  · rw [MonoidalCategory.tensorHom_comp_tensorHom, hkg₁, hkg₂]

end Tensor

end ResourceBounded

end Ript.Core
