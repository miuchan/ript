import Ript.Semantics.Eval
import Ript.Syntax.Derivation

/-!
# Soundness of sequential derivations

Every formal category-law derivation is respected by every cost-respecting
interpretation.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C R]
variable (interpretation : Interpretation signature C)

omit [ResourceAlgebra R] in
/-- Formal derivability implies equality in every interpretation. -/
theorem soundness {X Y : signature.Obj} {f g : Expr signature X Y}
    (derivation : Derives f g) : eval interpretation f = eval interpretation g := by
  induction derivation with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp_congr _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | id_comp _ => simp
  | comp_id _ => simp
  | assoc _ _ _ => simp

end Ript.Semantics
