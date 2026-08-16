import Ript.Univalent.Soundness

/-!
# External/internal identity boundary

Lean equality of codes can always be reflected into the internal identity
type.  The converse is intentionally absent: internal identity is univalent
with respect to the deeply embedded structural equivalences, while Lean
equality continues to distinguish the syntax trees of codes.

Keeping this map one-way is the central trust-boundary rule of the Stage-11
layer.  In particular, this file declares no axiom and contains no operation
of type `Equiv α β → α = β`.
-/

set_option autoImplicit false

namespace Ript.Univalent

universe u

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)
variable {A B : Code Atom}

/-- Embed external Lean equality of codes into internal identity.  This uses
only equality elimination and internal reflexivity. -/
def equalityToIdentity (h : A = B) : M.Identity A B := by
  cases h
  exact Identity.refl M A

@[simp]
theorem equalityToIdentity_refl (A : Code Atom) :
    equalityToIdentity M (Eq.refl A) = Identity.refl M A :=
  rfl

/-- External equality maps to the reflexive internal equivalence after
eliminating the equality witness. -/
theorem idToEquiv_equalityToIdentity (h : A = B) :
    idToEquiv M (equalityToIdentity M h) = by
      cases h
      exact InternalEquiv.refl M A := by
  cases h
  apply InternalEquiv.eq_of_interpret_eq M
  rfl

end UniverseModel

end Ript.Univalent
