import Mathlib.Algebra.Group.Basic
import Ript.Syntax.MonoidalCost

/-!
# Equational derivations for symmetric monoidal syntax

The relation contains the category laws, tensor functoriality, monoidal
coherence, and symmetric braiding laws as explicit proof constructors.
-/

set_option autoImplicit false

namespace Ript.Syntax

universe u w

/-- Formal equality derivations for symmetric monoidal process expressions. -/
inductive MonoidalDerives {R : Type w} {signature : MonoidalSignature.{u, w} R} :
    {X Y : signature.Obj} →
      MonoidalExpr signature X Y → MonoidalExpr signature X Y → Prop where
  /-- Reflexivity. -/
  | refl {X Y : signature.Obj} (f : MonoidalExpr signature X Y) : MonoidalDerives f f
  /-- Symmetry of formal equality. -/
  | symm {X Y : signature.Obj} {f g : MonoidalExpr signature X Y} :
      MonoidalDerives f g → MonoidalDerives g f
  /-- Transitivity of formal equality. -/
  | trans {X Y : signature.Obj} {f g h : MonoidalExpr signature X Y} :
      MonoidalDerives f g → MonoidalDerives g h → MonoidalDerives f h
  /-- Sequential congruence. -/
  | comp_congr {X Y Z : signature.Obj}
      {f f' : MonoidalExpr signature X Y} {g g' : MonoidalExpr signature Y Z} :
      MonoidalDerives f f' → MonoidalDerives g g' →
        MonoidalDerives (.comp f g) (.comp f' g')
  /-- Tensor congruence. -/
  | tensor_congr {X₁ Y₁ X₂ Y₂ : signature.Obj}
      {f f' : MonoidalExpr signature X₁ Y₁}
      {g g' : MonoidalExpr signature X₂ Y₂} :
      MonoidalDerives f f' → MonoidalDerives g g' →
        MonoidalDerives (.tensor f g) (.tensor f' g')
  /-- Left identity law. -/
  | id_comp {X Y : signature.Obj} (f : MonoidalExpr signature X Y) :
      MonoidalDerives (.comp (.id X) f) f
  /-- Right identity law. -/
  | comp_id {X Y : signature.Obj} (f : MonoidalExpr signature X Y) :
      MonoidalDerives (.comp f (.id Y)) f
  /-- Associativity of sequential composition. -/
  | assoc {W X Y Z : signature.Obj} (f : MonoidalExpr signature W X)
      (g : MonoidalExpr signature X Y) (h : MonoidalExpr signature Y Z) :
      MonoidalDerives (.comp (.comp f g) h) (.comp f (.comp g h))
  /-- Tensor preserves identity morphisms. -/
  | tensor_id (X Y : signature.Obj) :
      MonoidalDerives (.tensor (.id X) (.id Y)) (.id (.tensor X Y))
  /-- Tensor satisfies the interchange law. -/
  | interchange {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : signature.Obj}
      (f₁ : MonoidalExpr signature X₁ Y₁) (f₂ : MonoidalExpr signature X₂ Y₂)
      (g₁ : MonoidalExpr signature Y₁ Z₁) (g₂ : MonoidalExpr signature Y₂ Z₂) :
      MonoidalDerives (.comp (.tensor f₁ f₂) (.tensor g₁ g₂))
        (.tensor (.comp f₁ g₁) (.comp f₂ g₂))
  /-- A forward associator followed by its inverse is an identity. -/
  | associator_hom_inv (X Y Z : signature.Obj) :
      MonoidalDerives (.comp (.associator X Y Z) (.associatorInv X Y Z))
        (.id (.tensor (.tensor X Y) Z))
  /-- An inverse associator followed by its forward map is an identity. -/
  | associator_inv_hom (X Y Z : signature.Obj) :
      MonoidalDerives (.comp (.associatorInv X Y Z) (.associator X Y Z))
        (.id (.tensor X (.tensor Y Z)))
  /-- A forward left unitor followed by its inverse is an identity. -/
  | leftUnitor_hom_inv (X : signature.Obj) :
      MonoidalDerives (.comp (.leftUnitor X) (.leftUnitorInv X))
        (.id (.tensor .unit X))
  /-- An inverse left unitor followed by its forward map is an identity. -/
  | leftUnitor_inv_hom (X : signature.Obj) :
      MonoidalDerives (.comp (.leftUnitorInv X) (.leftUnitor X)) (.id X)
  /-- A forward right unitor followed by its inverse is an identity. -/
  | rightUnitor_hom_inv (X : signature.Obj) :
      MonoidalDerives (.comp (.rightUnitor X) (.rightUnitorInv X))
        (.id (.tensor X .unit))
  /-- An inverse right unitor followed by its forward map is an identity. -/
  | rightUnitor_inv_hom (X : signature.Obj) :
      MonoidalDerives (.comp (.rightUnitorInv X) (.rightUnitor X)) (.id X)
  /-- Naturality of the associator. -/
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : signature.Obj}
      (f₁ : MonoidalExpr signature X₁ Y₁) (f₂ : MonoidalExpr signature X₂ Y₂)
      (f₃ : MonoidalExpr signature X₃ Y₃) :
      MonoidalDerives
        (.comp (.tensor (.tensor f₁ f₂) f₃) (.associator Y₁ Y₂ Y₃))
        (.comp (.associator X₁ X₂ X₃) (.tensor f₁ (.tensor f₂ f₃)))
  /-- Naturality of the left unitor. -/
  | leftUnitor_naturality {X Y : signature.Obj} (f : MonoidalExpr signature X Y) :
      MonoidalDerives (.comp (.tensor (.id .unit) f) (.leftUnitor Y))
        (.comp (.leftUnitor X) f)
  /-- Naturality of the right unitor. -/
  | rightUnitor_naturality {X Y : signature.Obj} (f : MonoidalExpr signature X Y) :
      MonoidalDerives (.comp (.tensor f (.id .unit)) (.rightUnitor Y))
        (.comp (.rightUnitor X) f)
  /-- Mac Lane's pentagon equation. -/
  | pentagon (W X Y Z : signature.Obj) :
      MonoidalDerives
        (.comp (.tensor (.associator W X Y) (.id Z))
          (.comp (.associator W (.tensor X Y) Z)
            (.tensor (.id W) (.associator X Y Z))))
        (.comp (.associator (.tensor W X) Y Z) (.associator W X (.tensor Y Z)))
  /-- Mac Lane's triangle equation. -/
  | triangle (X Y : signature.Obj) :
      MonoidalDerives
        (.comp (.associator X .unit Y) (.tensor (.id X) (.leftUnitor Y)))
        (.tensor (.rightUnitor X) (.id Y))
  /-- Symmetry is involutive. -/
  | braid_symmetry (X Y : signature.Obj) :
      MonoidalDerives (.comp (.braid X Y) (.braid Y X)) (.id (.tensor X Y))
  /-- Naturality of symmetry. -/
  | braid_naturality {X₁ Y₁ X₂ Y₂ : signature.Obj}
      (f : MonoidalExpr signature X₁ Y₁) (g : MonoidalExpr signature X₂ Y₂) :
      MonoidalDerives (.comp (.tensor f g) (.braid Y₁ Y₂))
        (.comp (.braid X₁ X₂) (.tensor g f))
  /-- Naturality of symmetry in its right argument. -/
  | braid_naturality_right (X : signature.Obj) {Y Z : signature.Obj}
      (f : MonoidalExpr signature Y Z) :
      MonoidalDerives (.comp (.tensor (.id X) f) (.braid X Z))
        (.comp (.braid X Y) (.tensor f (.id X)))
  /-- Naturality of symmetry in its left argument. -/
  | braid_naturality_left {X Y : signature.Obj}
      (f : MonoidalExpr signature X Y) (Z : signature.Obj) :
      MonoidalDerives (.comp (.tensor f (.id Z)) (.braid Y Z))
        (.comp (.braid X Z) (.tensor (.id Z) f))
  /-- Forward braided hexagon equation. -/
  | hexagon_forward (X Y Z : signature.Obj) :
      MonoidalDerives
        (.comp (.associator X Y Z)
          (.comp (.braid X (.tensor Y Z)) (.associator Y Z X)))
        (.comp (.tensor (.braid X Y) (.id Z))
          (.comp (.associator Y X Z) (.tensor (.id Y) (.braid X Z))))
  /-- Reverse braided hexagon equation. -/
  | hexagon_reverse (X Y Z : signature.Obj) :
      MonoidalDerives
        (.comp (.associatorInv X Y Z)
          (.comp (.braid (.tensor X Y) Z) (.associatorInv Z X Y)))
        (.comp (.tensor (.id X) (.braid Y Z))
          (.comp (.associatorInv X Z Y) (.tensor (.braid X Z) (.id Y))))

/-- The setoid of monoidal expressions modulo explicit symmetric monoidal derivations. -/
def monoidalDerivesSetoid {R : Type w} (signature : MonoidalSignature.{u, w} R)
    (X Y : signature.Obj) : Setoid (MonoidalExpr signature X Y) where
  r := MonoidalDerives
  iseqv := ⟨MonoidalDerives.refl, MonoidalDerives.symm, MonoidalDerives.trans⟩

namespace MonoidalDerives

variable {R : Type w} [AddCommMonoid R]
variable {signature : MonoidalSignature.{u, w} R} {X Y : signature.Obj}
variable {f g : MonoidalExpr signature X Y}

/-- Every symmetric monoidal derivation preserves computed syntax cost. -/
theorem syntaxCost_eq (derivation : MonoidalDerives f g) :
    f.syntaxCost = g.syntaxCost := by
  induction derivation <;>
    simp_all [MonoidalExpr.syntaxCost, add_assoc, add_comm, add_left_comm]

end MonoidalDerives

end Ript.Syntax
