import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Ript.ForMathlib.CategoryTheory.Bicategory.HomotopyCategory

/-!
# From the pith of a bicategory to its homotopy category

For a bicategory `B`, `Pith B` retains its objects and 1-morphisms but discards
all noninvertible 2-cells.  Its remaining 2-cells induce equalities of classes
in `HomotopyCategory B`, giving a canonical pseudofunctor to the locally
discrete bicategory on that ordinary category.

Factoring through `Pith` is essential.  A general noninvertible 2-cell does not
identify its source and target in the homotopy category, whose equivalence
relation is generated only by invertible 2-cells.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory

open CategoryTheory

universe u v w

namespace HomotopyCategory

variable (B : Type u) [Bicategory.{w, v} B]

/-- The canonical pseudofunctor from the maximal locally groupoidal part of a
bicategory to the locally discrete bicategory on its homotopy 1-category. -/
@[simps! obj map]
noncomputable def pithToHomotopy :
    Pith B ⥤ᵖ LocallyDiscrete (HomotopyCategory B) where
  obj X := LocallyDiscrete.mk (of X.as)
  map f := (homMk f.of).toLoc
  map₂ := fun {_ _} {f g} η ↦ eqToHom (by
      apply Discrete.ext
      exact (homMk_eq_iff f.of g.of).2 ⟨η.iso⟩)
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

end HomotopyCategory

end CategoryTheory.Bicategory
