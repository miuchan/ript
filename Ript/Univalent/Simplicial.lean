import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Ript.Univalent.Presheaf

/-!
# Simplicial nerve of the internal interface groupoid

This file adds genuine simplicial data to the internally univalent interface
model.  It takes the ordinary categorical nerve of `UniverseModel.Object` and
specializes Mathlib's strict Segal, quasicategory, 2-coskeletal, and homotopy-
category theorems to Ript's internal groupoid.

The low-dimensional semantics are exposed explicitly.

* Vertices are internal interface objects.
* Edges between chosen vertices are exactly internal identities, and therefore
  exactly internal structural equivalences.
* A composable pair of identities determines a 2-simplex whose three faces are
  the first edge, second edge, and their composite.
* Every edge has a groupoid inverse, and the corresponding 2-simplex has a
  degenerate composite face.
* Every `n`-simplex is uniquely reconstructed from its spine.

This is a strict 1-categorical nerve.  It is a simplicial set and a
quasicategory, but this file does not prove the Kan horn-filling condition,
construct a complete Segal space, localize a presheaf category, or identify
equivalent external Lean types.  In particular, it is not a Rezk completion.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory
open SSet
open Simplicial

universe u

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)
variable {A B C : Code Atom}

/-- The ordinary simplicial nerve of the internal interface groupoid. -/
abbrev InterfaceNerve : SSet.{u} :=
  CategoryTheory.nerve M.Object

/-- The internal interface nerve is strict Segal: every simplex is uniquely
determined by its composable spine of edges. -/
def interfaceNerveStrictSegal : SSet.StrictSegal M.InterfaceNerve :=
  CategoryTheory.Nerve.strictSegal M.Object

/-- The proposition-level strict Segal instance induced by the explicit
reconstruction data. -/
instance interfaceNerveIsStrictSegal : M.InterfaceNerve.IsStrictSegal :=
  (interfaceNerveStrictSegal M).isStrictSegal

/-- The internal interface nerve is a quasicategory because every strict Segal
simplicial set has unique inner horn fillers. -/
instance interfaceNerveQuasicategory : Quasicategory M.InterfaceNerve :=
  inferInstance

/-- The internal interface nerve is 2-coskeletal: all dimensions above two are
determined by its 2-truncation. -/
instance interfaceNerveTwoCoskeletal :
    SimplicialObject.IsCoskeletal M.InterfaceNerve 2 :=
  inferInstance

/-- Exact Segal equivalence between `n`-simplices and length-`n` composable
spines of edges. -/
def interfaceNerveSegalEquiv (n : ℕ) :
    M.InterfaceNerve _⦋n⦌ ≃ M.InterfaceNerve.Path n :=
  (interfaceNerveStrictSegal M).spineEquiv n

/-- Vertices of the internal nerve are exactly internal interface objects. -/
def interfaceNerveVertexEquiv :
    M.InterfaceNerve _⦋0⦌ ≃ M.Object :=
  CategoryTheory.nerveEquiv

/-- The vertex represented by a raw internal interface code. -/
def interfaceNerveVertex (A : Code Atom) : M.InterfaceNerve _⦋0⦌ :=
  (interfaceNerveVertexEquiv M).symm ⟨A⟩

/-- Edges between the vertices represented by `A` and `B` are exactly internal
identities from `A` to `B`. -/
def interfaceNerveEdgeEquiv (A B : Code Atom) :
    M.InterfaceNerve.Edge
        (interfaceNerveVertex M A) (interfaceNerveVertex M B) ≃
      M.Identity A B :=
  CategoryTheory.nerve.homEquiv

/-- By internal univalence, edges of the nerve are also exactly internal
structural equivalences. -/
def interfaceNerveEquivEdgeEquiv (A B : Code Atom) :
    M.InterfaceNerve.Edge
        (interfaceNerveVertex M A) (interfaceNerveVertex M B) ≃
      M.InternalEquiv A B :=
  (interfaceNerveEdgeEquiv M A B).trans (internalUnivalence M A B)

/-- Regard an internal identity as the corresponding edge in the simplicial
nerve. -/
def interfaceNerveIdentityEdge (path : M.Identity A B) :
    M.InterfaceNerve.Edge
      (interfaceNerveVertex M A) (interfaceNerveVertex M B) :=
  CategoryTheory.nerve.edgeMk path

/-- Decoding an edge constructed from an internal identity recovers that
identity exactly. -/
@[simp]
theorem interfaceNerveEdgeEquiv_identityEdge (path : M.Identity A B) :
    interfaceNerveEdgeEquiv M A B (interfaceNerveIdentityEdge M path) = path := by
  change CategoryTheory.nerve.homEquiv
    (CategoryTheory.nerve.edgeMk
      (C := M.Object) (x := (⟨A⟩ : M.Object)) (y := (⟨B⟩ : M.Object))
      (path : (⟨A⟩ : M.Object) ⟶ (⟨B⟩ : M.Object))) = path
  exact CategoryTheory.nerve.homEquiv_edgeMk
    (C := M.Object) (x := (⟨A⟩ : M.Object)) (y := (⟨B⟩ : M.Object))
    (path : (⟨A⟩ : M.Object) ⟶ (⟨B⟩ : M.Object))

/-- Internal reflexivity is the degenerate identity edge. -/
@[simp]
theorem interfaceNerveIdentityEdge_refl (A : Code Atom) :
    interfaceNerveIdentityEdge M (Identity.refl M A) =
      SSet.Edge.id (interfaceNerveVertex M A) := by
  change CategoryTheory.nerve.edgeMk
    (C := M.Object) (x := (⟨A⟩ : M.Object)) (y := (⟨A⟩ : M.Object))
    (𝟙 (⟨A⟩ : M.Object)) =
      SSet.Edge.id (X := CategoryTheory.nerve M.Object)
        (CategoryTheory.nerveEquiv.symm (⟨A⟩ : M.Object))
  exact CategoryTheory.nerve.edgeMk_id (⟨A⟩ : M.Object)

/-- Reverse a nerve edge using symmetry of the decoded internal identity. -/
def interfaceNerveInverseEdge
    (edge : M.InterfaceNerve.Edge
      (interfaceNerveVertex M A) (interfaceNerveVertex M B)) :
    M.InterfaceNerve.Edge
      (interfaceNerveVertex M B) (interfaceNerveVertex M A) :=
  interfaceNerveIdentityEdge M
    (Identity.symm M (interfaceNerveEdgeEquiv M A B edge))

/-- Decoding the inverse edge returns the symmetric internal identity. -/
@[simp]
theorem interfaceNerveEdgeEquiv_inverseEdge
    (edge : M.InterfaceNerve.Edge
      (interfaceNerveVertex M A) (interfaceNerveVertex M B)) :
    interfaceNerveEdgeEquiv M B A (interfaceNerveInverseEdge M edge) =
      Identity.symm M (interfaceNerveEdgeEquiv M A B edge) :=
  interfaceNerveEdgeEquiv_identityEdge M _

/-- The 2-simplex determined by two composable internal identities. -/
def interfaceNerveCompositionSimplex
    (first : M.Identity A B) (second : M.Identity B C) :
    M.InterfaceNerve _⦋2⦌ :=
  ComposableArrows.mk₂ first second

/-- The second face of the composition 2-simplex is its first edge. -/
@[simp]
theorem interfaceNerveComposition_first
    (first : M.Identity A B) (second : M.Identity B C) :
    M.InterfaceNerve.δ 2 (interfaceNerveCompositionSimplex M first second) =
      ComposableArrows.mk₁ first := by
  simpa [InterfaceNerve, interfaceNerveCompositionSimplex] using
    (CategoryTheory.nerve.δ₂_mk₂_eq (C := M.Object) first second)

/-- The zeroth face of the composition 2-simplex is its second edge. -/
@[simp]
theorem interfaceNerveComposition_second
    (first : M.Identity A B) (second : M.Identity B C) :
    M.InterfaceNerve.δ 0 (interfaceNerveCompositionSimplex M first second) =
      ComposableArrows.mk₁ second := by
  simpa [InterfaceNerve, interfaceNerveCompositionSimplex] using
    (CategoryTheory.nerve.δ₀_mk₂_eq (C := M.Object) first second)

/-- The middle face of the composition 2-simplex is path transitivity. -/
@[simp]
theorem interfaceNerveComposition_composite
    (first : M.Identity A B) (second : M.Identity B C) :
    M.InterfaceNerve.δ 1 (interfaceNerveCompositionSimplex M first second) =
      ComposableArrows.mk₁ (Identity.trans M first second) := by
  change (CategoryTheory.nerve M.Object).δ 1
    (ComposableArrows.mk₂ first second) =
      ComposableArrows.mk₁ (first ≫ second)
  exact CategoryTheory.nerve.δ₁_mk₂_eq
    (C := M.Object)
    (X₀ := (⟨A⟩ : M.Object)) (X₁ := (⟨B⟩ : M.Object))
    (X₂ := (⟨C⟩ : M.Object))
    (first : (⟨A⟩ : M.Object) ⟶ (⟨B⟩ : M.Object))
    (second : (⟨B⟩ : M.Object) ⟶ (⟨C⟩ : M.Object))

/-- The composition 2-simplex for an internal identity followed by its
groupoid inverse. -/
def interfaceNerveInverseCompositionSimplex (path : M.Identity A B) :
    M.InterfaceNerve _⦋2⦌ :=
  interfaceNerveCompositionSimplex M path (Identity.symm M path)

/-- The composite face of an identity and its inverse is the degenerate
reflexivity edge. -/
@[simp]
theorem interfaceNerveInverseComposition_composite (path : M.Identity A B) :
    M.InterfaceNerve.δ 1 (interfaceNerveInverseCompositionSimplex M path) =
      ComposableArrows.mk₁ (Identity.refl M A) := by
  rw [interfaceNerveInverseCompositionSimplex,
    interfaceNerveComposition_composite]
  apply congrArg ComposableArrows.mk₁
  apply Identity.eq_of_interpret_eq M
  simp

/-- The homotopy category of the internal nerve recovers the original
interface groupoid.  This is the counit isomorphism of Mathlib's homotopy-
category/nerve adjunction. -/
noncomputable def interfaceNerveHomotopyCategoryIso :
    SSet.hoFunctor.obj M.InterfaceNerve ≅ Cat.of M.Object :=
  CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of M.Object)

end UniverseModel

end Ript.Univalent
