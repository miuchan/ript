import Ript.Univalent.Simplicial

/-!
# The Rezk classifying diagram of the internal interface groupoid

The ordinary nerve in `Ript.Univalent.Simplicial` remembers objects, arrows,
and strict composition, but it is only a simplicial *set*.  Rezk's
classifying-diagram construction retains a second simplicial direction: in
outer degree `n`, it takes the nerve of the category of functors
`Fin (n + 1) ⥤ M.Object` and natural transformations between them.

For the internal interface model, `M.Object` is a groupoid.  Consequently
every natural transformation in every outer degree is pointwise invertible,
so every vertical simplicial set is the nerve of a groupoid and is therefore
a Kan complex.

This file constructs that genuine two-dimensional object and proves its
levelwise groupoidal/Kan structure.  It also identifies its vertical vertices
with the ordinary interface nerve and its vertical edges with invertible
natural transformations.  It does not yet package or prove the outer Segal
and Rezk completeness equivalences; those remain the next completion step.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory
open Opposite
open Simplicial
open SSet

universe u

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)

/-- The category-valued outer simplicial direction of the interface
classifying diagram.  Its outer `n`-simplices are composable `n`-strings in
the internal interface groupoid, and its morphisms are natural
transformations between those strings. -/
def interfaceClassifyingDiagramCat : SimplicialObject Cat where
  obj Δ := Cat.of (ComposableArrows M.Object (Δ.unop.len))
  map f := (ComposableArrows.whiskerLeftFunctor
    (SimplexCategory.toCat.map f.unop).toFunctor).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Rezk classifying diagram of the internal interface groupoid, as a
simplicial object in simplicial sets.  No completeness claim is built into
this definition. -/
def InterfaceClassifyingDiagram : SimplicialObject SSet :=
  interfaceClassifyingDiagramCat M ⋙ CategoryTheory.nerveFunctor

/-- The outer category at a simplex `Δ` is definitionally the category of
`Δ`-shaped composable arrows. -/
@[simp]
theorem interfaceClassifyingDiagramCat_obj (Δ : SimplexCategoryᵒᵖ) :
    (interfaceClassifyingDiagramCat M).obj Δ =
      Cat.of (ComposableArrows M.Object (Δ.unop.len)) :=
  rfl

/-- Every natural transformation between composable strings of internal
interfaces is an isomorphism, because each component lies in the internal
interface groupoid. -/
instance interfaceComposableArrowsIsGroupoid (n : ℕ) :
    IsGroupoid (ComposableArrows M.Object n) where
  all_isIso η := by
    exact NatIso.isIso_of_isIso_app η

/-- The groupoid structure on each category of composable interface arrows. -/
noncomputable instance interfaceComposableArrowsGroupoid (n : ℕ) :
    Groupoid (ComposableArrows M.Object n) :=
  Groupoid.ofIsGroupoid

/-- Every outer level is strict Segal in its vertical simplicial direction. -/
def interfaceClassifyingDiagramLevelStrictSegal
    (Δ : SimplexCategoryᵒᵖ) :
    SSet.StrictSegal ((InterfaceClassifyingDiagram M).obj Δ) := by
  change SSet.StrictSegal (CategoryTheory.nerve
    (ComposableArrows M.Object (Δ.unop.len)))
  exact CategoryTheory.Nerve.strictSegal
    (ComposableArrows M.Object (Δ.unop.len))

/-- Proposition-level strict-Segal instance for every vertical level. -/
instance interfaceClassifyingDiagramLevelIsStrictSegal
    (Δ : SimplexCategoryᵒᵖ) :
    ((InterfaceClassifyingDiagram M).obj Δ).IsStrictSegal :=
  (interfaceClassifyingDiagramLevelStrictSegal M Δ).isStrictSegal

/-- Every outer level of the classifying diagram is a Kan complex in its
vertical simplicial direction. -/
instance interfaceClassifyingDiagramLevelKan
    (Δ : SimplexCategoryᵒᵖ) :
    KanComplex ((InterfaceClassifyingDiagram M).obj Δ) := by
  change KanComplex (CategoryTheory.nerve
    (ComposableArrows M.Object (Δ.unop.len)))
  exact CategoryTheory.Nerve.kanComplex
    (ComposableArrows M.Object (Δ.unop.len))

/-- Every vertical level is, in particular, a quasicategory. -/
instance interfaceClassifyingDiagramLevelQuasicategory
    (Δ : SimplexCategoryᵒᵖ) :
    Quasicategory ((InterfaceClassifyingDiagram M).obj Δ) :=
  inferInstance

/-- Every vertical level is 2-coskeletal, as the nerve of an ordinary
category. -/
instance interfaceClassifyingDiagramLevelTwoCoskeletal
    (Δ : SimplexCategoryᵒᵖ) :
    SimplicialObject.IsCoskeletal ((InterfaceClassifyingDiagram M).obj Δ) 2 :=
  inferInstance

/-- The outer simplicial set obtained by taking vertical vertices of the
classifying diagram. -/
def InterfaceClassifyingDiagramVerticalVertices : SSet :=
  InterfaceClassifyingDiagram M ⋙ SSet.evaluation.obj (op ⦋0⦌)

/-- Taking vertical vertices of the classifying diagram recovers the ordinary
interface nerve naturally in every outer degree.  This is stronger than a
mere degreewise bijection: it commutes with every face and degeneracy map. -/
def interfaceClassifyingDiagramVerticalVerticesIso :
    InterfaceClassifyingDiagramVerticalVertices M ≅ M.InterfaceNerve :=
  NatIso.ofComponents
    (fun _ ↦ (CategoryTheory.nerveEquiv
      (C := ComposableArrows M.Object _)).toIso)
    (fun _ ↦ by
      ext F
      rfl)

/-- Vertical vertices in outer degree `n` recover the `n`-simplices of the
ordinary interface nerve. -/
def interfaceClassifyingDiagramVerticalVertexEquiv (n : ℕ) :
    ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)) _⦋0⦌ ≃
      M.InterfaceNerve _⦋n⦌ :=
  CategoryTheory.nerveEquiv

/-- Vertical edges are exactly natural transformations between outer
`n`-simplices.  Such a transformation is a pointwise internal identity and,
by univalence of the internal model, a pointwise structural equivalence. -/
def interfaceClassifyingDiagramVerticalEdgeEquiv (n : ℕ)
    (F G : M.InterfaceNerve _⦋n⦌) :
    ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)).Edge
        ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm F)
        ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm G) ≃
      (F ⟶ G) :=
  CategoryTheory.nerve.homEquiv

/-- Every vertical transformation is invertible. -/
theorem interfaceClassifyingDiagramVerticalTransformation_isIso (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌} (η : F ⟶ G) :
    IsIso η := by
  exact NatIso.isIso_of_isIso_app η

/-- The inverse of a natural transformation between outer simplices. -/
noncomputable def interfaceClassifyingDiagramVerticalTransformationInverse (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌} (η : F ⟶ G) : G ⟶ F := by
  letI : IsIso η :=
    interfaceClassifyingDiagramVerticalTransformation_isIso M n η
  exact inv η

/-- A vertical transformation followed by its inverse is the identity. -/
@[simp]
theorem interfaceClassifyingDiagramVerticalTransformation_comp_inverse (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌} (η : F ⟶ G) :
    η ≫ interfaceClassifyingDiagramVerticalTransformationInverse M n η = 𝟙 F := by
  have : IsIso η :=
    interfaceClassifyingDiagramVerticalTransformation_isIso M n η
  simp [interfaceClassifyingDiagramVerticalTransformationInverse]

/-- The inverse of a vertical transformation followed by that transformation
is the identity. -/
@[simp]
theorem interfaceClassifyingDiagramVerticalTransformation_inverse_comp (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌} (η : F ⟶ G) :
    interfaceClassifyingDiagramVerticalTransformationInverse M n η ≫ η = 𝟙 G := by
  have : IsIso η :=
    interfaceClassifyingDiagramVerticalTransformation_isIso M n η
  simp [interfaceClassifyingDiagramVerticalTransformationInverse]

/-- The component of a vertical edge is an internal interface identity. -/
def interfaceClassifyingDiagramVerticalEdgeComponent (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌}
    (edge : ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)).Edge
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm F)
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm G))
    (i : Fin (n + 1)) : F.obj i ⟶ G.obj i :=
  (interfaceClassifyingDiagramVerticalEdgeEquiv M n F G edge).app i

/-- Every component of a vertical edge is an invertible internal identity. -/
theorem interfaceClassifyingDiagramVerticalEdgeComponent_isIso (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌}
    (edge : ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)).Edge
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm F)
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm G))
    (i : Fin (n + 1)) :
    IsIso (interfaceClassifyingDiagramVerticalEdgeComponent M n edge i) := by
  infer_instance

/-- Reverse a vertical edge using the inverse natural transformation. -/
noncomputable def interfaceClassifyingDiagramVerticalInverseEdge (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌}
    (edge : ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)).Edge
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm F)
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm G)) :
    ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)).Edge
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm G)
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm F) := by
  exact CategoryTheory.nerve.edgeMk
    (interfaceClassifyingDiagramVerticalTransformationInverse M n
      (interfaceClassifyingDiagramVerticalEdgeEquiv M n F G edge))

/-- Decoding the reversed vertical edge recovers the inverse natural
transformation exactly. -/
@[simp]
theorem interfaceClassifyingDiagramVerticalEdgeEquiv_inverseEdge (n : ℕ)
    {F G : M.InterfaceNerve _⦋n⦌}
    (edge : ((InterfaceClassifyingDiagram M).obj (op ⦋n⦌)).Edge
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm F)
      ((interfaceClassifyingDiagramVerticalVertexEquiv M n).symm G)) :
    interfaceClassifyingDiagramVerticalEdgeEquiv M n G F
      (interfaceClassifyingDiagramVerticalInverseEdge M n edge) =
        interfaceClassifyingDiagramVerticalTransformationInverse M n
          (interfaceClassifyingDiagramVerticalEdgeEquiv M n F G edge) := by
  exact CategoryTheory.nerve.homEquiv_edgeMk _

end UniverseModel

end Ript.Univalent
