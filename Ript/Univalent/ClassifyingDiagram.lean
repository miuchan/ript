import Mathlib.CategoryTheory.Functor.Currying
import Ript.ForMathlib.AlgebraicTopology.ReedyMatching
import Ript.ForMathlib.AlgebraicTopology.StrictSegalIso
import Ript.ForMathlib.CategoryTheory.GroupoidInterval
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
levelwise groupoidal/Kan structure.  It identifies its vertical vertices with
the ordinary interface nerve and its vertical edges with invertible natural
transformations.  By flipping the two finite indexing categories, every
horizontal row is naturally isomorphic to an ordinary categorical nerve, so
the actual outer spine maps are equivalences in every bidegree.  The Rezk
completeness comparison is the outer degeneracy from degree zero to the space
of horizontal equivalences.  Since the source is a groupoid, every horizontal
arrow is an equivalence; this file proves that the actual degeneracy is the
nerve of an equivalence of categories.  Higher localization remains separate.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory
open HomotopicalAlgebra
open Opposite
open Simplicial
open SSet
open scoped SSet.modelCategoryQuillen

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

/-- The horizontal simplicial set obtained by evaluating the vertical
simplicial direction in degree `k`. -/
def InterfaceClassifyingDiagramHorizontalRow (k : ℕ) : SSet :=
  InterfaceClassifyingDiagram M ⋙ SSet.evaluation.obj (op ⦋k⦌)

/-- In bidegree `(n,k)`, flipping the two finite indexing categories identifies
the classifying diagram with the `n`-simplices in the nerve of the category of
composable `k`-strings. -/
def interfaceClassifyingDiagramHorizontalSimplexEquiv (k n : ℕ) :
    (InterfaceClassifyingDiagramHorizontalRow M k) _⦋n⦌ ≃
      (CategoryTheory.nerve (ComposableArrows M.Object k)) _⦋n⦌ :=
  Functor.flippingEquiv

/-- Flipping the two finite indexing categories is natural in the horizontal
simplicial direction.  Thus every horizontal row is an ordinary categorical
nerve, not merely degreewise equivalent to one. -/
def interfaceClassifyingDiagramHorizontalRowIso (k : ℕ) :
    InterfaceClassifyingDiagramHorizontalRow M k ≅
      CategoryTheory.nerve (ComposableArrows M.Object k) :=
  NatIso.ofComponents
    (fun _ ↦ (Functor.flippingEquiv
      (C := Fin (k + 1)) (D := Fin (_ + 1)) (E := M.Object)).toIso)
    (fun _ ↦ by
      ext F
      rfl)

/-- Every horizontal row has a canonical strict Segal structure, transported
from the ordinary nerve of the category of composable `k`-strings. -/
def interfaceClassifyingDiagramHorizontalStrictSegal (k : ℕ) :
    SSet.StrictSegal (InterfaceClassifyingDiagramHorizontalRow M k) :=
  SSet.StrictSegal.ofIso
    (interfaceClassifyingDiagramHorizontalRowIso M k)
    (CategoryTheory.Nerve.strictSegal (ComposableArrows M.Object k))

/-- Proposition-level strict-Segal instance for every horizontal row. -/
instance interfaceClassifyingDiagramHorizontalRowIsStrictSegal (k : ℕ) :
    (InterfaceClassifyingDiagramHorizontalRow M k).IsStrictSegal :=
  (interfaceClassifyingDiagramHorizontalStrictSegal M k).isStrictSegal

/-- The outer Segal comparison in every vertical degree is an equivalence.
Its forward map is the actual spine map, so this is stronger than a merely
chosen equivalence between the two underlying types. -/
def interfaceClassifyingDiagramOuterSegalEquiv (k n : ℕ) :
    (InterfaceClassifyingDiagramHorizontalRow M k) _⦋n⦌ ≃
      (InterfaceClassifyingDiagramHorizontalRow M k).Path n :=
  (interfaceClassifyingDiagramHorizontalStrictSegal M k).spineEquiv n

/-- The forward direction of the outer Segal equivalence is definitionally
the outer spine comparison. -/
@[simp]
theorem interfaceClassifyingDiagramOuterSegalEquiv_apply (k n : ℕ)
    (x : (InterfaceClassifyingDiagramHorizontalRow M k) _⦋n⦌) :
    interfaceClassifyingDiagramOuterSegalEquiv M k n x =
      (InterfaceClassifyingDiagramHorizontalRow M k).spine n x :=
  rfl

/-- The vertical simplicial set of objects in outer degree zero. -/
abbrev InterfaceClassifyingDiagramObjectSpace : SSet :=
  (InterfaceClassifyingDiagram M).obj (op ⦋0⦌)

/-- The vertical simplicial set of horizontal equivalences.  For the
classifying diagram of a groupoid this is the entire outer degree-one space,
because every horizontal arrow is invertible. -/
abbrev InterfaceClassifyingDiagramEquivalenceSpace : SSet :=
  (InterfaceClassifyingDiagram M).obj (op ⦋1⦌)

/-- Every horizontal arrow represented in outer degree one is an equivalence
in the internal interface groupoid. -/
theorem interfaceClassifyingDiagramHorizontalArrow_isIso
    (F : ComposableArrows M.Object 1) : IsIso F.hom := by
  infer_instance

/-- The Rezk completeness comparison: the actual outer zero-degeneracy sends
an object to its identity horizontal arrow. -/
def interfaceClassifyingDiagramCompletenessMap :
    InterfaceClassifyingDiagramObjectSpace M ⟶
      InterfaceClassifyingDiagramEquivalenceSpace M :=
  (InterfaceClassifyingDiagram M).σ (0 : Fin 1)

/-- The composite equivalence through the underlying interface groupoid has a
forward functor naturally isomorphic to the actual outer zero-degeneracy
functor.  The explicit isomorphism prevents replacing the real simplicial
structure map by an unrelated equivalent functor. -/
noncomputable def interfaceClassifyingDiagramCompletenessFunctorIso :
    (CategoryTheory.Groupoid.constantDiagramEquivalence M.Object 0).symm.functor ⋙
        (CategoryTheory.Groupoid.constantDiagramEquivalence M.Object 1).functor ≅
      ((interfaceClassifyingDiagramCat M).σ (0 : Fin 1)).toFunctor :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents
      (fun i ↦ Groupoid.isoEquivHom _ _ |>.symm
        (F.map (homOfLE (Fin.zero_le
          ((SimplexCategory.toCat.map
            (SimplexCategory.σ (0 : Fin 1))).toFunctor.obj i)))))
      (fun _ ↦ by
        change (𝟙 (F.obj 0) : F.obj 0 ⟶ F.obj 0) ≫ F.map _ =
          F.map _ ≫ F.map _
        rw [Category.id_comp, ← F.map_comp]
        congr))
    (fun η ↦ by
      apply NatTrans.ext
      funext i
      exact (η.naturality (homOfLE (Fin.zero_le
        ((SimplexCategory.toCat.map
          (SimplexCategory.σ (0 : Fin 1))).toFunctor.obj i)))).symm)

/-- The category functor underlying the actual Rezk completeness comparison
is an equivalence.  Its inverse evaluates an identity-arrow diagram at its
source and packages the result as an outer zero-simplex. -/
noncomputable def interfaceClassifyingDiagramCompletenessEquivalence :
    ComposableArrows M.Object 0 ≌ ComposableArrows M.Object 1 :=
  ((CategoryTheory.Groupoid.constantDiagramEquivalence M.Object 0).symm.trans
    (CategoryTheory.Groupoid.constantDiagramEquivalence M.Object 1)).changeFunctor
      (interfaceClassifyingDiagramCompletenessFunctorIso M)

/-- The forward functor of the completeness equivalence is definitionally the
actual outer zero-degeneracy functor. -/
@[simp]
theorem interfaceClassifyingDiagramCompletenessEquivalence_functor :
    (interfaceClassifyingDiagramCompletenessEquivalence M).functor =
      ((interfaceClassifyingDiagramCat M).σ (0 : Fin 1)).toFunctor :=
  rfl

/-- The actual category-valued outer zero-degeneracy is an equivalence. -/
noncomputable instance interfaceClassifyingDiagramCompletenessFunctorIsEquivalence :
    ((interfaceClassifyingDiagramCat M).σ
      (0 : Fin 1)).toFunctor.IsEquivalence :=
  (interfaceClassifyingDiagramCompletenessEquivalence M).isEquivalence_functor

/-- The actual Rezk completeness map is exactly the nerve of the forward
functor in the displayed category equivalence.  Thus the formal statement is
about the real outer degeneracy, not only an abstract map between equivalent
objects. -/
theorem interfaceClassifyingDiagramCompletenessMap_eq_nerveMap :
    interfaceClassifyingDiagramCompletenessMap M =
      CategoryTheory.nerveMap
        (interfaceClassifyingDiagramCompletenessEquivalence M).functor :=
  rfl

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

/-- Outer degree `n` of the categorical classifying diagram is isomorphic to
the simplicial mapping space `Map(Δ[n], N(M.Object))`.  The construction uses
the closed-nerve comparison and a strict universe-lift bridge for the finite
ordinal indexing category. -/
noncomputable def interfaceClassifyingDiagramMappingSpaceIso (n : ℕ) :
    (InterfaceClassifyingDiagram M).obj (op ⦋n⦌) ≅
      (ihom (Δ[n] : SSet.{u})).obj M.InterfaceNerve := by
  change CategoryTheory.nerve (Fin (n + 1) ⥤ M.Object) ≅ _
  exact SSet.nerveFunctorSimplexMappingIso M.Object n

/-- The concrete degree-`n` boundary-matching object in the mapping-space
presentation of the interface classifying diagram. -/
abbrev InterfaceClassifyingDiagramBoundaryMatchingObject (n : ℕ) : SSet.{u} :=
  SSet.BoundaryMatchingObject M.InterfaceNerve n

/-- Transport the standard boundary-restriction matching map through the
categorical classifying diagram's degreewise mapping-space presentation. -/
noncomputable def interfaceClassifyingDiagramBoundaryMatchingMap (n : ℕ) :
    (InterfaceClassifyingDiagram M).obj (op ⦋n⦌) ⟶
      InterfaceClassifyingDiagramBoundaryMatchingObject M n :=
  (interfaceClassifyingDiagramMappingSpaceIso M n).hom ≫
    SSet.boundaryMatchingMap M.InterfaceNerve n

/-- Every transported boundary-matching map is a fibration.  This proves the
model-categorical lifting statement needed for Reedy fibrancy once the
degreewise presentation is upgraded to a natural identification with the
abstract Reedy matching limit. -/
theorem interfaceClassifyingDiagramBoundaryMatchingMap_fibration (n : ℕ) :
    Fibration (interfaceClassifyingDiagramBoundaryMatchingMap M n) := by
  change Fibration ((interfaceClassifyingDiagramMappingSpaceIso M n).hom ≫
    SSet.boundaryMatchingMap M.InterfaceNerve n)
  rw [fibration_iff]
  apply (fibrations SSet).comp_mem
  · rw [← fibration_iff]
    infer_instance
  · rw [← fibration_iff]
    exact SSet.boundaryMatchingMap_fibration M.InterfaceNerve n

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
