import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Products.Associator
import Ript.ForMathlib.AlgebraicTopology.GroupoidNerve
import Ript.ForMathlib.AlgebraicTopology.NerveHomotopy
import Ript.ForMathlib.CategoryTheory.Bicategory.HomotopyCategory
import Ript.Higher.TotalModelCoherence

/-!
# Simplicial semantics of the total resource-model bicategory

This module gives two complementary, honest simplicial views of the total
bicategory.

* The object core is the nerve of the core of the bicategorical homotopy
  category. Its edges are exactly total-model equivalences up to invertible
  2-cells. It is a Kan, strict-Segal, 2-coskeletal simplicial set.
* For every pair of total models, the mapping nerve is the ordinary nerve of
  their full local hom-category. Its vertices are resource-changing model
  1-cells and its edges are all monoidal model 2-cells, including
  noninvertible ones. Horizontal composition is represented by a functor and
  hence by an exact simplicial map. The bicategorical associator and both
  unitors are lifted to natural isomorphisms and then to genuine simplicial
  homotopies, with the pointwise pentagon and triangle equations retained.

The second construction deliberately does not replace local categories by
groupoids, so noninvertible 2-cells are retained. Together these layers are a
verified object/equivalence and locally coherent 2-cell bridge toward a
complete Segal 2-space. They are not yet the global bisimplicial assembly or
a higher-localization universal property for the full resource bicategory.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory
open Opposite
open SSet
open Simplicial

universe u v w

namespace TotalModelSimplicial

/-- The homotopy 1-category of the total resource-model bicategory. Objects
are unchanged; parallel 1-cells are identified exactly along invertible
2-cells. -/
abbrev HomotopyCategory :=
  CategoryTheory.Bicategory.HomotopyCategory ResourceModel.{u, v, w}

/-- The groupoid of total resource models and isomorphisms in the homotopy
category. -/
abbrev ObjectCore := CategoryTheory.Core (HomotopyCategory.{u, v, w})

/-- The simplicial object-equivalence core of the total model bicategory. -/
abbrev ObjectNerve := CategoryTheory.nerve (ObjectCore.{u, v, w})

/-- A total model as a vertex object of the homotopy core. -/
def objectCoreVertex (M : ResourceModel.{u, v, w}) :
    ObjectCore.{u, v, w} :=
  ⟨CategoryTheory.Bicategory.HomotopyCategory.of M⟩

/-- A total model as a vertex of the object nerve. -/
def objectNerveVertex (M : ResourceModel.{u, v, w}) :
    ObjectNerve.{u, v, w} _⦋0⦌ :=
  CategoryTheory.nerveEquiv.symm (objectCoreVertex M)

/-- Edges between represented total models are exactly isomorphisms in the
bicategorical homotopy category. -/
def objectNerveEdgeEquiv (M N : ResourceModel.{u, v, w}) :
    ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N) ≃
      (CategoryTheory.Bicategory.HomotopyCategory.of M ≅
        CategoryTheory.Bicategory.HomotopyCategory.of N) :=
  (CategoryTheory.nerve.homEquiv).trans
    { toFun := fun edge ↦ edge.iso
      invFun := fun iso ↦ ⟨iso⟩
      left_inv := by
        intro edge
        cases edge
        rfl
      right_inv := by
        intro iso
        rfl }

/-- A bicategorical equivalence determines an edge of the total-model object
nerve. -/
def objectNerveEquivalenceEdge {M N : ResourceModel.{u, v, w}}
    (equivalence : CategoryTheory.Bicategory.Equivalence M N) :
    ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N) :=
  CategoryTheory.nerve.edgeMk
    ⟨CategoryTheory.Bicategory.HomotopyCategory.isoOfEquivalence equivalence⟩

@[simp]
theorem objectNerveEdgeEquiv_equivalenceEdge
    {M N : ResourceModel.{u, v, w}}
    (equivalence : CategoryTheory.Bicategory.Equivalence M N) :
    objectNerveEdgeEquiv M N (objectNerveEquivalenceEdge equivalence) =
      CategoryTheory.Bicategory.HomotopyCategory.isoOfEquivalence equivalence := by
  change
    (CategoryTheory.nerve.homEquiv
      (CategoryTheory.nerve.edgeMk
        (C := ObjectCore.{u, v, w})
        ⟨CategoryTheory.Bicategory.HomotopyCategory.isoOfEquivalence
          equivalence⟩)).iso = _
  rw [CategoryTheory.nerve.homEquiv_edgeMk]

/-- Choose a bicategorical equivalence represented by an arbitrary object-core
edge. Choice is confined to selecting a representative of one homotopy-class
quotient; it does not enter executable process models. -/
noncomputable def objectNerveEdgeToEquivalence
    {M N : ResourceModel.{u, v, w}}
    (edge : ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N)) :
    CategoryTheory.Bicategory.Equivalence M N := by
  let homotopyIso := objectNerveEdgeEquiv M N edge
  let representative : M ⟶ N := Quotient.out homotopyIso.hom
  have represented :
      CategoryTheory.Bicategory.HomotopyCategory.homMk representative =
        homotopyIso.hom :=
    Quotient.out_eq _
  letI : IsIso
      (CategoryTheory.Bicategory.HomotopyCategory.homMk representative) := by
    rw [represented]
    infer_instance
  exact CategoryTheory.Bicategory.HomotopyCategory.equivalenceOfIsIso
    representative

/-- The chosen equivalence has exactly the homotopy-class edge from which it
was extracted. -/
theorem objectNerveEdgeToEquivalence_hom
    {M N : ResourceModel.{u, v, w}}
    (edge : ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N)) :
    CategoryTheory.Bicategory.HomotopyCategory.homMk
        (objectNerveEdgeToEquivalence edge).hom =
      (objectNerveEdgeEquiv M N edge).hom := by
  change CategoryTheory.Bicategory.HomotopyCategory.homMk
      (Quotient.out (objectNerveEdgeEquiv M N edge).hom) =
    (objectNerveEdgeEquiv M N edge).hom
  exact Quotient.out_eq _

/-- **Object-equivalence representation.** Every edge of the total-model
object nerve is represented by a bicategorical equivalence, and re-encoding
the chosen equivalence recovers the original edge exactly. -/
theorem objectNerveEquivalenceEdge_edgeToEquivalence
    {M N : ResourceModel.{u, v, w}}
    (edge : ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N)) :
    objectNerveEquivalenceEdge (objectNerveEdgeToEquivalence edge) = edge := by
  apply (objectNerveEdgeEquiv M N).injective
  rw [objectNerveEdgeEquiv_equivalenceEdge]
  apply CategoryTheory.Iso.ext
  exact objectNerveEdgeToEquivalence_hom edge

/-- Every object-core edge has a bicategorical-equivalence representative. -/
theorem objectNerveEdge_exists_equivalence
    {M N : ResourceModel.{u, v, w}}
    (edge : ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N)) :
    ∃ equivalence : CategoryTheory.Bicategory.Equivalence M N,
      objectNerveEquivalenceEdge equivalence = edge :=
  ⟨objectNerveEdgeToEquivalence edge,
    objectNerveEquivalenceEdge_edgeToEquivalence edge⟩

/-! ## Single-valued internal equivalence classes -/

/-- Two chosen bicategorical equivalences represent the same internal object
identity exactly when they determine the same edge of the object nerve. -/
def equivalenceSetoid (M N : ResourceModel.{u, v, w}) :
    Setoid (CategoryTheory.Bicategory.Equivalence M N) where
  r first second :=
    objectNerveEquivalenceEdge first = objectNerveEquivalenceEdge second
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun equality ↦ equality.symm
    trans := fun first second ↦ first.trans second }

/-- Internal, single-valued total-model equivalences: chosen adjoint
equivalences modulo equality of their represented object-nerve edge. -/
abbrev InternalEquivalence (M N : ResourceModel.{u, v, w}) :=
  Quotient (equivalenceSetoid M N)

namespace InternalEquivalence

/-- Embed one chosen bicategorical equivalence into its internal quotient. -/
def mk {M N : ResourceModel.{u, v, w}}
    (equivalence : CategoryTheory.Bicategory.Equivalence M N) :
    InternalEquivalence M N :=
  Quotient.mk (equivalenceSetoid M N) equivalence

/-- Interpret an internal total-model equivalence as its canonical object-nerve
edge. -/
def toEdge {M N : ResourceModel.{u, v, w}}
    (equivalence : InternalEquivalence M N) :
    ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N) :=
  Quotient.lift objectNerveEquivalenceEdge (fun _ _ equality ↦ equality)
    equivalence

@[simp]
theorem toEdge_mk {M N : ResourceModel.{u, v, w}}
    (equivalence : CategoryTheory.Bicategory.Equivalence M N) :
    toEdge (mk equivalence) = objectNerveEquivalenceEdge equivalence :=
  rfl

/-- Every object-nerve edge determines an internal equivalence class. -/
noncomputable def ofEdge {M N : ResourceModel.{u, v, w}}
    (edge : ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N)) :
    InternalEquivalence M N :=
  mk (objectNerveEdgeToEquivalence edge)

@[simp]
theorem toEdge_ofEdge {M N : ResourceModel.{u, v, w}}
    (edge : ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N)) :
    toEdge (ofEdge edge) = edge :=
  objectNerveEquivalenceEdge_edgeToEquivalence edge

@[simp]
theorem ofEdge_toEdge {M N : ResourceModel.{u, v, w}}
    (equivalence : InternalEquivalence M N) :
    ofEdge (toEdge equivalence) = equivalence := by
  induction equivalence using Quotient.inductionOn with
  | _ representative =>
      apply Quotient.sound
      exact objectNerveEquivalenceEdge_edgeToEquivalence
        (objectNerveEquivalenceEdge representative)

/-- **Total-model internal univalence at object level.** Internal equivalence
classes are exactly identity edges of the Kan object core. -/
noncomputable def edgeEquiv {M N : ResourceModel.{u, v, w}} :
    InternalEquivalence M N ≃
      ObjectNerve.Edge (objectNerveVertex M) (objectNerveVertex N) where
  toFun := toEdge
  invFun := ofEdge
  left_inv := ofEdge_toEdge
  right_inv := toEdge_ofEdge

end InternalEquivalence

/-- The object-equivalence nerve is strict Segal. -/
def objectNerveStrictSegal : SSet.StrictSegal ObjectNerve.{u, v, w} :=
  CategoryTheory.Nerve.strictSegal ObjectCore.{u, v, w}

instance objectNerveIsStrictSegal : ObjectNerve.{u, v, w}.IsStrictSegal :=
  objectNerveStrictSegal.isStrictSegal

/-- The object-equivalence nerve is Kan because its source is a groupoid. -/
instance objectNerveKanComplex : KanComplex ObjectNerve.{u, v, w} :=
  CategoryTheory.Nerve.kanComplex ObjectCore.{u, v, w}

instance objectNerveQuasicategory : Quasicategory ObjectNerve.{u, v, w} :=
  inferInstance

instance objectNerveTwoCoskeletal :
    SimplicialObject.IsCoskeletal ObjectNerve.{u, v, w} 2 :=
  inferInstance

/-! ## Full local mapping nerves -/

/-- The full simplicial mapping category between two total resource models.
Vertices are model 1-cells and edges are all model 2-cells. -/
abbrev MappingNerve (M N : ResourceModel.{u, v, w}) :=
  CategoryTheory.nerve (ResourceModelHom M N)

/-- Vertices of a local mapping nerve are exactly resource-changing model
1-cells. -/
def mappingNerveVertexEquiv (M N : ResourceModel.{u, v, w}) :
    MappingNerve M N _⦋0⦌ ≃ ResourceModelHom M N :=
  CategoryTheory.nerveEquiv

/-- Encode a total-model 1-cell as a mapping-nerve vertex. -/
def mappingNerveVertex {M N : ResourceModel.{u, v, w}}
    (F : ResourceModelHom M N) : MappingNerve M N _⦋0⦌ :=
  (mappingNerveVertexEquiv M N).symm F

/-- Edges between mapping-nerve vertices are exactly total-model 2-cells,
without an invertibility restriction. -/
def mappingNerveEdgeEquiv {M N : ResourceModel.{u, v, w}}
    (F G : ResourceModelHom M N) :
    (MappingNerve M N).Edge (mappingNerveVertex F) (mappingNerveVertex G) ≃
      ResourceModelTransformation F G :=
  CategoryTheory.nerve.homEquiv

/-- Encode an arbitrary total-model 2-cell as an edge in its local mapping
nerve. -/
def mappingNerveTransformationEdge
    {M N : ResourceModel.{u, v, w}} {F G : ResourceModelHom M N}
    (transformation : ResourceModelTransformation F G) :
    (MappingNerve M N).Edge (mappingNerveVertex F) (mappingNerveVertex G) :=
  CategoryTheory.nerve.edgeMk transformation

@[simp]
theorem mappingNerveEdgeEquiv_transformationEdge
    {M N : ResourceModel.{u, v, w}} {F G : ResourceModelHom M N}
    (transformation : ResourceModelTransformation F G) :
    mappingNerveEdgeEquiv F G
        (mappingNerveTransformationEdge transformation) = transformation := by
  exact CategoryTheory.nerve.homEquiv_edgeMk
    (C := ResourceModelHom M N) (x := F) (y := G)
    (transformation : F ⟶ G)

/-- The 2-simplex encoding vertical composition of two model 2-cells. -/
def mappingNerveVerticalCompositionSimplex
    {M N : ResourceModel.{u, v, w}} {F G H : ResourceModelHom M N}
    (first : ResourceModelTransformation F G)
    (second : ResourceModelTransformation G H) :
    MappingNerve M N _⦋2⦌ :=
  ComposableArrows.mk₂ first second

@[simp]
theorem mappingNerveVerticalComposition_composite
    {M N : ResourceModel.{u, v, w}} {F G H : ResourceModelHom M N}
    (first : ResourceModelTransformation F G)
    (second : ResourceModelTransformation G H) :
    (MappingNerve M N).δ 1
        (mappingNerveVerticalCompositionSimplex first second) =
      ComposableArrows.mk₁ (first ≫ second) := by
  exact CategoryTheory.nerve.δ₁_mk₂_eq
    (C := ResourceModelHom M N) (X₀ := F) (X₁ := G) (X₂ := H)
    (first : F ⟶ G) (second : G ⟶ H)

/-- Every local mapping nerve is strict Segal. -/
def mappingNerveStrictSegal (M N : ResourceModel.{u, v, w}) :
    SSet.StrictSegal (MappingNerve M N) :=
  CategoryTheory.Nerve.strictSegal (ResourceModelHom M N)

instance mappingNerveIsStrictSegal (M N : ResourceModel.{u, v, w}) :
    (MappingNerve M N).IsStrictSegal :=
  (mappingNerveStrictSegal M N).isStrictSegal

instance mappingNerveQuasicategory (M N : ResourceModel.{u, v, w}) :
    Quasicategory (MappingNerve M N) :=
  inferInstance

instance mappingNerveTwoCoskeletal (M N : ResourceModel.{u, v, w}) :
    SimplicialObject.IsCoskeletal (MappingNerve M N) 2 :=
  inferInstance

/-! ## Global low-dimensional Duskin data -/

/-- Identity 2-cell with its total-model transformation type exposed
explicitly, avoiding ambiguity with identities internal to a model carrier. -/
def identityTransformation
    {A B : ResourceModel.{u, v, w}} (F : ResourceModelHom A B) :
    ResourceModelTransformation F F :=
  ResourceModelTransformation.ofNatTrans rfl (𝟙 F.toFunctor)

/-- The total bicategory associator exposed as a typed model
transformation. -/
def associatorTransformation
    {A B C D : ResourceModel.{u, v, w}}
    (first : ResourceModelHom A B)
    (second : ResourceModelHom B C)
    (third : ResourceModelHom C D) :
    ResourceModelTransformation ((first.comp second).comp third)
      (first.comp (second.comp third)) := by
  exact (CategoryTheory.Bicategory.associator
    (B := ResourceModel.{u, v, w}) first second third).hom

/-- A Duskin 2-simplex: three total models, its two consecutive edges, a
diagonal edge, and an arbitrary comparison 2-cell from the composite to that
diagonal. -/
structure Triangle
    (A B C : ResourceModel.{u, v, w}) where
  /-- Edge from vertex zero to vertex one. -/
  edge01 : ResourceModelHom A B
  /-- Edge from vertex one to vertex two. -/
  edge12 : ResourceModelHom B C
  /-- Diagonal edge from vertex zero to vertex two. -/
  edge02 : ResourceModelHom A C
  /-- Lax triangular comparison from the consecutive composite to the
  diagonal. -/
  cell012 : ResourceModelTransformation (edge01.comp edge12) edge02

namespace Triangle

/-- The canonical 2-simplex of a composable pair has the composite itself as
diagonal and the identity comparison cell. -/
def composition
    {A B C : ResourceModel.{u, v, w}}
    (first : ResourceModelHom A B) (second : ResourceModelHom B C) :
    Triangle A B C where
  edge01 := first
  edge12 := second
  edge02 := first.comp second
  cell012 := identityTransformation _

@[simp]
theorem composition_cell
    {A B C : ResourceModel.{u, v, w}}
    (first : ResourceModelHom A B) (second : ResourceModelHom B C) :
    (composition first second).cell012 =
      identityTransformation (first.comp second) :=
  rfl

end Triangle

/-- Boundary data of a Duskin 3-simplex: six edges and one comparison 2-cell
on each triangular face. -/
structure TetrahedronBoundary
    (A B C D : ResourceModel.{u, v, w}) where
  /-- Edge `0 → 1`. -/
  edge01 : ResourceModelHom A B
  /-- Edge `1 → 2`. -/
  edge12 : ResourceModelHom B C
  /-- Edge `2 → 3`. -/
  edge23 : ResourceModelHom C D
  /-- Edge `0 → 2`. -/
  edge02 : ResourceModelHom A C
  /-- Edge `1 → 3`. -/
  edge13 : ResourceModelHom B D
  /-- Edge `0 → 3`. -/
  edge03 : ResourceModelHom A D
  /-- Face comparison on vertices `0,1,2`. -/
  cell012 : ResourceModelTransformation (edge01.comp edge12) edge02
  /-- Face comparison on vertices `1,2,3`. -/
  cell123 : ResourceModelTransformation (edge12.comp edge23) edge13
  /-- Face comparison on vertices `0,1,3`. -/
  cell013 : ResourceModelTransformation (edge01.comp edge13) edge03
  /-- Face comparison on vertices `0,2,3`. -/
  cell023 : ResourceModelTransformation (edge02.comp edge23) edge03

namespace TetrahedronBoundary

/-- The tetrahedral Duskin coherence equation. The associator is essential:
horizontal composition in the source is weakly, not definitionally,
associative. -/
def Coherent
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D) : Prop :=
  ResourceModelTransformation.whiskerRight
        boundary.cell012 boundary.edge23 ≫ boundary.cell023 =
    associatorTransformation
        boundary.edge01 boundary.edge12 boundary.edge23 ≫
      ResourceModelTransformation.whiskerLeft
        boundary.edge01 boundary.cell123 ≫ boundary.cell013

/-- The `0,1,2` triangular face. -/
def face012
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D) : Triangle A B C where
  edge01 := boundary.edge01
  edge12 := boundary.edge12
  edge02 := boundary.edge02
  cell012 := boundary.cell012

/-- The `1,2,3` triangular face. -/
def face123
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D) : Triangle B C D where
  edge01 := boundary.edge12
  edge12 := boundary.edge23
  edge02 := boundary.edge13
  cell012 := boundary.cell123

/-- The `0,1,3` triangular face. -/
def face013
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D) : Triangle A B D where
  edge01 := boundary.edge01
  edge12 := boundary.edge13
  edge02 := boundary.edge03
  cell012 := boundary.cell013

/-- The `0,2,3` triangular face. -/
def face023
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D) : Triangle A C D where
  edge01 := boundary.edge02
  edge12 := boundary.edge23
  edge02 := boundary.edge03
  cell012 := boundary.cell023

end TetrahedronBoundary

/-- A Duskin 3-simplex is exactly a tetrahedral boundary equipped with its
associator-corrected coherence proof. -/
structure Tetrahedron
    (A B C D : ResourceModel.{u, v, w}) extends
      TetrahedronBoundary A B C D where
  /-- Compatibility of the four triangular 2-cells. -/
  coherence : toTetrahedronBoundary.Coherent

namespace Tetrahedron

/-- Build the unique tetrahedron carried by one coherent boundary. -/
def ofCoherent
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D)
    (coherence : boundary.Coherent) : Tetrahedron A B C D where
  toTetrahedronBoundary := boundary
  coherence := coherence

/-- **Three-dimensional representation and completeness.** A tetrahedral
boundary has a unique Duskin 3-simplex above it exactly when its four face
cells satisfy the associator-corrected coherence equation. -/
theorem existsUnique_over_iff_coherent
    {A B C D : ResourceModel.{u, v, w}}
    (boundary : TetrahedronBoundary A B C D) :
    boundary.Coherent ↔
      ∃! tetrahedron : Tetrahedron A B C D,
        tetrahedron.toTetrahedronBoundary = boundary := by
  constructor
  · intro coherence
    refine ⟨ofCoherent boundary coherence, rfl, ?_⟩
    intro tetrahedron equality
    cases tetrahedron with
    | mk tetrahedronBoundary tetrahedronCoherence =>
        dsimp at equality
        subst tetrahedronBoundary
        rfl
  · rintro ⟨tetrahedron, equality, _unique⟩
    rw [← equality]
    exact tetrahedron.coherence

/-- The canonical tetrahedron on three composable 1-cells. Its long diagonal
uses right-associated composition and its `0,2,3` face is the bicategorical
associator. -/
def composition
    {A B C D : ResourceModel.{u, v, w}}
    (first : ResourceModelHom A B)
    (second : ResourceModelHom B C)
    (third : ResourceModelHom C D) : Tetrahedron A B C D where
  edge01 := first
  edge12 := second
  edge23 := third
  edge02 := first.comp second
  edge13 := second.comp third
  edge03 := first.comp (second.comp third)
  cell012 := identityTransformation _
  cell123 := identityTransformation _
  cell013 := identityTransformation _
  cell023 := associatorTransformation first second third
  coherence := by
    change ResourceModelTransformation.whiskerRight
          (identityTransformation (first.comp second)) third ≫
        associatorTransformation first second third =
      associatorTransformation first second third ≫
        ResourceModelTransformation.whiskerLeft first
          (identityTransformation (second.comp third)) ≫
        identityTransformation (first.comp (second.comp third))
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight
          (𝟙 (first.toFunctor ⋙ second.toFunctor)) third.toFunctor ≫
        (Functor.associator
          first.toFunctor second.toFunctor third.toFunctor).hom =
      (Functor.associator
          first.toFunctor second.toFunctor third.toFunctor).hom ≫
        Functor.whiskerLeft first.toFunctor
          (𝟙 (second.toFunctor ⋙ third.toFunctor)) ≫
        𝟙 (first.toFunctor ⋙ second.toFunctor ⋙ third.toFunctor)
    ext object
    simp

@[simp]
theorem composition_cell023
    {A B C D : ResourceModel.{u, v, w}}
    (first : ResourceModelHom A B)
    (second : ResourceModelHom B C)
    (third : ResourceModelHom C D) :
    (composition first second third).cell023 =
      associatorTransformation first second third :=
  rfl

end Tetrahedron

/-! ## Horizontal composition -/

/-- Horizontal composition is a functor between local hom-categories. Its
functor laws are exactly identity preservation and bicategorical interchange. -/
def horizontalCompositionFunctor
    (A B C : ResourceModel.{u, v, w}) :
    (ResourceModelHom A B × ResourceModelHom B C) ⥤ ResourceModelHom A C where
  obj pair := pair.1.comp pair.2
  map transformation := ResourceModelTransformation.horizontalComp
    transformation.1 transformation.2
  map_id pair := by
    apply ResourceModelTransformation.ext
    simp [ResourceModelTransformation.horizontalComp_toNatTrans]
    rfl
  map_comp first second := by
    exact (ResourceModelTransformation.horizontalComp_interchange
      first.1 second.1 first.2 second.2).symm

/-- The simplicial map representing horizontal composition of model 1- and
2-cells. -/
def horizontalCompositionNerveMap
    (A B C : ResourceModel.{u, v, w}) :
    CategoryTheory.nerve
        (ResourceModelHom A B × ResourceModelHom B C) ⟶
      MappingNerve A C :=
  CategoryTheory.nerveMap (horizontalCompositionFunctor A B C)

@[simp]
theorem horizontalCompositionNerveMap_vertex
    {A B C : ResourceModel.{u, v, w}}
    (F : ResourceModelHom A B) (G : ResourceModelHom B C) :
    (horizontalCompositionNerveMap A B C).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (F, G)) =
      ComposableArrows.mk₀ (F.comp G) :=
  CategoryTheory.nerveMap_app_mk₀ _ _

@[simp]
theorem horizontalCompositionNerveMap_transformation
    {A B C : ResourceModel.{u, v, w}}
    {F₁ F₂ : ResourceModelHom A B}
    {G₁ G₂ : ResourceModelHom B C}
    (eta : ResourceModelTransformation F₁ F₂)
    (theta : ResourceModelTransformation G₁ G₂) :
    (horizontalCompositionNerveMap A B C).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (show (F₁, G₁) ⟶ (F₂, G₂) from (eta, theta))) =
      ComposableArrows.mk₁
        (ResourceModelTransformation.horizontalComp eta theta) :=
  CategoryTheory.nerveMap_app_mk₁ _ _

/-! ## Associative and unital local-nerve coherence -/

/-- Compose a triple of local 1-cells by first composing the first two.
This functor acts on arbitrary triples of 2-cells by horizontal composition. -/
def leftAssociatedCompositionFunctor
    (A B C D : ResourceModel.{u, v, w}) :
    ((ResourceModelHom A B × ResourceModelHom B C) × ResourceModelHom C D) ⥤
      ResourceModelHom A D :=
  (horizontalCompositionFunctor A B C).prod (𝟭 (ResourceModelHom C D)) ⋙
    horizontalCompositionFunctor A C D

/-- Compose a triple of local 1-cells by first composing the last two.  The
product associator makes its source literally equal to that of
`leftAssociatedCompositionFunctor`. -/
def rightAssociatedCompositionFunctor
    (A B C D : ResourceModel.{u, v, w}) :
    ((ResourceModelHom A B × ResourceModelHom B C) × ResourceModelHom C D) ⥤
      ResourceModelHom A D :=
  CategoryTheory.prod.associator
      (ResourceModelHom A B) (ResourceModelHom B C) (ResourceModelHom C D) ⋙
    (𝟭 (ResourceModelHom A B)).prod (horizontalCompositionFunctor B C D) ⋙
      horizontalCompositionFunctor A B D

/-- The bicategorical associator is natural in all three local 1-cells, hence
forms a natural isomorphism between the two triple-composition functors. -/
noncomputable def horizontalAssociatorNatIso
    (A B C D : ResourceModel.{u, v, w}) :
    leftAssociatedCompositionFunctor A B C D ≅
      rightAssociatedCompositionFunctor A B C D :=
  NatIso.ofComponents
    (fun triple => by
      change (triple.1.1.comp triple.1.2).comp triple.2 ≅
        triple.1.1.comp (triple.1.2.comp triple.2)
      exact CategoryTheory.Bicategory.associator
        (B := ResourceModel.{u, v, w})
        triple.1.1 triple.1.2 triple.2)
    (fun {X Y} transformation => by
      rcases transformation with ⟨⟨first, second⟩, third⟩
      change
        ResourceModelTransformation.horizontalComp
              (ResourceModelTransformation.horizontalComp first second) third ≫
            (CategoryTheory.Bicategory.associator
              (B := ResourceModel.{u, v, w}) Y.1.1 Y.1.2 Y.2).hom =
          (CategoryTheory.Bicategory.associator
              (B := ResourceModel.{u, v, w}) X.1.1 X.1.2 X.2).hom ≫
            ResourceModelTransformation.horizontalComp first
              (ResourceModelTransformation.horizontalComp second third)
      simp only [ResourceModelTransformation.horizontalComp]
      apply ResourceModelTransformation.ext
      ext object
      simp)

/-- The natural associator gives an actual simplicial homotopy between the
two nerve maps for triple horizontal composition. -/
noncomputable def horizontalAssociatorNerveHomotopy
    (A B C D : ResourceModel.{u, v, w}) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (leftAssociatedCompositionFunctor A B C D))
      (CategoryTheory.nerveMap (rightAssociatedCompositionFunctor A B C D)) :=
  CategoryTheory.NerveHomotopy.ofNatTrans
    (horizontalAssociatorNatIso A B C D).hom

/-- Horizontal composition with the identity 1-cell on the left. -/
def leftUnitCompositionFunctor
    (A B : ResourceModel.{u, v, w}) :
    ResourceModelHom A B ⥤ ResourceModelHom A B :=
  ((Functor.const (ResourceModelHom A B)).obj (𝟙 A)).prod'
      (𝟭 (ResourceModelHom A B)) ⋙
    horizontalCompositionFunctor A A B

/-- Horizontal composition with the identity 1-cell on the right. -/
def rightUnitCompositionFunctor
    (A B : ResourceModel.{u, v, w}) :
    ResourceModelHom A B ⥤ ResourceModelHom A B :=
  (𝟭 (ResourceModelHom A B)).prod'
      ((Functor.const (ResourceModelHom A B)).obj (𝟙 B)) ⋙
    horizontalCompositionFunctor A B B

/-- The bicategorical left unitor, natural in every local 1- and 2-cell. -/
noncomputable def horizontalLeftUnitorNatIso
    (A B : ResourceModel.{u, v, w}) :
    leftUnitCompositionFunctor A B ≅ 𝟭 (ResourceModelHom A B) :=
  NatIso.ofComponents
    (fun F => by
      change (ResourceModelHom.id A).comp F ≅ F
      exact CategoryTheory.Bicategory.leftUnitor
        (B := ResourceModel.{u, v, w}) F)
    (fun {F G} transformation => by
      change
        ResourceModelTransformation.horizontalComp
              (𝟙 (𝟙 A)) transformation ≫
            (CategoryTheory.Bicategory.leftUnitor
              (B := ResourceModel.{u, v, w}) G).hom =
          (CategoryTheory.Bicategory.leftUnitor
              (B := ResourceModel.{u, v, w}) F).hom ≫ transformation
      simp only [ResourceModelTransformation.horizontalComp]
      apply ResourceModelTransformation.ext
      ext object
      simp)

/-- The bicategorical right unitor, natural in every local 1- and 2-cell. -/
noncomputable def horizontalRightUnitorNatIso
    (A B : ResourceModel.{u, v, w}) :
    rightUnitCompositionFunctor A B ≅ 𝟭 (ResourceModelHom A B) :=
  NatIso.ofComponents
    (fun F => by
      change F.comp (ResourceModelHom.id B) ≅ F
      exact CategoryTheory.Bicategory.rightUnitor
        (B := ResourceModel.{u, v, w}) F)
    (fun {F G} transformation => by
      change
        ResourceModelTransformation.horizontalComp transformation
              (𝟙 (𝟙 B)) ≫
            (CategoryTheory.Bicategory.rightUnitor
              (B := ResourceModel.{u, v, w}) G).hom =
          (CategoryTheory.Bicategory.rightUnitor
              (B := ResourceModel.{u, v, w}) F).hom ≫ transformation
      simp only [ResourceModelTransformation.horizontalComp]
      apply ResourceModelTransformation.ext
      ext object
      simp)

/-- The nerve of an identity local functor is literally the identity
simplicial map. -/
theorem mappingNerveMapId (A B : ResourceModel.{u, v, w}) :
    CategoryTheory.nerveMap (𝟭 (ResourceModelHom A B)) =
      𝟙 (MappingNerve A B) := by
  ext degree simplex
  rfl

/-- The left unitor supplies a genuine simplicial homotopy from composition
with the left identity to the identity map of the full local nerve. -/
noncomputable def horizontalLeftUnitorNerveHomotopy
    (A B : ResourceModel.{u, v, w}) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (leftUnitCompositionFunctor A B))
      (𝟙 (MappingNerve A B)) := by
  rw [← mappingNerveMapId A B]
  exact CategoryTheory.NerveHomotopy.ofNatTrans
    (horizontalLeftUnitorNatIso A B).hom

/-- The right unitor supplies a genuine simplicial homotopy from composition
with the right identity to the identity map of the full local nerve. -/
noncomputable def horizontalRightUnitorNerveHomotopy
    (A B : ResourceModel.{u, v, w}) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (rightUnitCompositionFunctor A B))
      (𝟙 (MappingNerve A B)) := by
  rw [← mappingNerveMapId A B]
  exact CategoryTheory.NerveHomotopy.ofNatTrans
    (horizontalRightUnitorNatIso A B).hom

end TotalModelSimplicial

end Ript.Higher
