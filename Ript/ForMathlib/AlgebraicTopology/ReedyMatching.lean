import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Functor

/-!
# Boundary matching objects for simplicial mapping diagrams

For a simplicial mapping diagram `n ↦ Map(Δ[n], X)`, its degree-`n`
matching object is `Map(∂Δ[n], X)` and the matching map is restriction along
the boundary inclusion.  When `X` is Kan, the simplicial model structure makes
that restriction a fibration.

This file also identifies `nerve (Fin (n + 1) ⥤ C)` with
`Map(Δ[n], nerve C)`.  The universe lift in Mathlib's standard-simplex nerve
presentation requires an explicit isomorphism of functor categories; keeping
that bridge here makes the construction reusable and auditable.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open CategoryTheory.Limits
open scoped SSet.modelCategoryQuillen

noncomputable section

universe u

namespace SSet

/-- The concrete degree-`n` matching object of the mapping diagram represented
by a simplicial set `X`. -/
def BoundaryMatchingObject (X : SSet.{u}) (n : ℕ) : SSet.{u} :=
  (ihom (∂Δ[n] : SSet.{u})).obj X

/-- Restriction of a simplex-valued map to the boundary of the standard
simplex.  This is the matching map for `n ↦ Map(Δ[n], X)`. -/
def boundaryMatchingMap (X : SSet.{u}) (n : ℕ) :
    (ihom (Δ[n] : SSet.{u})).obj X ⟶ BoundaryMatchingObject X n :=
  (MonoidalClosed.pre (boundary.{u} n).ι).app X

/-- Boundary restriction into a Kan complex is a fibration.  This is the
pushout-product/model-category input needed for Reedy fibrancy of simplicial
mapping diagrams. -/
theorem boundaryMatchingMap_fibration (X : SSet.{u}) [KanComplex X] (n : ℕ) :
    Fibration (boundaryMatchingMap X n) := by
  exact (by infer_instance :
    Fibration ((MonoidalClosed.pre (boundary.{u} n).ι).app X))

/-- The outer simplicial mapping-space diagram represented by `X`.  A
morphism of finite ordinals acts by precomposition on the representing
standard simplex. -/
def simplexMappingDiagram (X : SSet.{u}) : SimplicialObject SSet.{u} :=
  SSet.stdSimplex.{u}.op ⋙ MonoidalClosed.internalHom ⋙
    (evaluation SSet SSet).obj X

@[simp]
theorem simplexMappingDiagram_obj (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) :
    (simplexMappingDiagram X).obj n =
      (ihom (SSet.stdSimplex.obj n.unop)).obj X :=
  rfl

@[simp]
theorem simplexMappingDiagram_map (X : SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (simplexMappingDiagram X).map f =
      (MonoidalClosed.pre (SSet.stdSimplex.map f.unop)).app X :=
  rfl

/-- The indexing category of the representable boundary presentation.  Its
objects are simplices of `∂Δ[n]`; the double opposite is the orientation
obtained by turning the density colimit into a matching limit. -/
abbrev BoundaryMatchingIndex (n : ℕ) :=
  (((boundary.{u} n : SSet.{u}).Elements)ᵒᵖ)ᵒᵖ

/-- Forget a boundary simplex to the outer simplex degree on which it lives.
The two explicit `unop`s remove the double-opposite indexing wrapper without
relying on definitional equality of category instances. -/
def boundaryMatchingIndexProjection (n : ℕ) :
    BoundaryMatchingIndex.{u} n ⥤ SimplexCategoryᵒᵖ where
  obj j := (CategoryOfElements.π
    (boundary.{u} n : SSet.{u})).obj j.unop.unop
  map f := (CategoryOfElements.π
    (boundary.{u} n : SSet.{u})).map f.unop.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical morphism of boundary elements induced by applying one
simplicial structure map to a boundary simplex. -/
def boundaryMatchingIndexMap (n : ℕ)
    {Δ Γ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ)
    (s : (boundary.{u} n : SSet.{u}).obj Δ) :
    (Opposite.op (Opposite.op
      (⟨Δ, s⟩ : (boundary.{u} n : SSet.{u}).Elements)) :
        BoundaryMatchingIndex.{u} n) ⟶
      (Opposite.op (Opposite.op
        (⟨Γ, (boundary.{u} n : SSet.{u}).map f s⟩ :
          (boundary.{u} n : SSet.{u}).Elements)) :
            BoundaryMatchingIndex.{u} n) :=
  (CategoryOfElements.homMk
    (⟨Δ, s⟩ : (boundary.{u} n : SSet.{u}).Elements)
    (⟨Γ, (boundary.{u} n : SSet.{u}).map f s⟩ :
      (boundary.{u} n : SSet.{u}).Elements) f rfl).op.op

@[simp]
theorem boundaryMatchingIndexMap_val (n : ℕ)
    {Δ Γ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ)
    (s : (boundary.{u} n : SSet.{u}).obj Δ) :
    (boundaryMatchingIndexMap n f s).unop.unop.val = f :=
  rfl

/-- The simplex of `Δ[n]` represented by an object of the boundary matching
index, obtained by forgetting the proof that it lies in `∂Δ[n]`. -/
def boundaryMatchingSimplex (n : ℕ) (j : BoundaryMatchingIndex.{u} n) :
    j.unop.unop.fst.unop ⟶ SimplexCategory.mk n :=
  SSet.stdSimplex.objEquiv
    ((boundary.{u} n).ι.app j.unop.unop.fst j.unop.unop.snd)

/-- A simplex represented by the boundary matching index is non-surjective. -/
theorem boundaryMatchingSimplex_not_surjective (n : ℕ)
    (j : BoundaryMatchingIndex.{u} n) :
    ¬ Function.Surjective (boundaryMatchingSimplex n j) := by
  exact j.unop.unop.snd.property

/-- The object of the degree-two boundary matching index represented by the
`i`th nondegenerate edge `δ i : Δ[1] → Δ[2]`. -/
def degreeTwoBoundaryFaceElement (i : Fin 3) :
    BoundaryMatchingIndex.{u} 2 :=
  Opposite.op (Opposite.op
    ⟨Opposite.op (SimplexCategory.mk 1),
      ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i), by
        rw [SSet.boundary_obj_eq_univ 1 2]
        simp⟩⟩)

/-- Forgetting the boundary-membership proof of the canonical face element
recovers the corresponding coface map. -/
@[simp]
theorem boundaryMatchingSimplex_degreeTwoBoundaryFaceElement (i : Fin 3) :
    boundaryMatchingSimplex 2 (degreeTwoBoundaryFaceElement.{u} i) =
      SimplexCategory.δ i := by
  change SSet.stdSimplex.objEquiv.{u}
    (SSet.stdSimplex.objEquiv.{u}.symm (SimplexCategory.δ i)) = _
  exact Equiv.apply_symm_apply _ _

/-- The object of the degree-two boundary matching index represented by the
vertex `r : Fin 3`. -/
def degreeTwoBoundaryVertexElement (r : Fin 3) :
    BoundaryMatchingIndex.{u} 2 :=
  Opposite.op (Opposite.op
    ⟨Opposite.op (SimplexCategory.mk 0),
      ⟨SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk 2) r), by
        rw [SSet.boundary_obj_eq_univ 0 2]
        simp⟩⟩)

/-- Forgetting the boundary-membership proof of a canonical vertex recovers
the corresponding constant simplex. -/
@[simp]
theorem boundaryMatchingSimplex_degreeTwoBoundaryVertexElement (r : Fin 3) :
    boundaryMatchingSimplex 2 (degreeTwoBoundaryVertexElement.{u} r) =
      SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 2) r := by
  change SSet.stdSimplex.objEquiv.{u}
    (SSet.stdSimplex.objEquiv.{u}.symm
      (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 2) r)) = _
  exact Equiv.apply_symm_apply _ _

/-- Incidence morphism from a canonical edge of the degree-two boundary to
one of its two endpoints. -/
def degreeTwoBoundaryFaceToVertex (i : Fin 3) (t : Fin 2) :
    degreeTwoBoundaryFaceElement.{u} i ⟶
      degreeTwoBoundaryVertexElement.{u} ((SimplexCategory.δ i) t) := by
  let face := (degreeTwoBoundaryFaceElement.{u} i).unop.unop
  let vertex :=
    (degreeTwoBoundaryVertexElement.{u} ((SimplexCategory.δ i) t)).unop.unop
  let g : face.fst ⟶ vertex.fst :=
    (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk 1) t).op
  let e : face ⟶ vertex := CategoryOfElements.homMk face vertex g (by
    apply Subtype.ext
    change (SSet.stdSimplex.obj (SimplexCategory.mk 2)).map g
        (SSet.stdSimplex.objEquiv.{u}.symm (SimplexCategory.δ i)) =
      SSet.stdSimplex.objEquiv.{u}.symm
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk 2) ((SimplexCategory.δ i) t))
    rw [SSet.stdSimplex.map_apply]
    apply SSet.stdSimplex.objEquiv.{u}.injective
    apply SimplexCategory.Hom.ext
    ext x
    fin_cases x
    rfl)
  exact e.op.op

/-- Morphisms in the boundary element category express precomposition of the
represented boundary simplices. -/
theorem boundaryMatchingSimplex_naturality (n : ℕ)
    {j k : BoundaryMatchingIndex.{u} n} (f : j ⟶ k) :
    f.unop.unop.val.unop ≫ boundaryMatchingSimplex n j =
      boundaryMatchingSimplex n k := by
  apply SSet.stdSimplex.objEquiv.symm.injective
  dsimp [boundaryMatchingSimplex]
  rw [Equiv.symm_apply_apply, ← SSet.stdSimplex.map_apply]
  rw [← NatTrans.naturality_apply (boundary.{u} n).ι
    f.unop.unop.val j.unop.unop.snd]
  rw [CategoryOfElements.map_snd f.unop.unop]

/-- The abstract Reedy boundary-matching diagram of an arbitrary simplicial
space.  An object is a simplex of `∂Δ[n]`; its underlying simplex degree
selects the corresponding outer level of `W`.  The double opposite gives the
covariant orientation required for a matching limit. -/
def simplicialSpaceBoundaryMatchingDiagram
    (W : SimplicialObject SSet.{u}) (n : ℕ) :
    BoundaryMatchingIndex.{u} n ⥤ SSet.{u} :=
  boundaryMatchingIndexProjection n ⋙ W

/-- The abstract degree-`n` Reedy matching object of an arbitrary simplicial
space, defined as the limit over all simplices of the standard boundary. -/
noncomputable abbrev SimplicialSpaceBoundaryMatchingObject
    (W : SimplicialObject SSet.{u}) (n : ℕ) : SSet.{u} :=
  limit (simplicialSpaceBoundaryMatchingDiagram W n)

/-- The selected limiting cone defining the abstract Reedy matching object. -/
noncomputable def simplicialSpaceBoundaryMatchingCone
    (W : SimplicialObject SSet.{u}) (n : ℕ) :
    Cone (simplicialSpaceBoundaryMatchingDiagram W n) :=
  limit.cone _

/-- The abstract boundary-matching cone satisfies its genuine categorical
limit universal property. -/
noncomputable def simplicialSpaceBoundaryMatchingConeIsLimit
    (W : SimplicialObject SSet.{u}) (n : ℕ) :
    IsLimit (simplicialSpaceBoundaryMatchingCone W n) :=
  limit.isLimit _

/-- The cone obtained by restricting an outer `n`-simplex along every simplex
of `∂Δ[n]`. -/
def simplicialSpaceBoundaryRestrictionCone
    (W : SimplicialObject SSet.{u}) (n : ℕ) :
    Cone (simplicialSpaceBoundaryMatchingDiagram W n) where
  pt := W.obj (Opposite.op (SimplexCategory.mk n))
  π := {
    app j := W.map (boundaryMatchingSimplex n j).op
    naturality := by
      intro j k f
      dsimp [simplicialSpaceBoundaryMatchingDiagram,
        boundaryMatchingIndexProjection]
      change 𝟙 _ ≫ W.map (boundaryMatchingSimplex n k).op =
        W.map (boundaryMatchingSimplex n j).op ≫
          W.map f.unop.unop.val
      rw [Category.id_comp, ← W.map_comp]
      apply congrArg W.map
      have h := congrArg Quiver.Hom.op
        (boundaryMatchingSimplex_naturality n f)
      simpa using h.symm }

/-- The genuine abstract Reedy matching map of an arbitrary simplicial space,
defined as the universal lift of its boundary restriction cone. -/
noncomputable def simplicialSpaceBoundaryMatchingMap
    (W : SimplicialObject SSet.{u}) (n : ℕ) :
    W.obj (Opposite.op (SimplexCategory.mk n)) ⟶
      SimplicialSpaceBoundaryMatchingObject W n :=
  (simplicialSpaceBoundaryMatchingConeIsLimit W n).lift
    (simplicialSpaceBoundaryRestrictionCone W n)

/-- The abstract matching map is definitionally the universal map into the
selected boundary matching limit. -/
theorem simplicialSpaceBoundaryMatchingMap_eq_limitLift
    (W : SimplicialObject SSet.{u}) (n : ℕ) :
    (simplicialSpaceBoundaryMatchingConeIsLimit W n).lift
        (simplicialSpaceBoundaryRestrictionCone W n) =
      simplicialSpaceBoundaryMatchingMap W n :=
  rfl

/-- The genuine boundary matching diagram, indexed by all simplices of the
boundary and valued in their represented mapping spaces. -/
def boundaryMatchingDiagram (X : SSet.{u}) (n : ℕ) :
    BoundaryMatchingIndex.{u} n ⥤ SSet.{u} :=
  (CategoryTheory.Presheaf.functorToRepresentables
      (boundary.{u} n : SSet.{u})).op ⋙
    MonoidalClosed.internalHom.flip.obj X

/-- The canonical cone from maps out of the boundary to maps out of every
representable boundary simplex. -/
noncomputable def boundaryMatchingCone (X : SSet.{u}) (n : ℕ) :
    Cone (boundaryMatchingDiagram X n) :=
  (MonoidalClosed.internalHom.flip.obj X).mapCone
    (CategoryTheory.Presheaf.coconeOfRepresentable
      (boundary.{u} n : SSet.{u})).op

/-- The canonical boundary matching cone is limiting.  This is the abstract
matching-object universal property: presheaf density presents the boundary as
a colimit of representables, and the contravariant internal Hom turns that
colimit into a limit. -/
noncomputable def boundaryMatchingConeIsLimit (X : SSet.{u}) (n : ℕ) :
    IsLimit (boundaryMatchingCone X n) :=
  isLimitOfPreserves (MonoidalClosed.internalHom.flip.obj X)
    (IsColimit.op (CategoryTheory.Presheaf.colimitOfRepresentable
      (boundary.{u} n : SSet.{u})))

@[simp]
theorem boundaryMatchingCone_pt (X : SSet.{u}) (n : ℕ) :
    (boundaryMatchingCone X n).pt = BoundaryMatchingObject X n :=
  rfl

/-- The cone obtained by restricting maps on the standard simplex to every
simplex of its boundary. -/
noncomputable def boundaryRestrictionCone (X : SSet.{u}) (n : ℕ) :
    Cone (boundaryMatchingDiagram X n) :=
  (boundaryMatchingCone X n).extend (boundaryMatchingMap X n)

/-- The concrete boundary restriction is exactly the universal morphism into
the boundary matching limit. -/
theorem boundaryMatchingMap_eq_limitLift (X : SSet.{u}) (n : ℕ) :
    (boundaryMatchingConeIsLimit X n).lift (boundaryRestrictionCone X n) =
      boundaryMatchingMap X n := by
  symm
  exact (boundaryMatchingConeIsLimit X n).uniq
    (boundaryRestrictionCone X n) (boundaryMatchingMap X n) (fun _ ↦ rfl)

/-- An isomorphism in the contravariant argument of internal Hom induces an
isomorphism of internal-Hom functors. -/
def internalHomPreIso {A B : SSet.{u}} (e : A ≅ B) : ihom B ≅ ihom A where
  hom := MonoidalClosed.pre e.hom
  inv := MonoidalClosed.pre e.inv
  hom_inv_id := by
    rw [← MonoidalClosed.pre_map, e.inv_hom_id, MonoidalClosed.pre_id]
  inv_hom_id := by
    rw [← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id]

end SSet

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- In the cartesian closed category of categories, the abstract internal-Hom
precomposition map is the ordinary functor-category precomposition functor.
The closed structure is defined through an adjunction, so this equality is
proved by uncurrying rather than by reflexivity. -/
theorem cat_pre_eq_whiskeringLeft
    {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (f : Cat.of B ⟶ Cat.of A) :
    (MonoidalClosed.pre f).app (Cat.of C) =
      ((Functor.whiskeringLeft B A C).obj f.toFunctor).toCatHom := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre]
  rfl

/-- The finite ordinal underlying a simplex, lifted into the ambient
universe.  The explicit definition makes its action strictly transparent
enough to prove naturality of functor-category universe lifting. -/
def uliftSimplexCategoryToCat : SimplexCategory ⥤ Cat.{u, u} where
  obj n := Cat.of (ULift.{u} (Fin (n.len + 1)))
  map := fun {n m} f ↦
    ({ obj := fun X ↦ ULift.up (f.toOrderHom X.down)
       map := fun g ↦ homOfLE (f.toOrderHom.monotone g.down.down)
       map_id := by intros; apply Subsingleton.elim
       map_comp := by intros; apply Subsingleton.elim } :
      ULift.{u} (Fin (n.len + 1)) ⥤
        ULift.{u} (Fin (m.len + 1))).toCatHom
  map_id n := by
    apply Cat.Hom.ext
    refine Functor.ext (fun X ↦ ?_) ?_
    · cases X
      rfl
    · intros X Y g
      apply ULift.ext
      apply Subsingleton.elim
  map_comp f g := by
    apply Cat.Hom.ext
    refine Functor.ext (fun X ↦ ?_) ?_
    · cases X
      rfl
    · intros X Y h
      apply ULift.ext
      apply Subsingleton.elim

@[simp]
theorem uliftSimplexCategoryToCat_obj (n : SimplexCategory) :
    (uliftSimplexCategoryToCat.{u}).obj n =
      Cat.of (ULift.{u} (Fin (n.len + 1))) :=
  rfl

/-- The lifted string-category diagram, built functorially from internal Hom
in `Cat`. -/
def uliftFunctorClassifyingDiagramCat (C : Type u) [Category.{u} C] :
    SimplicialObject Cat.{u, u} :=
  uliftSimplexCategoryToCat.{u}.op ⋙ MonoidalClosed.internalHom ⋙
    (evaluation Cat Cat).obj (Cat.of C)

/-- The finite ordinal and its universe lift are equivalent as their preorder
categories, even though their hom types live in different universes. -/
def finULiftPreorderEquivalence (n : ℕ) :
    @CategoryTheory.Equivalence.{0, u, 0, u}
      (Fin (n + 1)) (ULift.{u} (Fin (n + 1)))
      (by infer_instance) (by infer_instance) where
  functor :=
    { obj := ULift.up
      map := fun f ↦ homOfLE f.down.down
      map_id := by intros; apply Subsingleton.elim
      map_comp := by intros; apply Subsingleton.elim }
  inverse :=
    { obj := ULift.down
      map := fun f ↦ homOfLE f.down.down
      map_id := by intros; apply Subsingleton.elim
      map_comp := by intros; apply Subsingleton.elim }
  unitIso := NatIso.ofComponents
    (fun _ ↦ eqToIso rfl)
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun X ↦ eqToIso (ULift.ext _ _ rfl))
    (fun _ ↦ Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem functorFinULift_roundtrip_left
    (C : Type u) [Category.{u} C] (n : ℕ) (F : Fin (n + 1) ⥤ C) :
    (finULiftPreorderEquivalence.{u} n).congrLeft.inverse.obj
        ((finULiftPreorderEquivalence.{u} n).congrLeft.functor.obj F) = F := by
  refine Functor.ext (fun _ ↦ rfl) ?_
  intros X Y f
  dsimp [Equivalence.congrLeft, finULiftPreorderEquivalence]
  simp only [Category.comp_id, Category.id_comp]
  exact congrArg F.map (Subsingleton.elim _ f)

set_option backward.isDefEq.respectTransparency false in
private theorem functorFinULift_roundtrip_right
    (C : Type u) [Category.{u} C] (n : ℕ)
    (F : ULift.{u} (Fin (n + 1)) ⥤ C) :
    (finULiftPreorderEquivalence.{u} n).congrLeft.functor.obj
        ((finULiftPreorderEquivalence.{u} n).congrLeft.inverse.obj F) = F := by
  refine Functor.ext (fun X ↦ by cases X; rfl) ?_
  intros X Y f
  dsimp [Equivalence.congrLeft, finULiftPreorderEquivalence]
  simp only [Category.comp_id, Category.id_comp]
  exact congrArg F.map (Subsingleton.elim _ f)

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition along the finite-ordinal universe lift is a strict
isomorphism in `Cat`, not merely an equivalence of categories. -/
def functorFinULiftIso (C : Type u) [Category.{u} C] (n : ℕ) :
    Cat.of (Fin (n + 1) ⥤ C) ≅
      Cat.of (ULift.{u} (Fin (n + 1)) ⥤ C) := by
  let e := finULiftPreorderEquivalence.{u} n
  exact Cat.isoOfEquiv e.congrLeft
    (functorFinULift_roundtrip_left C n)
    (functorFinULift_roundtrip_right C n)
    (fun F ↦ by
      change ((finULiftPreorderEquivalence.{u} n).funInvIdAssoc F).inv = 𝟙 _
      apply NatTrans.ext
      funext X
      rw [Equivalence.funInvIdAssoc_inv_app]
      change F.map (𝟙 X) = 𝟙 (F.obj X)
      simp)
    (fun F ↦ by
      change ((finULiftPreorderEquivalence.{u} n).invFunIdAssoc F).hom = 𝟙 _
      apply NatTrans.ext
      funext X
      rw [Equivalence.invFunIdAssoc_hom_app]
      cases X
      change F.map (𝟙 _) = 𝟙 _
      simp)

/-- The simplicial category of finite strings in `C`. -/
def functorClassifyingDiagramCat (C : Type u) [Category.{u} C] :
    SimplicialObject Cat where
  obj Δ := Cat.of (ComposableArrows C Δ.unop.len)
  map f := (ComposableArrows.whiskerLeftFunctor
    (SimplexCategory.toCat.map f.unop).toFunctor).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The bisimplicial nerve of finite strings in a category. -/
def functorClassifyingDiagram (C : Type u) [Category.{u} C] :
    SimplicialObject SSet :=
  functorClassifyingDiagramCat C ⋙ nerveFunctor

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition along `Fin → ULift Fin` is natural in every simplex
morphism, not only an equivalence separately in each degree. -/
noncomputable def functorClassifyingDiagramCatUliftIso
    (C : Type u) [Category.{u} C] :
    functorClassifyingDiagramCat C ≅ uliftFunctorClassifyingDiagramCat C :=
  NatIso.ofComponents
    (fun Δ ↦ functorFinULiftIso C Δ.unop.len)
    (fun {n m} f ↦ by
      dsimp [uliftFunctorClassifyingDiagramCat]
      change _ = _ ≫ (MonoidalClosed.pre
        (uliftSimplexCategoryToCat.map f.unop)).app (Cat.of C)
      rw [cat_pre_eq_whiskeringLeft
        (uliftSimplexCategoryToCat.map f.unop)]
      apply Cat.Hom.ext
      refine Functor.ext (fun F ↦ ?_) ?_
      · refine Functor.ext (fun X ↦ ?_) ?_
        · cases X
          rfl
        · intros X Y g
          dsimp [functorClassifyingDiagramCat,
            uliftSimplexCategoryToCat, functorFinULiftIso,
            Equivalence.congrLeft, finULiftPreorderEquivalence]
          simp only [Category.comp_id, Category.id_comp]
          exact congrArg F.map (Subsingleton.elim _ _)
      · intros F G η
        apply NatTrans.ext
        funext X
        dsimp [functorClassifyingDiagramCat, functorFinULiftIso,
          Equivalence.congrLeft, finULiftPreorderEquivalence]
        simp only [Category.comp_id, Category.id_comp]
        rfl)

end CategoryTheory

namespace SSet

local instance : MonoidalClosedFunctor CategoryTheory.nerveFunctor.{u, u} :=
  CategoryTheory.cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
    CategoryTheory.nerveFunctor.{u, u} CategoryTheory.nerveAdjunction.{u}

/-- The nerve of a functor category out of Mathlib's lifted finite ordinal is
the internal Hom from the corresponding standard simplex. -/
def nerveFunctorInternalHomIso (C : Type u) [Category.{u} C] (n : ℕ) :
    CategoryTheory.nerve (ULift.{u} (Fin (n + 1)) ⥤ C) ≅
      (ihom (Δ[n] : SSet.{u})).obj (CategoryTheory.nerve C) := by
  let e := asIso (expComparison CategoryTheory.nerveFunctor.{u, u}
    (Cat.of (ULift.{u} (Fin (n + 1))))).natTrans
  exact e.app (Cat.of C) ≪≫
    (internalHomPreIso (stdSimplex.isoNerve.{u} n)).app
      (CategoryTheory.nerve C)

/-- Degree `n` of the categorical classifying diagram is the simplicial
mapping space from `Δ[n]` into the nerve. -/
def nerveFunctorSimplexMappingIso (C : Type u) [Category.{u} C] (n : ℕ) :
    CategoryTheory.nerve (Fin (n + 1) ⥤ C) ≅
      (ihom (Δ[n] : SSet.{u})).obj (CategoryTheory.nerve C) :=
  CategoryTheory.nerveFunctor.mapIso
      (CategoryTheory.functorFinULiftIso C n) ≪≫
    nerveFunctorInternalHomIso C n

/-- Mapping spaces whose representing simplex is the nerve of the lifted
finite ordinal. -/
def uliftNerveSimplexMappingDiagram (X : SSet.{u}) :
    SimplicialObject SSet.{u} :=
  CategoryTheory.uliftSimplexCategoryToCat.{u}.op ⋙
    CategoryTheory.nerveFunctor.op ⋙ MonoidalClosed.internalHom ⋙
      (evaluation SSet SSet).obj X

/-- The closed-nerve comparison is natural in the lifted finite ordinal. -/
noncomputable def uliftFunctorClassifyingDiagramNerveIso
    (C : Type u) [Category.{u} C] :
    CategoryTheory.uliftFunctorClassifyingDiagramCat C ⋙
        CategoryTheory.nerveFunctor ≅
      uliftNerveSimplexMappingDiagram (CategoryTheory.nerve C) :=
  NatIso.ofComponents
    (fun Δ ↦ (asIso (CategoryTheory.expComparison
      CategoryTheory.nerveFunctor.{u, u}
      ((CategoryTheory.uliftSimplexCategoryToCat.{u}).obj Δ.unop)).natTrans).app
        (Cat.of C))
    (fun {n m} f ↦ by
      have h := CategoryTheory.expComparison_whiskerLeft
        CategoryTheory.nerveFunctor.{u, u}
        ((CategoryTheory.uliftSimplexCategoryToCat.{u}).map f.unop)
      have h' := congrArg (fun w ↦ w.natTrans.app (Cat.of C)) h
      change
        ((CategoryTheory.expComparison CategoryTheory.nerveFunctor.{u, u}
            ((CategoryTheory.uliftSimplexCategoryToCat.{u}).obj m.unop)).whiskerTop
          (MonoidalClosed.pre
            ((CategoryTheory.uliftSimplexCategoryToCat.{u}).map f.unop))).natTrans.app
              (Cat.of C) =
        ((CategoryTheory.expComparison CategoryTheory.nerveFunctor.{u, u}
            ((CategoryTheory.uliftSimplexCategoryToCat.{u}).obj n.unop)).whiskerBottom
          (MonoidalClosed.pre (CategoryTheory.nerveFunctor.map
            ((CategoryTheory.uliftSimplexCategoryToCat.{u}).map f.unop)))).natTrans.app
              (Cat.of C)
      exact h'.symm)

/-- The standard simplex is naturally the nerve of the lifted finite ordinal. -/
noncomputable def stdSimplexUliftNerveIso :
    SSet.stdSimplex.{u} ≅
      CategoryTheory.uliftSimplexCategoryToCat.{u} ⋙
        CategoryTheory.nerveFunctor :=
  NatIso.ofComponents
    (fun Δ ↦ SSet.stdSimplex.isoNerve.{u} Δ.len)
    (fun {n m} f ↦ by
      ext d F
      rfl)

/-- Replacing the lifted ordinal nerve by the standard simplex is natural in
the represented mapping-space diagram. -/
noncomputable def uliftNerveSimplexMappingDiagramIso (X : SSet.{u}) :
    uliftNerveSimplexMappingDiagram X ≅ simplexMappingDiagram X :=
  NatIso.ofComponents
    (fun Δ ↦ (internalHomPreIso
      ((stdSimplexUliftNerveIso.{u}).app Δ.unop)).app X)
    (fun {n m} f ↦ by
      change
        (MonoidalClosed.pre (CategoryTheory.nerveFunctor.map
          ((CategoryTheory.uliftSimplexCategoryToCat.{u}).map f.unop))).app X ≫
            (MonoidalClosed.pre
              ((stdSimplexUliftNerveIso.{u}).hom.app m.unop)).app X =
          (MonoidalClosed.pre
              ((stdSimplexUliftNerveIso.{u}).hom.app n.unop)).app X ≫
            (MonoidalClosed.pre (SSet.stdSimplex.map f.unop)).app X
      rw [← NatTrans.comp_app, ← NatTrans.comp_app,
        ← MonoidalClosed.pre_map, ← MonoidalClosed.pre_map,
        (stdSimplexUliftNerveIso.{u}).hom.naturality f.unop]
      rfl)

/-- The classifying diagram of strings in `C` is naturally the simplicial
mapping-space diagram represented by the categorical nerve of `C`. -/
noncomputable def functorClassifyingDiagramMappingIso
    (C : Type u) [Category.{u} C] :
    CategoryTheory.functorClassifyingDiagram C ≅
      simplexMappingDiagram (CategoryTheory.nerve C) :=
  CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.functorClassifyingDiagramCatUliftIso C)
      CategoryTheory.nerveFunctor ≪≫
    uliftFunctorClassifyingDiagramNerveIso C ≪≫
    uliftNerveSimplexMappingDiagramIso (CategoryTheory.nerve C)

/-- A project-local, fully explicit Reedy-fibrancy witness for a simplicial
object naturally presented as `n ↦ Map(Δ[n], X)` with `X` Kan.  Mathlib does
not yet package the Reedy model structure, so this structure records precisely
the presentation from which the genuine matching limits and matching-map
fibrations below are derived. -/
structure BoundaryReedyFibrant (W : SimplicialObject SSet.{u}) where
  /-- The Kan complex represented by the outer mapping diagram. -/
  representingObject : SSet.{u}
  /-- Natural, rather than merely degreewise, mapping-space presentation. -/
  presentation : W ≅ simplexMappingDiagram representingObject
  /-- Fibrancy of the representing simplicial set. -/
  kanComplex : KanComplex representingObject

namespace BoundaryReedyFibrant

variable {W : SimplicialObject SSet.{u}} (h : BoundaryReedyFibrant W)

/-- The degree-`n` matching object associated to a boundary Reedy witness. -/
abbrev matchingObject (n : ℕ) : SSet.{u} :=
  BoundaryMatchingObject h.representingObject n

/-- The genuine degree-`n` matching cone. -/
noncomputable def matchingCone (n : ℕ) :
    Cone (boundaryMatchingDiagram h.representingObject n) :=
  boundaryMatchingCone h.representingObject n

/-- The matching cone satisfies its universal property. -/
noncomputable def matchingConeIsLimit (n : ℕ) :
    IsLimit (h.matchingCone n) :=
  boundaryMatchingConeIsLimit h.representingObject n

/-- The matching map, transported through the natural mapping-space
presentation. -/
noncomputable def matchingMap (n : ℕ) :
    W.obj (Opposite.op (SimplexCategory.mk n)) ⟶ h.matchingObject n :=
  (h.presentation.app (Opposite.op (SimplexCategory.mk n))).hom ≫
    boundaryMatchingMap h.representingObject n

/-- The source cone whose universal map is the transported matching map. -/
noncomputable def restrictionCone (n : ℕ) :
    Cone (boundaryMatchingDiagram h.representingObject n) :=
  (boundaryRestrictionCone h.representingObject n).extend
    (h.presentation.app (Opposite.op (SimplexCategory.mk n))).hom

/-- The transported matching map is exactly the universal lift into the
matching limit. -/
theorem matchingMap_eq_limitLift (n : ℕ) :
    (h.matchingConeIsLimit n).lift (h.restrictionCone n) = h.matchingMap n := by
  symm
  exact (h.matchingConeIsLimit n).uniq
    (h.restrictionCone n) (h.matchingMap n) (fun _ ↦ rfl)

/-- Every matching map of a represented Kan mapping diagram is a fibration. -/
theorem matchingMap_fibration (n : ℕ) : Fibration (h.matchingMap n) := by
  change Fibration
    ((h.presentation.app (Opposite.op (SimplexCategory.mk n))).hom ≫
      boundaryMatchingMap h.representingObject n)
  rw [fibration_iff]
  apply (fibrations SSet).comp_mem
  · rw [← fibration_iff]
    infer_instance
  · exact (fibration_iff (boundaryMatchingMap h.representingObject n)).mp
      (@boundaryMatchingMap_fibration h.representingObject h.kanComplex n)

end BoundaryReedyFibrant

end SSet
