import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
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

end SSet
