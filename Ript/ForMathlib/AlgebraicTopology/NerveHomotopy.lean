import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Natural transformations induce nerve homotopies

This file constructs the standard simplicial homotopy between the nerve maps
induced by two functors connected by a natural transformation.  Mathlib
provides the target notion `SSet.Homotopy`, but not the category-to-nerve
bridge used here.

The construction is explicit.  A natural transformation `F ⟶ G` is
uncurried to a functor on `C × [1]`; an `n`-simplex of `N(C) ⊗ Δ[1]`
is converted to a functor into that product and then evaluated in `D`.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory

open CategoryTheory.Functor
open Opposite Simplicial SSet MonoidalCategory

universe u v

namespace NerveHomotopy

variable {C D : Type max u v} [Category.{v} C] [Category.{v} D]
variable {F G : C ⥤ D}

private abbrev Interval := ULift.{v} (Fin 2)

private abbrev intervalDownFunctor : Interval.{v} ⥤ Fin 2 :=
  ULift.orderIso.monotone.functor

/-- Project the universe-sized simplicial interval to the hom-universe-sized
categorical interval used by the cylinder functor. -/
private abbrev intervalProjection :
    ULift.{max u v} (Fin 2) ⥤ Interval.{v} :=
  ULift.orderIso.monotone.functor ⋙
    ULift.orderIso.symm.monotone.functor

@[simp]
private lemma intervalDownFunctor_obj_up (i : Fin 2) :
    intervalDownFunctor.obj (ULift.up i) = i :=
  rfl

private lemma intervalDownFunctor_map_id (i : Fin 2) :
    intervalDownFunctor.map (𝟙 (ULift.up i)) = 𝟙 i := by
  simp

private def intervalDiagram (alpha : F ⟶ G) :
    Interval.{v} ⥤ (C ⥤ D) :=
  intervalDownFunctor ⋙ ComposableArrows.mk₁ alpha

@[simp]
private lemma mk₁_obj_zero (alpha : F ⟶ G) :
    (ComposableArrows.mk₁ alpha).obj 0 = F :=
  rfl

@[simp]
private lemma mk₁_obj_one (alpha : F ⟶ G) :
    (ComposableArrows.mk₁ alpha).obj 1 = G :=
  rfl

private def cylinderFunctor (alpha : F ⟶ G) :
    C × Interval.{v} ⥤ D :=
  Functor.uncurry.obj (intervalDiagram alpha).flip

private abbrev vertexFunctor (n : ℕ) (k : Fin 2) :
    Fin (n + 1) ⥤ Interval.{v} :=
  (Functor.const (Fin (n + 1))).obj (ULift.up k)

private lemma iotaZero_fst {Δ : SimplexCategoryᵒᵖ} (x : (nerve C).obj Δ) :
    ((SSet.ι₀.app Δ).hom' x).1 = x := by
  rfl

private lemma iotaOne_fst {Δ : SimplexCategoryᵒᵖ} (x : (nerve C).obj Δ) :
    ((SSet.ι₁.app Δ).hom' x).1 = x := by
  rfl

private lemma iotaZero_interval
    {Δ : SimplexCategoryᵒᵖ} (x : (nerve C).obj Δ) :
    (stdSimplex.isoNerve 1).hom.app Δ ((SSet.ι₀.app Δ).hom' x).2 ⋙
        intervalProjection.{u, v} =
      vertexFunctor Δ.unop.len 0 := by
  apply Functor.ext
  · intro i j f
    subsingleton
  · intro i
    rfl

private lemma iotaOne_interval
    {Δ : SimplexCategoryᵒᵖ} (x : (nerve C).obj Δ) :
    (stdSimplex.isoNerve 1).hom.app Δ ((SSet.ι₁.app Δ).hom' x).2 ⋙
        intervalProjection.{u, v} =
      vertexFunctor Δ.unop.len 1 := by
  apply Functor.ext
  · intro i j f
    subsingleton
  · intro i
    rfl

private lemma cylinder_zero
    {n : ℕ} (x : ComposableArrows C n) (alpha : F ⟶ G) :
    x.prod' (vertexFunctor n 0) ⋙ cylinderFunctor alpha = x ⋙ F := by
  exact Functor.ext (fun i ↦ rfl) (fun i j f ↦ by
    dsimp [cylinderFunctor, intervalDiagram, intervalDownFunctor, vertexFunctor]
    rw [intervalDownFunctor_map_id]
    simp
    generalize_proofs hEq
    cases Subsingleton.elim hEq rfl
    simp)

private lemma cylinder_one
    {n : ℕ} (x : ComposableArrows C n) (alpha : F ⟶ G) :
    x.prod' (vertexFunctor n 1) ⋙ cylinderFunctor alpha = x ⋙ G := by
  exact Functor.ext (fun i ↦ rfl) (fun i j f ↦ by
    dsimp [cylinderFunctor, intervalDiagram, intervalDownFunctor, vertexFunctor]
    rw [intervalDownFunctor_map_id]
    simp
    generalize_proofs hEq
    cases Subsingleton.elim hEq rfl
    simp)

/-- The categorical cylinder associated to a natural transformation, viewed
degreewise as a map from the nerve cylinder. -/
def nerveCylinder (alpha : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app Δ := ↾fun x ↦
    x.1.prod'
        ((stdSimplex.isoNerve 1).hom.app Δ x.2 ⋙
          intervalProjection.{u, v}) ⋙
      cylinderFunctor alpha
  naturality X Y f := by
    ext x
    rfl

/-- Every natural transformation induces an explicit simplicial homotopy
between the corresponding nerve maps. -/
noncomputable def ofNatTrans (alpha : F ⟶ G) :
    SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := nerveCylinder alpha
  h₀ := by
    ext Δ x
    change
      (((SSet.ι₀.app Δ).hom' x).1.prod'
        ((stdSimplex.isoNerve 1).hom.app Δ ((SSet.ι₀.app Δ).hom' x).2 ⋙
          intervalProjection.{u, v}) ⋙
          cylinderFunctor alpha) = x ⋙ F
    rw [iotaZero_fst, iotaZero_interval]
    exact cylinder_zero x alpha
  h₁ := by
    ext Δ x
    change
      (((SSet.ι₁.app Δ).hom' x).1.prod'
        ((stdSimplex.isoNerve 1).hom.app Δ ((SSet.ι₁.app Δ).hom' x).2 ⋙
          intervalProjection.{u, v}) ⋙
          cylinderFunctor alpha) = x ⋙ G
    rw [iotaOne_fst, iotaOne_interval]
    exact cylinder_one x alpha
  rel := by
    ext Δ x
    exact False.elim (by simpa using x.1.property)

end NerveHomotopy

/-- A categorical nerve map sends a canonical composable-pair 2-simplex to
the canonical 2-simplex of the two mapped arrows. -/
@[simp]
theorem nerveMap_app_mk₂
    {C D : Type max u v} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (nerveMap F).app (Opposite.op ⦋2⦌) (ComposableArrows.mk₂ f g) =
      ComposableArrows.mk₂ (F.map f) (F.map g) := by
  change (F.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g) = _
  refine ComposableArrows.ext₂
    (f := (F.mapComposableArrows 2).obj (ComposableArrows.mk₂ f g))
    (g := ComposableArrows.mk₂ (F.map f) (F.map g))
    rfl rfl rfl ?_ ?_
  · change F.map f = 𝟙 _ ≫ F.map f ≫ 𝟙 _
    simp
  · change F.map g = 𝟙 _ ≫ F.map g ≫ 𝟙 _
    simp

end CategoryTheory
