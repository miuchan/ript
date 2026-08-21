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

namespace SimplicialObject.Homotopy

universe u'

variable {X Y : SSet.{u'}} {f g : X ⟶ Y}

/-- The simplex in the target of a combinatorial simplicial homotopy indexed
by one nondegenerate simplex in the standard prism triangulation. -/
noncomputable def prismSimplex
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    Y.obj (op ⦋n + 1⦌) :=
  (H.h i).hom' x

/-- The first face of the first prism simplex is the target map. -/
@[simp]
theorem prismSimplex_zero_face_zero
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    (Y.δ 0).hom' (prismSimplex H x 0) =
      (g.app (op ⦋n⦌)).hom' x := by
  exact ConcreteCategory.congr_hom (H.h_zero_comp_δ_zero n) x

/-- The last face of the last prism simplex is the source map. -/
@[simp]
theorem prismSimplex_last_face_last
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    (Y.δ (Fin.last (n + 1))).hom'
        (prismSimplex H x (Fin.last n)) =
      (f.app (op ⦋n⦌)).hom' x := by
  exact ConcreteCategory.congr_hom (H.h_last_comp_δ_last n) x

/-- Faces before the switching vertex are the corresponding prism simplices
on source faces. -/
@[simp]
theorem prismSimplex_succ_face_castSucc_of_le
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (x : X.obj (op ⦋n + 1⦌)) :
    (Y.δ i.castSucc).hom' (prismSimplex H x j.succ) =
      prismSimplex H ((X.δ i).hom' x) j := by
  exact ConcreteCategory.congr_hom
    (H.h_succ_comp_δ_castSucc_of_lt i j hij) x

/-- Adjacent prism simplices share their switching face exactly. -/
@[simp]
theorem prismSimplex_succ_face_middle
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (j : Fin (n + 1)) (x : X.obj (op ⦋n + 1⦌)) :
    (Y.δ j.castSucc.succ).hom' (prismSimplex H x j.succ) =
      (Y.δ j.castSucc.succ).hom'
        (prismSimplex H x j.castSucc) := by
  exact ConcreteCategory.congr_hom
    (H.h_succ_comp_δ_castSucc_succ j) x

/-- Faces after the switching vertex are the corresponding prism simplices
on source faces. -/
@[simp]
theorem prismSimplex_castSucc_face_succ_of_lt
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (x : X.obj (op ⦋n + 1⦌)) :
    (Y.δ i.succ).hom' (prismSimplex H x j.castSucc) =
      prismSimplex H ((X.δ i).hom' x) j := by
  exact ConcreteCategory.congr_hom
    (H.h_castSucc_comp_δ_succ_of_lt i j hji) x

/-- Degeneracies at or before the switching vertex move to the successor
prism index. -/
@[simp]
theorem prismSimplex_degeneracy_castSucc_of_le
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j)
    (x : X.obj (op ⦋n⦌)) :
    (Y.σ i.castSucc).hom' (prismSimplex H x j) =
      prismSimplex H ((X.σ i).hom' x) j.succ := by
  exact ConcreteCategory.congr_hom
    (H.h_comp_σ_castSucc_of_le i j hij) x

/-- Degeneracies at or after the switching vertex retain the cast prism
index. -/
@[simp]
theorem prismSimplex_degeneracy_succ_of_le
    (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i)
    (x : X.obj (op ⦋n⦌)) :
    (Y.σ i.succ).hom' (prismSimplex H x j) =
      prismSimplex H ((X.σ i).hom' x) j.castSucc := by
  exact ConcreteCategory.congr_hom
    (H.h_comp_σ_succ_of_lt i j hji) x

end SimplicialObject.Homotopy

end CategoryTheory

open CategoryTheory Simplicial Opposite

namespace SSet.Homotopy

universe u'

variable {X Y : SSet.{u'}} {f g : X ⟶ Y}

/-- A simplex of an `SSet.Homotopy` in the standard simplicial prism
triangulation. -/
noncomputable def prismSimplex (H : SSet.Homotopy f g)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    Y.obj (op ⦋n + 1⦌) :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex
    H.toSimplicialObjectHomotopy x i

end SSet.Homotopy

namespace CategoryTheory.NerveHomotopy

universe u v

variable {C D : Type max u v} [Category.{v} C] [Category.{v} D]
variable {F G : C ⥤ D}

/-- Before the switching vertex, the prism of a nerve homotopy induced by a
natural transformation has the corresponding source-functor object. -/
theorem ofNatTrans_prismSimplex_obj_castSucc_of_le
    (alpha : F ⟶ G) {n : ℕ} (x : ComposableArrows C n)
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    (SSet.Homotopy.prismSimplex (ofNatTrans alpha) x i).obj j.castSucc =
      F.obj (x.obj j) := by
  let sourceDegeneracy := ((CategoryTheory.nerve C).σ i).hom' x
  let intervalSimplex :=
    ((SSet.stdSimplex.isoNerve 1).hom.app (op ⦋n + 1⦌)
      (SSet.stdSimplex.objMk₁ i.succ.castSucc)) ⋙
        intervalProjection.{u, v}
  change ((sourceDegeneracy.prod' intervalSimplex) ⋙
    cylinderFunctor alpha).obj j.castSucc = F.obj (x.obj j)
  have hSource : sourceDegeneracy.obj j.castSucc = x.obj j := by
    dsimp [sourceDegeneracy]
    change x.obj (i.predAbove j.castSucc) = x.obj j
    rw [Fin.predAbove_of_le_castSucc i j.castSucc
      (Fin.castSucc_le_castSucc_iff.mpr hji)]
    rfl
  have hInterval :
      intervalSimplex.obj j.castSucc = ULift.up (0 : Fin 2) := by
    change ULift.up
      ((SSet.stdSimplex.objMk₁.{max u v} i.succ.castSucc) j.castSucc) = _
    rw [SSet.stdSimplex.objMk₁_of_castSucc_lt]
    simpa using Fin.castSucc_lt_succ_iff.mpr hji
  change (cylinderFunctor alpha).obj
    (sourceDegeneracy.obj j.castSucc, intervalSimplex.obj j.castSucc) = _
  rw [hSource, hInterval]
  rfl

/-- After the switching vertex, the prism of a nerve homotopy induced by a
natural transformation has the corresponding target-functor object. -/
theorem ofNatTrans_prismSimplex_obj_succ_of_le
    (alpha : F ⟶ G) {n : ℕ} (x : ComposableArrows C n)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (SSet.Homotopy.prismSimplex (ofNatTrans alpha) x i).obj j.succ =
      G.obj (x.obj j) := by
  let sourceDegeneracy := ((CategoryTheory.nerve C).σ i).hom' x
  let intervalSimplex :=
    ((SSet.stdSimplex.isoNerve 1).hom.app (op ⦋n + 1⦌)
      (SSet.stdSimplex.objMk₁ i.succ.castSucc)) ⋙
        intervalProjection.{u, v}
  change ((sourceDegeneracy.prod' intervalSimplex) ⋙
    cylinderFunctor alpha).obj j.succ = G.obj (x.obj j)
  have hSource : sourceDegeneracy.obj j.succ = x.obj j := by
    dsimp [sourceDegeneracy]
    change x.obj (i.predAbove j.succ) = x.obj j
    rw [Fin.predAbove_of_castSucc_lt i j.succ
      (Fin.castSucc_lt_succ_iff.mpr hij), Fin.pred_succ]
  have hInterval :
      intervalSimplex.obj j.succ = ULift.up (1 : Fin 2) := by
    change ULift.up
      ((SSet.stdSimplex.objMk₁.{max u v} i.succ.castSucc) j.succ) = _
    rw [SSet.stdSimplex.objMk₁_of_le_castSucc]
    simpa using Fin.succ_le_succ_iff.mpr hij
  change (cylinderFunctor alpha).obj
    (sourceDegeneracy.obj j.succ, intervalSimplex.obj j.succ) = _
  rw [hSource, hInterval]
  rfl

end CategoryTheory.NerveHomotopy

namespace SSet.Homotopy

universe u'

variable {X Y : SSet.{u'}} {f g : X ⟶ Y}

/-- Every vertex of one standard prism simplex lies either before the
switching edge as a cast source index, or after it as a successor source
index. The two alternatives overlap exactly at the switching source vertex. -/
theorem prismVertex_castSucc_or_succ {n : ℕ}
    (i : Fin (n + 1)) (k : Fin (n + 2)) :
    (∃ j : Fin (n + 1), j ≤ i ∧ k = j.castSucc) ∨
      ∃ j : Fin (n + 1), i ≤ j ∧ k = j.succ := by
  by_cases hki : k ≤ i.castSucc
  · left
    have hkLast : k ≠ Fin.last (n + 1) :=
      Fin.ne_last_of_lt (lt_of_le_of_lt hki i.castSucc_lt_last)
    let j := k.castPred hkLast
    refine ⟨j, ?_, ?_⟩
    · apply Fin.castSucc_le_castSucc_iff.mp
      simpa [j] using hki
    · exact (Fin.castSucc_castPred k hkLast).symm
  · right
    have hik : i.castSucc < k := lt_of_not_ge hki
    have hkZero : k ≠ 0 :=
      Fin.ne_zero_of_lt (lt_of_le_of_lt (Fin.zero_le i.castSucc) hik)
    let j := k.pred hkZero
    refine ⟨j, ?_, ?_⟩
    · apply (Fin.le_pred_iff hkZero).2
      exact Fin.castSucc_lt_iff_succ_le.mp hik
    · exact (Fin.succ_pred k hkZero).symm

@[simp]
theorem prismSimplex_zero_face_zero (H : SSet.Homotopy f g)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    (Y.δ 0).hom' (prismSimplex H x 0) =
      (g.app (op ⦋n⦌)).hom' x :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_zero_face_zero
    H.toSimplicialObjectHomotopy x

@[simp]
theorem prismSimplex_last_face_last (H : SSet.Homotopy f g)
    {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    (Y.δ (Fin.last (n + 1))).hom'
        (prismSimplex H x (Fin.last n)) =
      (f.app (op ⦋n⦌)).hom' x :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_last_face_last
    H.toSimplicialObjectHomotopy x

@[simp]
theorem prismSimplex_succ_face_castSucc_of_le
    (H : SSet.Homotopy f g)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (x : X.obj (op ⦋n + 1⦌)) :
    (Y.δ i.castSucc).hom' (prismSimplex H x j.succ) =
      prismSimplex H ((X.δ i).hom' x) j :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_succ_face_castSucc_of_le
    H.toSimplicialObjectHomotopy i j hij x

@[simp]
theorem prismSimplex_succ_face_middle
    (H : SSet.Homotopy f g)
    {n : ℕ} (j : Fin (n + 1)) (x : X.obj (op ⦋n + 1⦌)) :
    (Y.δ j.castSucc.succ).hom' (prismSimplex H x j.succ) =
      (Y.δ j.castSucc.succ).hom'
        (prismSimplex H x j.castSucc) :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_succ_face_middle
    H.toSimplicialObjectHomotopy j x

@[simp]
theorem prismSimplex_castSucc_face_succ_of_lt
    (H : SSet.Homotopy f g)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (x : X.obj (op ⦋n + 1⦌)) :
    (Y.δ i.succ).hom' (prismSimplex H x j.castSucc) =
      prismSimplex H ((X.δ i).hom' x) j :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_castSucc_face_succ_of_lt
    H.toSimplicialObjectHomotopy i j hji x

@[simp]
theorem prismSimplex_degeneracy_castSucc_of_le
    (H : SSet.Homotopy f g)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j)
    (x : X.obj (op ⦋n⦌)) :
    (Y.σ i.castSucc).hom' (prismSimplex H x j) =
      prismSimplex H ((X.σ i).hom' x) j.succ :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_degeneracy_castSucc_of_le
    H.toSimplicialObjectHomotopy i j hij x

@[simp]
theorem prismSimplex_degeneracy_succ_of_le
    (H : SSet.Homotopy f g)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i)
    (x : X.obj (op ⦋n⦌)) :
    (Y.σ i.succ).hom' (prismSimplex H x j) =
      prismSimplex H ((X.σ i).hom' x) j.castSucc :=
  CategoryTheory.SimplicialObject.Homotopy.prismSimplex_degeneracy_succ_of_le
    H.toSimplicialObjectHomotopy i j hji x

/-- Complete all-degree coherence package for the standard simplicial prism
triangulation associated to an `SSet.Homotopy`. It records both endpoint
faces, both side-face families, shared switching faces, and both degeneracy
families in every simplicial degree. -/
def AllPrismCoherence (H : SSet.Homotopy f g) : Prop :=
  (∀ (n : ℕ) (x : X.obj (op ⦋n⦌)),
    (Y.δ 0).hom' (prismSimplex H x 0) =
      (g.app (op ⦋n⦌)).hom' x) ∧
  (∀ (n : ℕ) (x : X.obj (op ⦋n⦌)),
    (Y.δ (Fin.last (n + 1))).hom'
        (prismSimplex H x (Fin.last n)) =
      (f.app (op ⦋n⦌)).hom' x) ∧
  (∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
      (_hij : i ≤ j.castSucc) (x : X.obj (op ⦋n + 1⦌)),
    (Y.δ i.castSucc).hom' (prismSimplex H x j.succ) =
      prismSimplex H ((X.δ i).hom' x) j) ∧
  (∀ (n : ℕ) (j : Fin (n + 1)) (x : X.obj (op ⦋n + 1⦌)),
    (Y.δ j.castSucc.succ).hom' (prismSimplex H x j.succ) =
      (Y.δ j.castSucc.succ).hom'
        (prismSimplex H x j.castSucc)) ∧
  (∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
      (_hji : j.castSucc < i) (x : X.obj (op ⦋n + 1⦌)),
    (Y.δ i.succ).hom' (prismSimplex H x j.castSucc) =
      prismSimplex H ((X.δ i).hom' x) j) ∧
  (∀ (n : ℕ) (i j : Fin (n + 1)) (_hij : i ≤ j)
      (x : X.obj (op ⦋n⦌)),
    (Y.σ i.castSucc).hom' (prismSimplex H x j) =
      prismSimplex H ((X.σ i).hom' x) j.succ) ∧
  (∀ (n : ℕ) (i j : Fin (n + 1)) (_hji : j ≤ i)
      (x : X.obj (op ⦋n⦌)),
    (Y.σ i.succ).hom' (prismSimplex H x j) =
      prismSimplex H ((X.σ i).hom' x) j.castSucc)

/-- Every simplicial homotopy satisfies the complete all-degree prism
coherence package. -/
theorem allPrismCoherence (H : SSet.Homotopy f g) :
    AllPrismCoherence H := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact prismSimplex_zero_face_zero H x
  · intro n x
    exact prismSimplex_last_face_last H x
  · intro n i j hij x
    exact prismSimplex_succ_face_castSucc_of_le H i j hij x
  · intro n j x
    exact prismSimplex_succ_face_middle H j x
  · intro n i j hji x
    exact prismSimplex_castSucc_face_succ_of_lt H i j hji x
  · intro n i j hij x
    exact prismSimplex_degeneracy_castSucc_of_le H i j hij x
  · intro n i j hji x
    exact prismSimplex_degeneracy_succ_of_le H i j hji x

/-- Complete face package for the three tetrahedra triangulating a
degree-two simplicial homotopy prism. -/
def DegreeTwoPrismFaces (H : SSet.Homotopy f g)
    (x : X.obj (op ⦋2⦌)) : Prop :=
  (Y.δ 0).hom' (prismSimplex H x 0) =
      (g.app (op ⦋2⦌)).hom' x ∧
  (Y.δ (Fin.last 3)).hom'
      (prismSimplex H x (Fin.last 2)) =
      (f.app (op ⦋2⦌)).hom' x ∧
  (∀ j : Fin 2,
    (Y.δ j.castSucc.succ).hom' (prismSimplex H x j.succ) =
      (Y.δ j.castSucc.succ).hom'
        (prismSimplex H x j.castSucc)) ∧
  (∀ (i : Fin 3) (j : Fin 2) (_hij : i ≤ j.castSucc),
    (Y.δ i.castSucc).hom' (prismSimplex H x j.succ) =
      prismSimplex H ((X.δ i).hom' x) j) ∧
  (∀ (i : Fin 3) (j : Fin 2) (_hji : j.castSucc < i),
    (Y.δ i.succ).hom' (prismSimplex H x j.castSucc) =
      prismSimplex H ((X.δ i).hom' x) j)

/-- Every degree-two simplex has an explicit three-tetrahedron prism whose
twelve faces are identified by the standard homotopy equations. -/
theorem degreeTwoPrismFaces (H : SSet.Homotopy f g)
    (x : X.obj (op ⦋2⦌)) :
    DegreeTwoPrismFaces H x := by
  refine ⟨prismSimplex_zero_face_zero H x,
    prismSimplex_last_face_last H x, ?_, ?_, ?_⟩
  · intro j
    exact prismSimplex_succ_face_middle H j x
  · intro i j hij
    exact prismSimplex_succ_face_castSucc_of_le H i j hij x
  · intro i j hji
    exact prismSimplex_castSucc_face_succ_of_lt H i j hji x

end SSet.Homotopy

namespace CategoryTheory

universe u v

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
