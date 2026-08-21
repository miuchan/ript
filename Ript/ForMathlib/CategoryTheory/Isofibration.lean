import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Core
import Ript.ForMathlib.AlgebraicTopology.GroupoidNerve

/-!
# Categorical isofibrations

This file supplies the strict object-and-isomorphism lifting interface needed
to prove that nerves of isofibrations between groupoids are Kan fibrations.
The lift records an on-the-nose target object equality, which is exactly the
extra datum required by a simplicial horn lift rather than a merely
essentially-surjective comparison.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Functor

section General

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A strict lift of a target-side isomorphism along a functor. -/
structure IsoLift (F : C ⥤ D) {X : C} {Y : D} (e : F.obj X ≅ Y) where
  /-- The lifted target object. -/
  obj : C
  /-- Its image is the requested target on the nose. -/
  obj_eq : F.obj obj = Y
  /-- The lifted isomorphism. -/
  iso : X ≅ obj
  /-- Mapping the lifted isomorphism recovers the requested isomorphism. -/
  map_iso_hom : F.map iso.hom = e.hom ≫ eqToHom obj_eq.symm

/-- A functor is an isofibration when every isomorphism out of an object in
its image has a strict object-and-isomorphism lift. -/
class IsIsofibration (F : C ⥤ D) : Prop where
  exists_isoLift :
    ∀ {X : C} {Y : D} (e : F.obj X ≅ Y), Nonempty (IsoLift F e)

instance isIsofibrationId : (Functor.id C).IsIsofibration where
  exists_isoLift {X Y} e := ⟨{
    obj := Y
    obj_eq := rfl
    iso := e
    map_iso_hom := by simp }⟩

instance coreInclusionIsIsofibration :
    (CategoryTheory.Core.inclusion C).IsIsofibration where
  exists_isoLift {X Y} e := ⟨{
    obj := ⟨Y⟩
    obj_eq := rfl
    iso := Core.isoMk e
    map_iso_hom := by
      change (Core.isoMk e).hom.iso.hom = e.hom ≫ eqToHom rfl
      rw [Core.isoMk_hom_iso]
      simp }⟩

instance isIsofibrationComp
    {E : Type u₃} [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.IsIsofibration] [G.IsIsofibration] : (F ⋙ G).IsIsofibration where
  exists_isoLift {X Z} e := by
    obtain ⟨lg⟩ := IsIsofibration.exists_isoLift (F := G) e
    obtain ⟨lf⟩ := IsIsofibration.exists_isoLift (F := F) lg.iso
    let h : (F ⋙ G).obj lf.obj = Z :=
      (congrArg G.obj lf.obj_eq).trans lg.obj_eq
    exact ⟨{
      obj := lf.obj
      obj_eq := h
      iso := lf.iso
      map_iso_hom := by
        rw [Functor.comp_map, lf.map_iso_hom, G.map_comp,
          lg.map_iso_hom]
        rw [Category.assoc, eqToHom_map, eqToHom_trans] }⟩

/-- Endpoint evaluation on the core of the walking-arrow category. -/
def coreArrowEndpoints :
    Core (ComposableArrows C 1) ⥤ Core C × Core C :=
  (((evaluation (Fin 2) C).obj 0).core).prod'
    (((evaluation (Fin 2) C).obj 1).core)

/-- Endpoint evaluation is a strict isofibration: conjugating an arrow by the
two requested endpoint isomorphisms constructs its lift. -/
instance coreArrowEndpointsIsIsofibration :
    (coreArrowEndpoints (C := C)).IsIsofibration where
  exists_isoLift {X Y} e := by
    let α₀ : X.of.obj 0 ≅ Y.1.of := e.hom.1.iso
    let α₁ : X.of.obj 1 ≅ Y.2.of := e.hom.2.iso
    let g : Y.1.of ⟶ Y.2.of := α₀.inv ≫ X.of.hom ≫ α₁.hom
    let X' : Core (ComposableArrows C 1) := ⟨ComposableArrows.mk₁ g⟩
    let η : X ≅ X' := Core.isoMk
      (ComposableArrows.isoMk₁ α₀ α₁ (by
        change X.of.hom ≫ α₁.hom = α₀.hom ≫ g
        simp only [g, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]))
    exact ⟨{
      obj := X'
      obj_eq := rfl
      iso := η
      map_iso_hom := by
        apply Prod.hom_ext
        · apply Core.hom_ext
          dsimp [coreArrowEndpoints, η, α₀, α₁]
          change α₀.hom = α₀.hom ≫ 𝟙 _
          simp
        · apply Core.hom_ext
          dsimp [coreArrowEndpoints, η, α₀, α₁]
          change α₁.hom = α₁.hom ≫ 𝟙 _
          simp }⟩

variable (F : C ⥤ D) [F.IsIsofibration]

/-- Chosen isomorphism lift. -/
noncomputable def isoLift {X : C} {Y : D} (e : F.obj X ≅ Y) :
    IsoLift F e :=
  (IsIsofibration.exists_isoLift e).some

@[simp]
theorem isoLift_map_hom {X : C} {Y : D} (e : F.obj X ≅ Y) :
    F.map (F.isoLift e).iso.hom =
      e.hom ≫ eqToHom (F.isoLift e).obj_eq.symm :=
  (F.isoLift e).map_iso_hom

/-- The chosen forward lift maps to the requested isomorphism, with only the
displayed target-object transport. -/
theorem exists_lift_iso_hom {X : C} {Y : D} (e : F.obj X ≅ Y) :
    ∃ (X' : C) (h : F.obj X' = Y) (f : X ≅ X'),
      F.map f.hom = e.hom ≫ eqToHom h.symm := by
  obtain ⟨l⟩ := IsIsofibration.exists_isoLift e
  exact ⟨l.obj, l.obj_eq, l.iso, l.map_iso_hom⟩

/-- Reversing a chosen lift gives the target-oriented edge-lifting formula. -/
theorem exists_lift_iso_inv {X : C} {Y : D} (e : Y ≅ F.obj X) :
    ∃ (X' : C) (h : F.obj X' = Y) (f : X' ≅ X),
      F.map f.hom = eqToHom h ≫ e.hom := by
  obtain ⟨l⟩ := IsIsofibration.exists_isoLift e.symm
  refine ⟨l.obj, l.obj_eq, l.iso.symm, ?_⟩
  rw [← cancel_mono (F.map l.iso.hom)]
  rw [show l.iso.symm.hom = l.iso.inv by rfl]
  rw [← F.map_comp, l.iso.inv_hom_id, F.map_id]
  simp [l.map_iso_hom, Category.assoc]

end General

section Nerve

universe v u

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (F : C ⥤ D) [F.IsIsofibration]

set_option backward.isDefEq.respectTransparency false in
/-- The forward lifted edge is sent by the nerve map to the requested edge,
up to the strict target equality stored in the lift. -/
theorem nerveMap_mk₁_isoLift {X : C} {Y : D} (e : F.obj X ≅ Y) :
    (CategoryTheory.nerveMap F).app (Opposite.op (SimplexCategory.mk 1))
        (ComposableArrows.mk₁ (F.isoLift e).iso.hom) =
      ComposableArrows.mk₁ e.hom := by
  rw [CategoryTheory.nerveMap_app_mk₁]
  refine ComposableArrows.ext₁ rfl (F.isoLift e).obj_eq ?_
  rw [← ComposableArrows.map'_eq_hom₁,
    ← ComposableArrows.map'_eq_hom₁]
  convert F.isoLift_map_hom e using 1 <;> simp

/-- One-dimensional relative horn lifting for the nerve map of an
isofibration between groupoids. -/
theorem nerveMap_hornOne_lift
    {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
    (F : C ⥤ D) [F.IsIsofibration]
    (i : Fin 2)
    (f : ∀ (j : Fin 2), j ≠ i → (Δ[0] ⟶ CategoryTheory.nerve C))
    (_hf : SSet.horn.IsCompatible f)
    (b : Δ[1] ⟶ CategoryTheory.nerve D)
    (comm : ∀ (j : Fin 2) (hj : j ≠ i),
      f j hj ≫ CategoryTheory.nerveMap F = SSet.stdSimplex.δ j ≫ b) :
    ∃ φ : Δ[1] ⟶ CategoryTheory.nerve C,
      (∀ (j : Fin 2) (hj : j ≠ i), SSet.stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ CategoryTheory.nerveMap F = b := by
  let β := SSet.yonedaEquiv b
  fin_cases i
  · let a := SSet.yonedaEquiv (f 1 (by simp))
    have hs : F.obj (a.obj 0) = β.obj 0 := by
      have hc := congrArg SSet.yonedaEquiv (comm 1 (by simp))
      rw [SSet.yonedaEquiv_comp,
        SSet.stdSimplex.yonedaEquiv_δ_comp] at hc
      change (F.mapComposableArrows 0).obj a = (nerve D).δ 1 β at hc
      exact congrArg (fun z ↦ z.obj 0) hc
    let e : F.obj (a.obj 0) ≅ β.obj 1 :=
      (eqToIso hs).trans (asIso β.hom)
    obtain ⟨X', ht, g, hg⟩ := F.exists_lift_iso_hom e
    let φ : Δ[1] ⟶ CategoryTheory.nerve C :=
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g.hom)
    refine ⟨φ, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · simp at hj
      · apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp]
        exact ComposableArrows.ext₀ rfl
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      change (CategoryTheory.nerveMap F).app (Opposite.op (SimplexCategory.mk 1))
          (ComposableArrows.mk₁ g.hom) = β
      rw [CategoryTheory.nerveMap_app_mk₁]
      refine ComposableArrows.ext₁ hs ht ?_
      rw [← ComposableArrows.map'_eq_hom₁
        (ComposableArrows.mk₁ (F.map g.hom)),
        ← ComposableArrows.map'_eq_hom₁ β]
      change F.map g.hom = eqToHom hs ≫
        β.map' 0 1 ≫ eqToHom ht.symm
      rw [ComposableArrows.map'_eq_hom₁ β]
      simpa [e] using hg
  · let a := SSet.yonedaEquiv (f 0 (by simp))
    have ht : F.obj (a.obj 0) = β.obj 1 := by
      have hc := congrArg SSet.yonedaEquiv (comm 0 (by simp))
      rw [SSet.yonedaEquiv_comp,
        SSet.stdSimplex.yonedaEquiv_δ_comp] at hc
      change (F.mapComposableArrows 0).obj a = (nerve D).δ 0 β at hc
      exact congrArg (fun z ↦ z.obj 0) hc
    let e : β.obj 0 ≅ F.obj (a.obj 0) :=
      (asIso β.hom).trans (eqToIso ht).symm
    obtain ⟨X', hs, g, hg⟩ := F.exists_lift_iso_inv e
    let φ : Δ[1] ⟶ CategoryTheory.nerve C :=
      SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g.hom)
    refine ⟨φ, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp]
        exact ComposableArrows.ext₀ rfl
      · simp at hj
    · apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      change (CategoryTheory.nerveMap F).app (Opposite.op (SimplexCategory.mk 1))
          (ComposableArrows.mk₁ g.hom) = β
      rw [CategoryTheory.nerveMap_app_mk₁]
      refine ComposableArrows.ext₁ hs ht ?_
      rw [← ComposableArrows.map'_eq_hom₁
        (ComposableArrows.mk₁ (F.map g.hom)),
        ← ComposableArrows.map'_eq_hom₁ β]
      change F.map g.hom = eqToHom hs ≫
        β.map' 0 1 ≫ eqToHom ht.symm
      rw [ComposableArrows.map'_eq_hom₁ β]
      simpa [e] using hg

/-- Two-dimensional relative horn lifting for the nerve map of an
isofibration between groupoids. -/
theorem nerveMap_hornTwo_lift
    {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
    (F : C ⥤ D)
    (i : Fin 3)
    (f : ∀ (j : Fin 3), j ≠ i → (Δ[1] ⟶ CategoryTheory.nerve C))
    (hf : SSet.horn.IsCompatible f)
    (b : Δ[2] ⟶ CategoryTheory.nerve D)
    (comm : ∀ (j : Fin 3) (hj : j ≠ i),
      f j hj ≫ CategoryTheory.nerveMap F = SSet.stdSimplex.δ j ≫ b) :
    ∃ φ : Δ[2] ⟶ CategoryTheory.nerve C,
      (∀ (j : Fin 3) (hj : j ≠ i), SSet.stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ CategoryTheory.nerveMap F = b := by
  let _ : SSet.KanComplex (CategoryTheory.nerve C) :=
    CategoryTheory.Nerve.kanComplex C
  obtain ⟨φ, hφ⟩ := hf.exists_lift_of_kanComplex
  refine ⟨φ, hφ, ?_⟩
  apply SSet.yonedaEquiv.injective
  apply CategoryTheory.Nerve.two_simplex_eq_of_faces_except i
  intro j hj
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp,
    ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, hφ j hj, comm j hj]

/-- Relative horn lifting in dimensions at least three.  The source Kan filler
has the prescribed target because categorical nerve horns are unique there. -/
theorem nerveMap_hornHigh_lift
    {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
    (F : C ⥤ D)
    {n : ℕ} (i : Fin (n + 4))
    (f : ∀ (j : Fin (n + 4)), j ≠ i →
      (Δ[n + 2] ⟶ CategoryTheory.nerve C))
    (hf : SSet.horn.IsCompatible f)
    (b : Δ[n + 3] ⟶ CategoryTheory.nerve D)
    (comm : ∀ (j : Fin (n + 4)) (hj : j ≠ i),
      f j hj ≫ CategoryTheory.nerveMap F = SSet.stdSimplex.δ j ≫ b) :
    ∃ φ : Δ[n + 3] ⟶ CategoryTheory.nerve C,
      (∀ (j : Fin (n + 4)) (hj : j ≠ i), SSet.stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ CategoryTheory.nerveMap F = b := by
  let _ : SSet.KanComplex (CategoryTheory.nerve C) :=
    CategoryTheory.Nerve.kanComplex C
  obtain ⟨φ, hφ⟩ := hf.exists_lift_of_kanComplex
  refine ⟨φ, hφ, ?_⟩
  apply SSet.yonedaEquiv.injective
  apply CategoryTheory.Nerve.simplex_eq_of_faces_except_high i
  intro j hj
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp,
    ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  apply congrArg SSet.yonedaEquiv
  rw [← Category.assoc, hφ j hj, comm j hj]

end Nerve

end Functor

end CategoryTheory

namespace SSet

open modelCategoryQuillen

universe u

/-- Family form of the horn right-lifting property defining a Kan fibration. -/
theorem fibration_iff_hornFamily {X Y : SSet.{u}} (p : X ⟶ Y) :
    Fibration p ↔
      ∀ {n : ℕ} {i : Fin (n + 2)}
        (f : ∀ (j : Fin (n + 2)), j ≠ i → (Δ[n] ⟶ X))
        (_hf : horn.IsCompatible f) (b : Δ[n + 1] ⟶ Y)
        (_comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
          f j hj ≫ p = stdSimplex.δ j ≫ b),
        ∃ φ : Δ[n + 1] ⟶ X,
          (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj) ∧
          φ ≫ p = b := by
  constructor
  · intro hp n i f hf b comm
    let _ : Fibration p := hp
    exact hf.exists_lift p b comm
  · intro h
    rw [modelCategoryQuillen.fibration_iff]
    intro A B q hq
    simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hq
    obtain ⟨n, ⟨i⟩⟩ := hq
    refine ⟨fun {t b} sq ↦ ?_⟩
    let hf := horn.IsCompatible.of_hom t
    have comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
        (horn.ι i j hj ≫ t) ≫ p = stdSimplex.δ j ≫ b := by
      intro j hj
      calc
        (horn.ι i j hj ≫ t) ≫ p =
            horn.ι i j hj ≫ (t ≫ p) := Category.assoc _ _ _
        _ = horn.ι i j hj ≫ (Λ[n + 1, i].ι ≫ b) := by rw [sq.w]
        _ = (horn.ι i j hj ≫ Λ[n + 1, i].ι) ≫ b :=
          (Category.assoc _ _ _).symm
        _ = stdSimplex.δ j ≫ b := by rw [horn.ι_ι]
    obtain ⟨φ, hφ, hp⟩ := h
      (fun j hj ↦ horn.ι i j hj ≫ t) hf b comm
    exact ⟨⟨{
      l := φ
      fac_left := horn.hom_ext' (fun j hj ↦ by
        rw [← Category.assoc, horn.ι_ι, hφ j hj])
      fac_right := hp }⟩⟩

end SSet

namespace CategoryTheory.Functor

universe v u

variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]

/-- The nerve map of an isofibration between groupoids is a Kan fibration. -/
theorem nerveMap_fibration (F : C ⥤ D) [F.IsIsofibration] :
    Fibration (CategoryTheory.nerveMap F) := by
  rw [SSet.fibration_iff_hornFamily]
  intro n i f hf b comm
  obtain _ | n := n
  · exact F.nerveMap_hornOne_lift i f hf b comm
  obtain _ | n := n
  · exact F.nerveMap_hornTwo_lift i f hf b comm
  · exact F.nerveMap_hornHigh_lift i f hf b comm

/-- In a universe-balanced category, the degree-one endpoint matching map is
a Kan fibration after taking nerves. -/
theorem nerveMap_coreArrowEndpoints_fibration
    (C : Type u) [Category.{u} C] :
    Fibration (CategoryTheory.nerveMap (coreArrowEndpoints (C := C))) :=
  nerveMap_fibration (coreArrowEndpoints (C := C))

end CategoryTheory.Functor
