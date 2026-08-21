import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# The nerve of a groupoid is a Kan complex

This file supplies a horn-filling theorem that is not available in the pinned
Mathlib revision.  It is kept under `Ript.ForMathlib` because the result and
most of its supporting lemmas are suitable candidates for upstreaming.

The proof separates the genuinely groupoidal part from the simplicial
bookkeeping:

* one-dimensional horns are filled by degenerate identity edges;
* two-dimensional outer horns are filled using inverse morphisms;
* three-dimensional outer horns use cancellation by an isomorphism;
* inner horns are filled by the strict-Segal quasicategory theorem; and
* horns of dimension at least four are reconstructed from their spines and
  consecutive two-simplices.

Thus no classical choice beyond the constructions already used by Mathlib's
horn-colimit API is hidden in the mathematical statement.
-/

set_option autoImplicit false

open CategoryTheory
open Simplicial
open SSet

namespace SSet.horn

open Finset
open Opposite
open SimplexCategory

universe u

/-- Every horn in dimension at least three contains the standard spine. -/
@[simps! vertex_coe arrow_coe]
def spineIdOfThree {d : ℕ} (i : Fin (d + 1)) (hd : 3 ≤ d) :
    Path (Λ[d, i] : SSet.{u}) d :=
  Λ[d, i].liftPath (stdSimplex.spineId d) (by
    intro j
    rw [horn_obj_eq_univ i 0 (by lia)]
    trivial) (fun j ↦ by
      convert! (horn.edge₃.{u} d i j.castSucc j.succ (by
        simp only [← Fin.val_fin_le, Fin.val_castSucc, Fin.val_succ,
          le_add_iff_nonneg_right, zero_le]) hd).2
      ext a
      fin_cases a <;> rfl)

/-- Including the horn spine into the standard simplex recovers the standard
spine exactly. -/
@[simp]
lemma spineIdOfThree_map_hornInclusion {d : ℕ} (i : Fin (d + 1)) (hd : 3 ≤ d) :
    Path.map (spineIdOfThree.{u} i hd) Λ[d, i].ι =
      stdSimplex.spineId d := rfl

/-- In dimension at least four, every triangle on three consecutive vertices
belongs to every horn. -/
@[simps]
def primitiveTriangleOfFour {d : ℕ} (i : Fin (d + 1)) (hd : 4 ≤ d)
    (k : ℕ) (hk : k + 2 ≤ d) : (Λ[d, i] : SSet.{u}) _⦋2⦌ := by
  let a : Fin (d + 1) := ⟨k, by lia⟩
  let b : Fin (d + 1) := ⟨k + 1, by lia⟩
  let c : Fin (d + 1) := ⟨k + 2, by lia⟩
  refine ⟨stdSimplex.triangle a b c (by simp [a, b]) (by simp [b, c]), ?_⟩
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion,
    stdSimplex.mem_face_iff, mem_compl, mem_singleton, exists_prop]
  have hS : ¬ ({i, a, b, c} : Finset (Fin (d + 1))) = Finset.univ := by
    intro hS
    have hcard := congrArg Finset.card hS
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have hle : ({i, a, b, c} : Finset (Fin (d + 1))).card ≤ 4 := by
      have h₀ := Finset.card_insert_le i ({a, b, c} : Finset (Fin (d + 1)))
      have h₁ := Finset.card_insert_le a ({b, c} : Finset (Fin (d + 1)))
      have h₂ := Finset.card_insert_le b ({c} : Finset (Fin (d + 1)))
      have h₃ : ({c} : Finset (Fin (d + 1))).card = 1 := by simp
      omega
    lia
  rw [Finset.eq_univ_iff_forall, not_forall] at hS
  obtain ⟨l, hl⟩ := hS
  simp only [mem_insert, mem_singleton, not_or] at hl
  refine ⟨l, hl.1, fun z ↦ ?_⟩
  fin_cases z
  · exact Ne.symm hl.2.1
  · exact Ne.symm hl.2.2.1
  · exact Ne.symm hl.2.2.2

end SSet.horn

namespace SSet.StrictSegal

open CategoryTheory
open SimplicialObject
open SimplexCategory

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Horns of dimension at least four fill in every strict Segal simplicial
set. -/
theorem hornFillerOfFour {X : SSet.{u}} (sx : StrictSegal X)
    {n : ℕ} {i : Fin (n + 5)}
    (σ₀ : (Λ[n + 4, i] : SSet) ⟶ X) :
    ∃ σ : X _⦋n + 4⦌,
      ∀ (j : Fin (n + 5)) (hj : j ≠ i),
        X.δ j σ = σ₀.app _ (horn.face i j hj) := by
  use sx.spineToSimplex <| Path.map (horn.spineIdOfThree i (by lia)) σ₀
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality]
  let ksucc := k.succ.castSucc
  obtain hlt | hgt | heq : ksucc < j ∨ j < ksucc ∨ j = ksucc := by lia
  · rw [← spine_arrow, spine_δ_arrow_lt sx _ hlt]
    dsimp only [Path.map_arrow, spine_arrow, Fin.coe_eq_castSucc]
    dsimp
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι,
      stdSimplex.map_apply, Quiver.Hom.unop_op, SSet.yonedaEquiv_map,
      Equiv.apply_symm_apply, mkOfSucc_δ_lt hlt]
    rfl
  · rw [← spine_arrow, spine_δ_arrow_gt sx _ hgt]
    dsimp
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι,
      stdSimplex.map_apply, Quiver.Hom.unop_op, SSet.yonedaEquiv_map,
      Equiv.apply_symm_apply, mkOfSucc_δ_gt hgt]
    rfl
  · let triangle : (Λ[n + 4, i] : SSet.{u}) _⦋2⦌ :=
      horn.primitiveTriangleOfFour i (by lia) k (by grind)
    have hi : ((horn.spineIdOfThree i (by lia)).map σ₀).interval k 2 (by grind) =
        X.spine 2 (σ₀.app _ triangle) := by
      ext m
      dsimp [spine_arrow, Path.map_interval, Path.map_arrow]
      rw [← dsimp% σ₀.naturality_apply]
      apply congr_arg
      apply Subtype.ext
      ext a : 1
      fin_cases a <;> fin_cases m <;> rfl
    rw [← spine_arrow, spine_δ_arrow_eq sx _ heq, hi]
    simp only [spineToDiagonal, diagonal, spineToSimplex_spine_apply]
    rw [← types_comp_apply (σ₀.app _) (X.map _), ← σ₀.naturality,
      types_comp_apply]
    dsimp
    apply congr_arg
    apply Subtype.ext
    ext z : 1
    dsimp [horn.face]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι,
      stdSimplex.map_apply, Quiver.Hom.unop_op, stdSimplex.map_apply,
      Quiver.Hom.unop_op]
    dsimp [CosimplicialObject.δ]
    rw [SSet.yonedaEquiv_map]
    simp only [Equiv.apply_symm_apply, triangle]
    rw [mkOfSucc_δ_eq heq]
    fin_cases z <;> rfl

end SSet.StrictSegal

namespace SSet

universe u

/-- The canonical inclusion of a horn into the full boundary of the same
standard simplex. -/
def hornToBoundary (n : ℕ) (i : Fin (n + 1)) :
    (Λ[n, i] : SSet.{u}) ⟶ (∂Δ[n] : SSet.{u}) :=
  Subcomplex.homOfLE (by
    rw [horn_eq_iSup, iSup_le_iff]
    intro j
    exact face_singleton_compl_le_boundary j.1)

/-- Every included horn face agrees with the corresponding canonical boundary
face. -/
theorem hornFaceToBoundary (n : ℕ) (i j : Fin (n + 2))
    (hj : j ≠ i) :
    horn.ι i j hj ≫ hornToBoundary (n + 1) i = boundary.ι j := by
  rw [← cancel_mono (boundary (n + 1)).ι]
  change horn.ι i j hj ≫ (horn (n + 1) i).ι = stdSimplex.δ j
  exact horn.ι_ι i j hj

end SSet

namespace CategoryTheory.Nerve

open SimplexCategory

universe v u

/-- A one-dimensional horn in a categorical nerve is filled by a degenerate
identity edge. -/
theorem hornFillerOne {C : Type u} [Groupoid.{v} C]
    {i : Fin 2} (f : ∀ (j : Fin 2), j ≠ i → (Δ[0] ⟶ nerve C)) :
    ∃ φ : Δ[1] ⟶ nerve C,
      ∀ (j : Fin 2) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  fin_cases i
  · let x := SSet.yonedaEquiv (f 1 (by simp))
    refine ⟨SSet.yonedaEquiv.symm ((nerve C).σ 0 x), ?_⟩
    intro j hj
    fin_cases j
    · simp at hj
    · apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      change (nerve C).δ 1 ((nerve C).σ 0 x) = x
      exact (nerve C).δ_comp_σ_succ_apply (0 : Fin 1) x
  · let x := SSet.yonedaEquiv (f 0 (by simp))
    refine ⟨SSet.yonedaEquiv.symm ((nerve C).σ 0 x), ?_⟩
    intro j hj
    fin_cases j
    · apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      change (nerve C).δ 0 ((nerve C).σ 0 x) = x
      exact (nerve C).δ_comp_σ_self_apply (0 : Fin 1) x
    · simp at hj

/-- Fill the zeroth two-dimensional outer horn using a groupoid inverse. -/
theorem hornFillerTwoZero {C : Type u} [Groupoid.{v} C]
    (f : ∀ (j : Fin 3), j ≠ (0 : Fin 3) → (Δ[1] ⟶ nerve C))
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[2] ⟶ nerve C,
      ∀ (j : Fin 3) (hj : j ≠ (0 : Fin 3)), stdSimplex.δ j ≫ φ = f j hj := by
  let a := SSet.yonedaEquiv (f 1 (by simp))
  let b := SSet.yonedaEquiv (f 2 (by simp))
  obtain ⟨A₀, A₂, h₀₂, ha⟩ := ComposableArrows.mk₁_surjective a
  obtain ⟨B₀, B₁, h₀₁, hb⟩ := ComposableArrows.mk₁_surjective b
  have hc := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (1 : Fin 3)) (k := (2 : Fin 3)))
  simp only [stdSimplex.yonedaEquiv_δ_comp] at hc
  change (nerve C).δ 1 a = (nerve C).δ 1 b at hc
  have hsource : A₀ = B₀ := by
    rw [ha, hb] at hc
    exact congrArg nerveEquiv hc
  subst B₀
  let σ := ComposableArrows.mk₂ h₀₁ (inv h₀₁ ≫ h₀₂)
  refine ⟨SSet.yonedaEquiv.symm σ, ?_⟩
  intro j hj
  fin_cases j
  · simp at hj
  · apply SSet.yonedaEquiv.injective
    change (nerve C).δ 1 σ = a
    rw [CategoryTheory.nerve.δ₁_mk₂_eq, ha]
    simp
    rfl
  · apply SSet.yonedaEquiv.injective
    change (nerve C).δ 2 σ = b
    rw [CategoryTheory.nerve.δ₂_mk₂_eq, hb]

/-- Fill the last two-dimensional outer horn using a groupoid inverse. -/
theorem hornFillerTwoLast {C : Type u} [Groupoid.{v} C]
    (f : ∀ (j : Fin 3), j ≠ (2 : Fin 3) → (Δ[1] ⟶ nerve C))
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[2] ⟶ nerve C,
      ∀ (j : Fin 3) (hj : j ≠ (2 : Fin 3)), stdSimplex.δ j ≫ φ = f j hj := by
  let a := SSet.yonedaEquiv (f 0 (by simp))
  let b := SSet.yonedaEquiv (f 1 (by simp))
  obtain ⟨A₁, A₂, h₁₂, ha⟩ := ComposableArrows.mk₁_surjective a
  obtain ⟨B₀, B₂, h₀₂, hb⟩ := ComposableArrows.mk₁_surjective b
  have hc := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (0 : Fin 3)) (k := (1 : Fin 3)))
  simp only [stdSimplex.yonedaEquiv_δ_comp] at hc
  change (nerve C).δ 0 a = (nerve C).δ 0 b at hc
  have htarget : A₂ = B₂ := by
    rw [ha, hb] at hc
    exact congrArg nerveEquiv hc
  subst B₂
  let σ := ComposableArrows.mk₂ (h₀₂ ≫ inv h₁₂) h₁₂
  refine ⟨SSet.yonedaEquiv.symm σ, ?_⟩
  intro j hj
  fin_cases j
  · apply SSet.yonedaEquiv.injective
    change (nerve C).δ 0 σ = a
    rw [CategoryTheory.nerve.δ₀_mk₂_eq, ha]
  · apply SSet.yonedaEquiv.injective
    change (nerve C).δ 1 σ = b
    rw [CategoryTheory.nerve.δ₁_mk₂_eq, hb]
    simp
    rfl
  · simp at hj

/-- Fill the zeroth three-dimensional outer horn by cancelling its first
groupoid edge. -/
theorem hornFillerThreeZero {C : Type u} [Groupoid.{v} C]
    (f : ∀ (j : Fin 4), j ≠ (0 : Fin 4) → (Δ[2] ⟶ nerve C))
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[3] ⟶ nerve C,
      ∀ (j : Fin 4) (hj : j ≠ (0 : Fin 4)), stdSimplex.δ j ≫ φ = f j hj := by
  let x₁ := SSet.yonedaEquiv (f 1 (by simp))
  let x₂ := SSet.yonedaEquiv (f 2 (by simp))
  let x₃ := SSet.yonedaEquiv (f 3 (by simp))
  obtain ⟨A₀, A₂, A₃, h₀₂, h₂₃, hx₁⟩ := ComposableArrows.mk₂_surjective x₁
  obtain ⟨B₀, B₁, B₃, h₀₁', h₁₃, hx₂⟩ := ComposableArrows.mk₂_surjective x₂
  obtain ⟨C₀, C₁, C₂, h₀₁, h₁₂, hx₃⟩ := ComposableArrows.mk₂_surjective x₃
  have hc₁₃ := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (1 : Fin 4)) (k := (3 : Fin 4)))
  have hc₂₃ := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (2 : Fin 4)) (k := (3 : Fin 4)))
  have hc₁₂ := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (1 : Fin 4)) (k := (2 : Fin 4)))
  simp only [stdSimplex.yonedaEquiv_δ_comp] at hc₁₃ hc₂₃ hc₁₂
  change (nerve C).δ 2 x₁ = (nerve C).δ 1 x₃ at hc₁₃
  change (nerve C).δ 2 x₂ = (nerve C).δ 2 x₃ at hc₂₃
  change (nerve C).δ 1 x₁ = (nerve C).δ 1 x₂ at hc₁₂
  rw [hx₁, hx₃, CategoryTheory.nerve.δ₂_mk₂_eq,
    CategoryTheory.nerve.δ₁_mk₂_eq] at hc₁₃
  rw [hx₂, hx₃, CategoryTheory.nerve.δ₂_mk₂_eq,
    CategoryTheory.nerve.δ₂_mk₂_eq] at hc₂₃
  rw [hx₁, hx₂, CategoryTheory.nerve.δ₁_mk₂_eq,
    CategoryTheory.nerve.δ₁_mk₂_eq] at hc₁₂
  have hA₀C₀ := congrArg (fun q ↦ q.obj 0) hc₁₃
  have hA₂C₂ := congrArg (fun q ↦ q.obj 1) hc₁₃
  have hB₀C₀ := congrArg (fun q ↦ q.obj 0) hc₂₃
  have hB₁C₁ := congrArg (fun q ↦ q.obj 1) hc₂₃
  have hA₃B₃ := congrArg (fun q ↦ q.obj 1) hc₁₂
  change A₀ = C₀ at hA₀C₀
  change A₂ = C₂ at hA₂C₂
  change B₀ = C₀ at hB₀C₀
  change B₁ = C₁ at hB₁C₁
  change A₃ = B₃ at hA₃B₃
  subst A₀
  subst A₂
  subst B₀
  subst B₁
  subst B₃
  have h02 : h₀₂ = h₀₁ ≫ h₁₂ := by
    rw [← Arrow.mk_inj]
    exact congrArg (fun q ↦ Arrow.mk q.hom) hc₁₃
  have h01 : h₀₁' = h₀₁ := by
    rw [← Arrow.mk_inj]
    exact congrArg (fun q ↦ Arrow.mk q.hom) hc₂₃
  have hcomp : h₀₂ ≫ h₂₃ = h₀₁' ≫ h₁₃ := by
    rw [← Arrow.mk_inj]
    exact congrArg (fun q ↦ Arrow.mk q.hom) hc₁₂
  have h13 : h₁₃ = h₁₂ ≫ h₂₃ := by
    rw [h02, h01, Category.assoc] at hcomp
    exact (cancel_epi h₀₁).1 hcomp.symm
  let σ := ComposableArrows.mk₃ h₀₁ h₁₂ h₂₃
  refine ⟨SSet.yonedaEquiv.symm σ, ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  fin_cases j
  · simp at hj
  · change (nerve C).δ 1 σ = x₁
    rw [hx₁, h02]
    apply ComposableArrows.ext₂_of_arrow <;> cat_disch
  · change (nerve C).δ 2 σ = x₂
    rw [hx₂, h01, h13]
    apply ComposableArrows.ext₂_of_arrow <;> cat_disch
  · change (nerve C).δ 3 σ = x₃
    rw [hx₃]
    apply ComposableArrows.ext₂_of_arrow <;> cat_disch

/-- Fill the last three-dimensional outer horn by cancelling its last
groupoid edge. -/
theorem hornFillerThreeLast {C : Type u} [Groupoid.{v} C]
    (f : ∀ (j : Fin 4), j ≠ (3 : Fin 4) → (Δ[2] ⟶ nerve C))
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[3] ⟶ nerve C,
      ∀ (j : Fin 4) (hj : j ≠ (3 : Fin 4)), stdSimplex.δ j ≫ φ = f j hj := by
  let x₀ := SSet.yonedaEquiv (f 0 (by simp))
  let x₁ := SSet.yonedaEquiv (f 1 (by simp))
  let x₂ := SSet.yonedaEquiv (f 2 (by simp))
  obtain ⟨A₁, A₂, A₃, h₁₂, h₂₃, hx₀⟩ := ComposableArrows.mk₂_surjective x₀
  obtain ⟨B₀, B₂, B₃, h₀₂, h₂₃', hx₁⟩ := ComposableArrows.mk₂_surjective x₁
  obtain ⟨C₀, C₁, C₃, h₀₁, h₁₃, hx₂⟩ := ComposableArrows.mk₂_surjective x₂
  have hc₀₁ := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (0 : Fin 4)) (k := (1 : Fin 4)))
  have hc₀₂ := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (0 : Fin 4)) (k := (2 : Fin 4)))
  have hc₁₂ := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (j := (1 : Fin 4)) (k := (2 : Fin 4)))
  simp only [stdSimplex.yonedaEquiv_δ_comp] at hc₀₁ hc₀₂ hc₁₂
  change (nerve C).δ 0 x₀ = (nerve C).δ 0 x₁ at hc₀₁
  change (nerve C).δ 1 x₀ = (nerve C).δ 0 x₂ at hc₀₂
  change (nerve C).δ 1 x₁ = (nerve C).δ 1 x₂ at hc₁₂
  rw [hx₀, hx₁, CategoryTheory.nerve.δ₀_mk₂_eq,
    CategoryTheory.nerve.δ₀_mk₂_eq] at hc₀₁
  rw [hx₀, hx₂, CategoryTheory.nerve.δ₁_mk₂_eq,
    CategoryTheory.nerve.δ₀_mk₂_eq] at hc₀₂
  rw [hx₁, hx₂, CategoryTheory.nerve.δ₁_mk₂_eq,
    CategoryTheory.nerve.δ₁_mk₂_eq] at hc₁₂
  have hA₂B₂ := congrArg (fun q ↦ q.obj 0) hc₀₁
  have hA₃B₃ := congrArg (fun q ↦ q.obj 1) hc₀₁
  have hA₁C₁ := congrArg (fun q ↦ q.obj 0) hc₀₂
  have hA₃C₃ := congrArg (fun q ↦ q.obj 1) hc₀₂
  have hB₀C₀ := congrArg (fun q ↦ q.obj 0) hc₁₂
  change A₂ = B₂ at hA₂B₂
  change A₃ = B₃ at hA₃B₃
  change A₁ = C₁ at hA₁C₁
  change A₃ = C₃ at hA₃C₃
  change B₀ = C₀ at hB₀C₀
  subst B₂
  subst B₃
  subst C₁
  subst C₃
  subst C₀
  have h23 : h₂₃ = h₂₃' := by
    rw [← Arrow.mk_inj]
    exact congrArg (fun q ↦ Arrow.mk q.hom) hc₀₁
  have h13 : h₁₂ ≫ h₂₃ = h₁₃ := by
    rw [← Arrow.mk_inj]
    exact congrArg (fun q ↦ Arrow.mk q.hom) hc₀₂
  have hcomp : h₀₂ ≫ h₂₃' = h₀₁ ≫ h₁₃ := by
    rw [← Arrow.mk_inj]
    exact congrArg (fun q ↦ Arrow.mk q.hom) hc₁₂
  have h02 : h₀₂ = h₀₁ ≫ h₁₂ := by
    rw [← h23, ← h13, ← Category.assoc] at hcomp
    exact (cancel_mono h₂₃).1 hcomp
  let σ := ComposableArrows.mk₃ h₀₁ h₁₂ h₂₃
  refine ⟨SSet.yonedaEquiv.symm σ, ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  fin_cases j
  · change (nerve C).δ 0 σ = x₀
    rw [hx₀]
    apply ComposableArrows.ext₂_of_arrow <;> cat_disch
  · change (nerve C).δ 1 σ = x₁
    rw [hx₁, h02, ← h23]
    apply ComposableArrows.ext₂_of_arrow <;> cat_disch
  · change (nerve C).δ 2 σ = x₂
    rw [hx₂, ← h13]
    apply ComposableArrows.ext₂_of_arrow <;> cat_disch
  · simp at hj

/-- Fill an inner horn in a categorical nerve using its strict-Segal
quasicategory structure. -/
theorem hornFillerInner {C : Type u} [Category.{v} C]
    {n : ℕ} {i : Fin (n + 2)} (h₀ : 0 < i) (hₙ : i < Fin.last (n + 1))
    (f : ∀ (j : Fin (n + 2)), j ≠ i → (Δ[n] ⟶ nerve C))
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[n + 1] ⟶ nerve C,
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  let _ : SSet.Quasicategory (nerve C) :=
    SSet.StrictSegal.quasicategory (CategoryTheory.Nerve.strictSegal C)
  obtain ⟨φ, hφ⟩ := SSet.Quasicategory.hornFilling h₀ hₙ hf.desc
  refine ⟨φ, fun j hj ↦ ?_⟩
  rw [← hf.ι_desc j hj, hφ, ← Category.assoc, SSet.horn.ι_ι]

/-- Convert the high-dimensional strict-Segal simplex filler into the
compatible-family form used by `SSet.KanComplex.iff`. -/
theorem hornFillerOfFourFamily {X : SSet.{u}} (sx : X.StrictSegal)
    {n : ℕ} {i : Fin (n + 5)}
    (f : ∀ (j : Fin (n + 5)), j ≠ i → (Δ[n + 3] ⟶ X))
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[n + 4] ⟶ X,
      ∀ (j : Fin (n + 5)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain ⟨σ, hσ⟩ := sx.hornFillerOfFour hf.desc
  refine ⟨SSet.yonedaEquiv.symm σ, fun j hj ↦ ?_⟩
  apply SSet.yonedaEquiv.injective
  change X.δ j σ = SSet.yonedaEquiv (f j hj)
  rw [hσ j hj]
  have hface := congrArg SSet.yonedaEquiv (hf.ι_desc j hj)
  simpa only [SSet.yonedaEquiv_comp, SSet.horn.yonedaEquiv_ι] using hface

/-- The nerve of a groupoid satisfies the complete Kan horn-filling
condition. -/
theorem kanComplex (C : Type u) [Groupoid.{v} C] : SSet.KanComplex (nerve C) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  obtain _ | n := n
  · exact hornFillerOne f
  obtain _ | n := n
  · fin_cases i
    · exact hornFillerTwoZero f hf
    · exact hornFillerInner (by simp) (by simp) f hf
    · exact hornFillerTwoLast f hf
  obtain _ | n := n
  · fin_cases i
    · exact hornFillerThreeZero f hf
    · exact hornFillerInner (by simp) (by simp) f hf
    · exact hornFillerInner (by simp) (by simp) f hf
    · exact hornFillerThreeLast f hf
  exact hornFillerOfFourFamily (CategoryTheory.Nerve.strictSegal C) f hf

private lemma twoFaceArrow {C : Type u} [Groupoid.{v} C]
    {x y : ComposableArrows C 2} {j : Fin 3}
    (h : (nerve C).δ j x = (nerve C).δ j y) :
    Arrow.mk (((nerve C).δ j x).hom) =
      Arrow.mk (((nerve C).δ j y).hom) :=
  congrArg (fun q ↦ Arrow.mk q.hom) h

/-- A 2-simplex in the nerve of a groupoid is uniquely determined by any
two of its faces.  The two outer cases use cancellation by invertible edges;
the inner case reads off the two spine arrows directly. -/
theorem two_simplex_eq_of_faces_except
    {C : Type u} [Groupoid.{v} C] (i : Fin 3)
    (x y : ComposableArrows C 2)
    (h : ∀ (j : Fin 3), j ≠ i → (nerve C).δ j x = (nerve C).δ j y) :
    x = y := by
  obtain ⟨x₀, x₁, x₂, f, g, rfl⟩ := ComposableArrows.mk₂_surjective x
  obtain ⟨y₀, y₁, y₂, f', g', rfl⟩ := ComposableArrows.mk₂_surjective y
  fin_cases i
  · have hf := twoFaceArrow (h 2 (by simp))
    have hfg := twoFaceArrow (h 1 (by simp))
    rw [nerve.δ₂_two, nerve.δ₂_two] at hf
    rw [nerve.δ₁_mk₂_eq, nerve.δ₁_mk₂_eq] at hfg
    obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj hf
    obtain rfl : x₁ = y₁ := congr_arg Arrow.rightFunc.obj hf
    obtain rfl : f = f' := by rwa [← Arrow.mk_inj]
    obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj hfg
    have : f ≫ g = f ≫ g' := by rwa [← Arrow.mk_inj]
    obtain rfl : g = g' := (cancel_epi f).1 this
    rfl
  · have hf := twoFaceArrow (h 2 (by simp))
    have hg := twoFaceArrow (h 0 (by simp))
    rw [nerve.δ₂_two, nerve.δ₂_two] at hf
    rw [nerve.δ₂_zero, nerve.δ₂_zero] at hg
    exact ComposableArrows.ext₂_of_arrow hf hg
  · have hg := twoFaceArrow (h 0 (by simp))
    have hfg := twoFaceArrow (h 1 (by simp))
    rw [nerve.δ₂_zero, nerve.δ₂_zero] at hg
    rw [nerve.δ₁_mk₂_eq, nerve.δ₁_mk₂_eq] at hfg
    obtain rfl : x₁ = y₁ := congr_arg Arrow.leftFunc.obj hg
    obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj hg
    obtain rfl : g = g' := by rwa [← Arrow.mk_inj]
    obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj hfg
    have : f ≫ g = f' ≫ g := by rwa [← Arrow.mk_inj]
    obtain rfl : f = f' := (cancel_mono g).1 this
    rfl

/-- A categorical nerve simplex of dimension at least two is determined by
all of its faces.  The zeroth face supplies the tail string, while the last
face supplies the initial object and initial arrow. -/
theorem simplex_eq_of_all_faces
    {C : Type u} [Category.{v} C] {n : ℕ}
    (x y : ComposableArrows C (n + 2))
    (h : ∀ j : Fin (n + 3), (nerve C).δ j x = (nerve C).δ j y) :
    x = y := by
  have htail := h 0
  change x.δ₀ = y.δ₀ at htail
  have hinit := h (Fin.last (n + 2))
  apply ComposableArrows.ext_succ (F := x) (G := y)
    (Functor.congr_obj hinit 0) htail
  convert Functor.congr_hom hinit
    (homOfLE (show (0 : Fin (n + 2)) ≤ 1 by simp)) using 1
  rfl

/-- Restrict one categorical-nerve simplex to the full boundary of its
standard simplex. -/
def boundaryRestriction {C : Type u} [Category.{v} C] (n : ℕ) :
    ComposableArrows C n →
      ((∂Δ[n] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) :=
  fun F => (SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm F

/-- In every dimension at least two, restriction of a categorical-nerve
simplex to its full boundary is injective. -/
theorem boundaryRestriction_injective
    {C : Type u} [Category.{v} C] (m : ℕ) :
    Function.Injective (boundaryRestriction (C := C) (m + 2)) := by
  intro F G h
  apply simplex_eq_of_all_faces F G
  intro i
  dsimp [boundaryRestriction] at h
  have hi := congrArg (fun q => SSet.boundary.ι i ≫ q) h
  erw [← Category.assoc, SSet.boundary.ι_ι] at hi
  erw [← Category.assoc, SSet.boundary.ι_ι] at hi
  have hi' := congrArg SSet.yonedaEquiv hi
  let d := (CategoryTheory.nerve C).δ i
  let e : ((Δ[m + 2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) ≃
      (CategoryTheory.nerve C).obj
        (Opposite.op (SimplexCategory.mk (m + 2))) :=
    SSet.yonedaEquiv
  calc
    d F = d (e (e.symm F)) :=
      congrArg d (e.apply_symm_apply F).symm
    _ = d (e (e.symm G)) := by
      simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp] using hi'
    _ = d G := congrArg d (e.apply_symm_apply G)

/-- In every dimension at least three, every full boundary in a categorical
nerve has a filler.  Restrict to the inner horn at vertex `1`, fill it using
the strict-Segal quasicategory structure, and recover the omitted face from
the codimension-two compatibility equations. -/
theorem boundaryRestriction_surjective
    {C : Type u} [Category.{v} C] (m : ℕ) :
    Function.Surjective (boundaryRestriction (C := C) (m + 3)) := by
  intro φ
  let i : Fin (m + 4) := 1
  let g : (Λ[m + 3, i] : SSet.{max u v}) ⟶ nerve C :=
    SSet.hornToBoundary (m + 3) i ≫ φ
  let f : ∀ (j : Fin (m + 4)), j ≠ i →
      ((Δ[m + 2] : SSet.{max u v}) ⟶ nerve C) :=
    fun j hj => SSet.horn.ι i j hj ≫ g
  have hf : SSet.horn.IsCompatible f :=
    SSet.horn.IsCompatible.of_hom g
  obtain ⟨ψ, hψ⟩ := hornFillerInner (C := C)
    (n := m + 2) (i := i) (by simp [i])
      (by change (1 : ℕ) < m + 3; omega) f hf
  let x : ComposableArrows C (m + 3) := SSet.yonedaEquiv ψ
  let b : Fin (m + 4) → ComposableArrows C (m + 2) :=
    fun j => SSet.yonedaEquiv (SSet.boundary.ι j ≫ φ)
  have hfaces (j : Fin (m + 4)) (hj : j ≠ i) :
      (nerve C).δ j x = b j := by
    have hmap := hψ j hj
    dsimp [f, g] at hmap
    erw [← Category.assoc,
      SSet.hornFaceToBoundary (m + 2) i j hj] at hmap
    have hmap' := congrArg SSet.yonedaEquiv hmap
    dsimp [x, b]
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp] using hmap'
  have hboundary (j k : Fin (m + 4)) (hjk : j < k) :
      (nerve C).δ (k.pred (Fin.ne_zero_of_lt hjk)) (b j) =
        (nerve C).δ (j.castPred (Fin.ne_last_of_lt hjk)) (b k) := by
    have hb : SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫
          SSet.boundary.ι j =
        SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫
          SSet.boundary.ι k := by
      rw [← cancel_mono (SSet.boundary (m + 3)).ι,
        Category.assoc, Category.assoc, SSet.boundary.ι_ι,
        SSet.boundary.ι_ι]
      obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last
        (Fin.ne_last_of_lt hjk)
      obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero
        (Fin.ne_zero_of_lt hjk)
      rw [Fin.pred_succ, Fin.castPred_castSucc,
        SSet.stdSimplex.δ_comp_δ (by grind)]
    have hb' := congrArg (fun q => q ≫ φ) hb
    simp only [Category.assoc] at hb'
    have hb'' := congrArg SSet.yonedaEquiv hb'
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, b] using hb''
  have hi : (nerve C).δ i x = b i := by
    apply simplex_eq_of_all_faces
    intro k
    by_cases hk : k.castSucc < i
    · have hx := ConcreteCategory.congr_hom
        ((nerve C).δ_comp_δ' hk) x
      exact hx.trans ((congrArg
        (fun z => ((nerve C).δ (i.pred hk.ne_zero)).hom' z)
        (hfaces k.castSucc hk.ne)).trans
          (hboundary k.castSucc i hk))
    · have hik : i ≤ k.castSucc := by omega
      have hx := ConcreteCategory.congr_hom
        ((nerve C).δ_comp_δ'' hik) x
      have hlt : i < k.succ := lt_of_le_of_lt hik k.castSucc_lt_succ
      exact hx.symm.trans ((congrArg
        (fun z => ((nerve C).δ (i.castLT (Nat.lt_of_le_of_lt
          (Fin.le_iff_val_le_val.mp hik) k.is_lt))).hom' z)
        (hfaces k.succ hlt.ne')).trans
          (hboundary i k.succ hlt).symm)
  refine ⟨x, ?_⟩
  have hx : SSet.yonedaEquiv.symm x = ψ := by
    dsimp [x]
    exact SSet.yonedaEquiv.symm_apply_apply ψ
  apply SSet.boundary.hom_ext
  intro j
  dsimp [boundaryRestriction]
  erw [← Category.assoc, SSet.boundary.ι_ι]
  rw [hx]
  have hj : (nerve C).δ j x = b j := by
    by_cases hji : j = i
    · simpa [hji] using hi
    · exact hfaces j hji
  apply SSet.yonedaEquiv.injective
  dsimp [x, b] at hj
  simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp] using hj

/-- Categorical-nerve boundary restriction is bijective in every dimension at
least three. -/
theorem boundaryRestriction_bijective
    {C : Type u} [Category.{v} C] (m : ℕ) :
    Function.Bijective (boundaryRestriction (C := C) (m + 3)) :=
  ⟨boundaryRestriction_injective (C := C) (m + 1),
    boundaryRestriction_surjective (C := C) m⟩

/-- In dimensions at least three, a categorical nerve simplex is determined
by any horn.  Simplicial identities recover every face of the omitted face,
after which `simplex_eq_of_all_faces` reconstructs both the omitted face and
the original simplex. -/
theorem simplex_eq_of_faces_except_high
    {C : Type u} [Category.{v} C] {n : ℕ}
    (i : Fin (n + 4)) (x y : ComposableArrows C (n + 3))
    (h : ∀ (j : Fin (n + 4)), j ≠ i →
      (nerve C).δ j x = (nerve C).δ j y) :
    x = y := by
  have hi : (nerve C).δ i x = (nerve C).δ i y := by
    apply simplex_eq_of_all_faces
    intro k
    by_cases hk : k.castSucc < i
    · have hx := ConcreteCategory.congr_hom ((nerve C).δ_comp_δ' hk) x
      have hy := ConcreteCategory.congr_hom ((nerve C).δ_comp_δ' hk) y
      exact hx.trans ((congrArg
        (fun z ↦ ((nerve C).δ (i.pred hk.ne_zero)).hom' z)
        (h k.castSucc hk.ne)).trans hy.symm)
    · have hik : i ≤ k.castSucc := by omega
      have hx := ConcreteCategory.congr_hom ((nerve C).δ_comp_δ'' hik) x
      have hy := ConcreteCategory.congr_hom ((nerve C).δ_comp_δ'' hik) y
      exact hx.symm.trans ((congrArg
        (fun z ↦ ((nerve C).δ (i.castLT (Nat.lt_of_le_of_lt
          (Fin.le_iff_val_le_val.mp hik) k.is_lt))).hom' z)
        (h k.succ (lt_of_le_of_lt hik k.castSucc_lt_succ).ne')).trans hy)
  apply simplex_eq_of_all_faces
  intro j
  by_cases hj : j = i
  · simpa [hj] using hi
  · exact h j hj

end CategoryTheory.Nerve
