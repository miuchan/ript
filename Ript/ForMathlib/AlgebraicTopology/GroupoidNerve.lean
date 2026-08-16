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

end CategoryTheory.Nerve
