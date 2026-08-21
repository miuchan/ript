import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
import Ript.Higher.TotalModelSemiSimplicial

/-!
# The global Duskin nerve of total resource models

The native definition of a Duskin simplex is a normal (strictly unitary) lax
functor from the locally discrete bicategory on a finite ordinal into the
total bicategory of resource models.  This formulation makes repeated
vertices, identity 1-cells, unitors, and all tetrahedral coherence part of the
standard lax-functor laws instead of exposing dependent equality transports
in coordinates.

Precomposition by a monotone map of finite ordinals preserves strict
unitality.  Hence all faces and degeneracies are handled uniformly.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory
open Opposite
open Simplicial

universe u v w

namespace TotalModelDuskinNerve

/-- The finite ordinal `[n]`, regarded as a locally discrete bicategory. -/
abbrev FiniteOrdinal (n : Nat) := LocallyDiscrete (Fin (n + 1))

/-- The unique source 1-cell selected by an inequality in `[n]`. -/
def ordinalHom {n : Nat} {i j : Fin (n + 1)} (hij : i ≤ j) :
    (LocallyDiscrete.mk i : FiniteOrdinal n) ⟶ LocallyDiscrete.mk j :=
  (homOfLE hij).toLoc

/-- A global `n`-simplex is a normal lax functor `[n] → ResourceModel`. -/
abbrev Simplex (n : Nat) :=
  StrictlyUnitaryLaxFunctor (FiniteOrdinal n) ResourceModel.{u, v, w}

/-- A monotone map of finite ordinals as a functor of their thin categories. -/
def ordinalFunctor {m n : Nat} (map : Fin (m + 1) →o Fin (n + 1)) :
    Functor (Fin (m + 1)) (Fin (n + 1)) where
  obj i := map i
  map arrow := homOfLE (map.monotone (leOfHom arrow))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- An ordinary functor induces a normal pseudofunctor between its locally
discrete bicategories. -/
def locallyDiscretePseudofunctor
    {C D : Type} [SmallCategory C] [SmallCategory D] (F : Functor C D) :
    StrictlyUnitaryPseudofunctor (LocallyDiscrete C) (LocallyDiscrete D) where
  __ := F.toPseudofunctor
  map_id X := by
    cases X with
    | mk X =>
      apply Discrete.ext
      exact F.map_id X
  mapId_eq_eqToIso X := by
    cases X
    apply Subsingleton.elim

/-- A monotone finite-ordinal map as a normal lax functor between the locally
discrete ordinal bicategories. -/
def ordinalLaxFunctor {m n : Nat} (map : Fin (m + 1) →o Fin (n + 1)) :
    StrictlyUnitaryLaxFunctor (FiniteOrdinal m) (FiniteOrdinal n) :=
  (locallyDiscretePseudofunctor (ordinalFunctor map)).toStrictlyUnitaryLaxFunctor

@[simp]
theorem ordinalLaxFunctor_map_ordinalHom {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    {i j : Fin (m + 1)} (hij : i ≤ j) :
    (ordinalLaxFunctor map).map (ordinalHom hij) =
      ordinalHom (map.monotone hij) := by
  apply Discrete.ext
  apply Subsingleton.elim

@[simp]
theorem ordinalLaxFunctor_mapComp_ordinalHom {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    {i j k : Fin (m + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (ordinalLaxFunctor map).mapComp (ordinalHom hij) (ordinalHom hjk) =
      𝟙 ((ordinalLaxFunctor map).map (ordinalHom hij) ≫
        (ordinalLaxFunctor map).map (ordinalHom hjk)) := by
  apply Subsingleton.elim

@[simp]
theorem ordinalLaxFunctor_map_comp_ordinalHom {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    {i j k : Fin (m + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (ordinalLaxFunctor map).map (ordinalHom hij ≫ ordinalHom hjk) =
      ordinalHom (map.monotone (hij.trans hjk)) := by
  apply Discrete.ext
  apply Subsingleton.elim

/-- Reindex a normal lax simplex along an arbitrary monotone ordinal map. -/
def Simplex.pullback {m n : Nat} (map : Fin (m + 1) →o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n) : Simplex.{u, v, w} m :=
  (ordinalLaxFunctor map).comp simplex

@[simp]
theorem ordinalLaxFunctor_id (n : Nat) :
    ordinalLaxFunctor (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) =
      StrictlyUnitaryLaxFunctor.id (FiniteOrdinal n) := by
  apply StrictlyUnitaryLaxFunctor.ext
  · rfl
  · apply heq_of_eq
    funext X Y arrow
    apply Discrete.ext
    apply Subsingleton.elim
  all_goals
    apply heq_of_eq
    apply Subsingleton.elim

@[simp]
theorem ordinalLaxFunctor_comp {l m n : Nat}
    (first : Fin (l + 1) →o Fin (m + 1))
    (second : Fin (m + 1) →o Fin (n + 1)) :
    ordinalLaxFunctor (second.comp first) =
      (ordinalLaxFunctor first).comp (ordinalLaxFunctor second) := by
  apply StrictlyUnitaryLaxFunctor.ext
  · rfl
  · apply heq_of_eq
    funext X Y arrow
    apply Discrete.ext
    apply Subsingleton.elim
  all_goals
    apply heq_of_eq
    apply Subsingleton.elim

@[simp]
theorem Simplex.pullback_refl {n : Nat} (simplex : Simplex.{u, v, w} n) :
    Simplex.pullback
        (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) simplex = simplex := by
  rw [Simplex.pullback, ordinalLaxFunctor_id]
  exact StrictlyUnitaryLaxFunctor.id_comp simplex

@[simp]
theorem Simplex.pullback_trans {l m n : Nat}
    (first : Fin (l + 1) →o Fin (m + 1))
    (second : Fin (m + 1) →o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n) :
    Simplex.pullback (second.comp first) simplex =
      Simplex.pullback first (Simplex.pullback second simplex) := by
  rw [Simplex.pullback, ordinalLaxFunctor_comp]
  exact StrictlyUnitaryLaxFunctor.comp_assoc
    (ordinalLaxFunctor first) (ordinalLaxFunctor second) simplex

/-- The simplicial set of normal lax finite-ordinal diagrams in the total
resource-model bicategory. -/
abbrev SSet := Functor SimplexCategoryᵒᵖ
  (Type (max (max (u + 1) (v + 1)) (w + 1)))

/-- **Global Duskin nerve.** Faces and degeneracies are both precomposition
by monotone finite-ordinal maps. -/
def nerve : SSet.{u, v, w} where
  obj dimension := Simplex.{u, v, w} dimension.unop.len
  map map := ↾fun simplex ↦ Simplex.pullback
    (SimplexCategory.homEquivOrderHom map.unop) simplex
  map_id dimension := by
    ext simplex
    exact Simplex.pullback_refl simplex
  map_comp first second := by
    ext simplex
    change Simplex.pullback
        (SimplexCategory.homEquivOrderHom (first ≫ second).unop) simplex =
      Simplex.pullback (SimplexCategory.homEquivOrderHom second.unop)
        (Simplex.pullback
          (SimplexCategory.homEquivOrderHom first.unop) simplex)
    rw [unop_comp]
    change Simplex.pullback
        ((SimplexCategory.homEquivOrderHom first.unop).comp
          (SimplexCategory.homEquivOrderHom second.unop)) simplex = _
    exact Simplex.pullback_trans
      (SimplexCategory.homEquivOrderHom second.unop)
      (SimplexCategory.homEquivOrderHom first.unop) simplex

@[simp]
theorem nerve_map_apply {source target : SimplexCategoryᵒᵖ}
    (map : source ⟶ target) (simplex : nerve.{u, v, w}.obj source) :
    nerve.{u, v, w}.map map simplex =
      Simplex.pullback
        (SimplexCategory.homEquivOrderHom map.unop) simplex :=
  rfl

/-! ## Coordinate decoding and degeneracy formulas -/

/-- The total resource model at a vertex of a native Duskin simplex. -/
def Simplex.vertex {n : Nat} (simplex : Simplex.{u, v, w} n)
    (i : Fin (n + 1)) : ResourceModel.{u, v, w} :=
  simplex.obj (LocallyDiscrete.mk i)

/-- The total-model 1-cell on a weakly increasing edge. -/
def Simplex.edge {n : Nat} (simplex : Simplex.{u, v, w} n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    ResourceModelHom (simplex.vertex i) (simplex.vertex j) :=
  simplex.map (ordinalHom hij)

/-- The lax comparison 2-cell on a weakly increasing triangle. -/
def Simplex.comparison {n : Nat} (simplex : Simplex.{u, v, w} n)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    ResourceModelTransformation
      ((simplex.edge hij).comp (simplex.edge hjk))
      (simplex.edge (hij.trans hjk)) := by
  exact simplex.toLaxFunctor.mapComp'
    (ordinalHom hij) (ordinalHom hjk) (ordinalHom (hij.trans hjk)) (by
      apply Discrete.ext
      apply Subsingleton.elim)

@[simp]
theorem Simplex.pullback_vertex {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n) (i : Fin (m + 1)) :
    (Simplex.pullback map simplex).vertex i = simplex.vertex (map i) :=
  rfl

@[simp]
theorem Simplex.pullback_edge {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n) {i j : Fin (m + 1)} (hij : i ≤ j) :
    (Simplex.pullback map simplex).edge hij =
      simplex.edge (map.monotone hij) := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem Simplex.pullback_comparison {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n)
    {i j k : Fin (m + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (Simplex.pullback map simplex).comparison hij hjk =
      simplex.comparison (map.monotone hij) (map.monotone hjk) := by
  change ((ordinalLaxFunctor map).comp simplex).toLaxFunctor.mapComp'
      (ordinalHom hij) (ordinalHom hjk) (ordinalHom (hij.trans hjk)) _ =
    simplex.toLaxFunctor.mapComp'
      (ordinalHom (map.monotone hij)) (ordinalHom (map.monotone hjk))
      (ordinalHom ((map.monotone hij).trans (map.monotone hjk))) _
  simp only [LaxFunctor.mapComp', StrictlyUnitaryLaxFunctor.comp_mapComp]
  rw [ordinalLaxFunctor_map_ordinalHom map hij,
    ordinalLaxFunctor_map_ordinalHom map hjk,
    ordinalLaxFunctor_mapComp_ordinalHom map hij hjk,
    StrictlyUnitaryLaxFunctor.comp_map₂,
    ordinalLaxFunctor_map_comp_ordinalHom map hij hjk]
  rw [Category.assoc, ← simplex.map₂_comp]
  congr 2

/-- Normality is visible in coordinates: the edge on a repeated vertex is
the identity total-model 1-cell. -/
@[simp]
theorem Simplex.edge_refl {n : Nat} (simplex : Simplex.{u, v, w} n)
    (i : Fin (n + 1)) (hii : i ≤ i) :
    simplex.edge hii = ResourceModelHom.id (simplex.vertex i) := by
  change simplex.map (ordinalHom hii) = _
  rw [show ordinalHom hii = 𝟙 (LocallyDiscrete.mk i) by
    apply Discrete.ext
    apply Subsingleton.elim]
  exact simplex.map_id (LocallyDiscrete.mk i)

/-- An edge whose endpoints are propositionally equal is heterogeneously the
identity edge; the heterogeneous equality records the endpoint transport. -/
theorem Simplex.edge_of_eq {n : Nat} (simplex : Simplex.{u, v, w} n)
    {i j : Fin (n + 1)} (hij : i ≤ j) (equality : i = j) :
    HEq (simplex.edge hij) (ResourceModelHom.id (simplex.vertex i)) := by
  subst j
  exact heq_of_eq (simplex.edge_refl i hij)

/-- Every collapsed edge under a monotone map becomes an identity after
pullback.  This is the coordinate content of a degeneracy map. -/
theorem Simplex.pullback_edge_of_eq {m n : Nat}
    (map : Fin (m + 1) →o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n) {i j : Fin (m + 1)} (hij : i ≤ j)
    (collapsed : map i = map j) :
    HEq ((Simplex.pullback map simplex).edge hij)
      (ResourceModelHom.id ((Simplex.pullback map simplex).vertex i)) := by
  rw [Simplex.pullback_edge]
  exact simplex.edge_of_eq (map.monotone hij) collapsed

/-- The unique monotone map `[1] → [0]`, generating the first degeneracy. -/
def zeroDegeneracyOrderHom : Fin 2 →o Fin 1 where
  toFun _ := 0
  monotone' _ _ _ := le_rfl

/-- The first degeneracy duplicates the sole vertex of a zero-simplex. -/
def Simplex.zeroDegeneracy (simplex : Simplex.{u, v, w} 0) :
    Simplex.{u, v, w} 1 :=
  Simplex.pullback zeroDegeneracyOrderHom simplex

@[simp]
theorem Simplex.zeroDegeneracy_vertex_zero
    (simplex : Simplex.{u, v, w} 0) :
    simplex.zeroDegeneracy.vertex 0 = simplex.vertex 0 :=
  rfl

@[simp]
theorem Simplex.zeroDegeneracy_vertex_one
    (simplex : Simplex.{u, v, w} 0) :
    simplex.zeroDegeneracy.vertex 1 = simplex.vertex 0 :=
  rfl

/-- The edge created by the first degeneracy is exactly an identity 1-cell,
up to the endpoint transport made explicit by `HEq`. -/
theorem Simplex.zeroDegeneracy_edge
    (simplex : Simplex.{u, v, w} 0) :
    HEq (simplex.zeroDegeneracy.edge (by decide : (0 : Fin 2) ≤ 1))
      (ResourceModelHom.id (simplex.zeroDegeneracy.vertex 0)) :=
  Simplex.pullback_edge_of_eq zeroDegeneracyOrderHom simplex
    (by decide : (0 : Fin 2) ≤ 1) rfl

/-- The tetrahedral equation of every native simplex is exactly the lax
associativity law, including the source and target bicategory associators. -/
theorem Simplex.tetrahedral_coherence {n : Nat}
    (simplex : Simplex.{u, v, w} n)
    {a b c d : FiniteOrdinal n}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    simplex.mapComp f g ▷ simplex.map h ≫
        simplex.mapComp (f ≫ g) h ≫ simplex.map₂ (α_ f g h).hom =
      (α_ (simplex.map f) (simplex.map g) (simplex.map h)).hom ≫
        simplex.map f ◁ simplex.mapComp g h ≫
        simplex.mapComp f (g ≫ h) :=
  simplex.map₂_associator f g h

/-- Forget the normal-lax presentation to the strictly increasing coordinate
presentation of the global semi-simplicial Duskin nerve. -/
def Simplex.toSemiSimplex {n : Nat} (simplex : Simplex.{u, v, w} n) :
    TotalModelSemiSimplicial.Simplex.{u, v, w} n where
  vertex := simplex.vertex
  edge i j hij := simplex.edge hij.le
  triangle i j k hij hjk := simplex.comparison hij.le hjk.le
  tetrahedron i j k l hij hjk hkl := by
    let f₀₁ := ordinalHom hij.le
    let f₁₂ := ordinalHom hjk.le
    let f₂₃ := ordinalHom hkl.le
    let f₀₂ := ordinalHom (hij.trans hjk).le
    let f₁₃ := ordinalHom (hjk.trans hkl).le
    let f₀₃ := ordinalHom (hij.trans (hjk.trans hkl)).le
    have h₀₂ : f₀₁ ≫ f₁₂ = f₀₂ := by
      apply Discrete.ext
      apply Subsingleton.elim
    have h₁₃ : f₁₂ ≫ f₂₃ = f₁₃ := by
      apply Discrete.ext
      apply Subsingleton.elim
    have h₀₃ : f₀₂ ≫ f₂₃ = f₀₃ := by
      apply Discrete.ext
      apply Subsingleton.elim
    have h₀₁₃ : f₀₁ ≫ f₁₃ = f₀₃ := by
      apply Discrete.ext
      apply Subsingleton.elim
    change
      simplex.toLaxFunctor.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷
            simplex.map f₂₃ ≫
          simplex.toLaxFunctor.mapComp' f₀₂ f₂₃ f₀₃ h₀₃ =
        (α_ (simplex.map f₀₁) (simplex.map f₁₂)
          (simplex.map f₂₃)).hom ≫
          simplex.map f₀₁ ◁
              simplex.toLaxFunctor.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫
            simplex.toLaxFunctor.mapComp' f₀₁ f₁₃ f₀₃ h₀₁₃
    exact simplex.toLaxFunctor.mapComp'_whiskerRight_comp_mapComp'
      f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f₀₃ h₀₂ h₁₃ h₀₃

@[simp]
theorem Simplex.toSemiSimplex_vertex {n : Nat}
    (simplex : Simplex.{u, v, w} n) (i : Fin (n + 1)) :
    simplex.toSemiSimplex.vertex i = simplex.vertex i :=
  rfl

@[simp]
theorem Simplex.toSemiSimplex_edge {n : Nat}
    (simplex : Simplex.{u, v, w} n) {i j : Fin (n + 1)} (hij : i < j) :
    simplex.toSemiSimplex.edge i j hij = simplex.edge hij.le :=
  rfl

@[simp]
theorem Simplex.toSemiSimplex_triangle {n : Nat}
    (simplex : Simplex.{u, v, w} n)
    {i j k : Fin (n + 1)} (hij : i < j) (hjk : j < k) :
    simplex.toSemiSimplex.triangle i j k hij hjk =
      simplex.comparison hij.le hjk.le :=
  rfl

/-- Forgetting a native simplex commutes with restriction along every strict
order embedding. -/
theorem Simplex.toSemiSimplex_pullback {m n : Nat}
    (map : Fin (m + 1) ↪o Fin (n + 1))
    (simplex : Simplex.{u, v, w} n) :
    (Simplex.pullback map.toOrderHom simplex).toSemiSimplex =
      TotalModelSemiSimplicial.Simplex.pullback map simplex.toSemiSimplex := by
  apply TotalModelSemiSimplicial.Simplex.extensionality
  · rfl
  · rfl
  · apply heq_of_eq
    funext i j k hij hjk
    exact Simplex.pullback_comparison map.toOrderHom simplex hij.le hjk.le

/-- The native Duskin nerve restricts naturally to the previously constructed
coordinate semi-simplicial nerve. -/
def forgetToSemi :
    SemiSimplexCategory.toSimplexCategory.op ⋙ nerve.{u, v, w} ⟶
      TotalModelSemiSimplicial.nerve.{u, v, w} where
  app dimension := ↾fun simplex ↦ simplex.toSemiSimplex
  naturality := by
    intro source target map
    ext simplex
    exact Simplex.toSemiSimplex_pullback
      (SemiSimplexCategory.homEquiv map.unop) simplex

theorem forgetToSemi_app_apply
    (dimension : SemiSimplexCategoryᵒᵖ)
    (simplex :
      (SemiSimplexCategory.toSimplexCategory.op ⋙ nerve.{u, v, w}).obj
        dimension) :
    forgetToSemi.{u, v, w}.app dimension simplex = simplex.toSemiSimplex :=
  rfl

end TotalModelDuskinNerve

end Ript.Higher
