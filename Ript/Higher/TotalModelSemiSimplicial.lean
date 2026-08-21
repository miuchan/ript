import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.CategoryTheory.Types.Basic
import Ript.Higher.TotalModelSimplicial

/-!
# The global semi-simplicial Duskin nerve of total resource models

An `n`-simplex contains a total resource model at every vertex, a
resource-changing model 1-cell on every increasing edge, a comparison 2-cell
on every increasing triangle, and the associator-corrected Duskin equation on
every increasing tetrahedron. This definition works uniformly in every
dimension.

Strictly monotone maps of finite ordinals only select vertices and therefore
act by literal restriction of all data. The restriction laws are strict, so
these simplices form a genuine semi-simplicial set. Degeneracy maps require
inserting identity 1-cells and unitors when vertices are repeated; that
separate normalization layer is intentionally not hidden in this file.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open Opposite
open Simplicial

universe u v w

namespace TotalModelSemiSimplicial

/-- Global Duskin simplex data in arbitrary dimension. -/
structure Simplex (n : Nat) where
  /-- Total resource model at every vertex. -/
  vertex : Fin (n + 1) → ResourceModel.{u, v, w}
  /-- Resource-changing model morphism on every strictly increasing edge. -/
  edge : ∀ (i j : Fin (n + 1)), i < j → ResourceModelHom (vertex i) (vertex j)
  /-- Lax comparison 2-cell on every strictly increasing triangle. -/
  triangle : ∀ (i j k : Fin (n + 1)) (hij : i < j) (hjk : j < k),
    ResourceModelTransformation
      ((edge i j hij).comp (edge j k hjk))
      (edge i k (hij.trans hjk))
  /-- Every strictly increasing tetrahedron satisfies the
  associator-corrected Duskin equation. -/
  tetrahedron : ∀ (i j k l : Fin (n + 1))
      (hij : i < j) (hjk : j < k) (hkl : k < l),
    ResourceModelTransformation.whiskerRight
          (triangle i j k hij hjk) (edge k l hkl) ≫
        triangle i k l (hij.trans hjk) hkl =
      TotalModelSimplicial.associatorTransformation
          (edge i j hij) (edge j k hjk) (edge k l hkl) ≫
        ResourceModelTransformation.whiskerLeft
          (edge i j hij) (triangle j k l hjk hkl) ≫
        triangle i j l hij (hjk.trans hkl)

namespace Simplex

/-- Two coordinate simplices are equal once their vertices, edges, and
triangle cells agree.  Tetrahedral coherence fields are propositions and
therefore proof-irrelevant. -/
theorem extensionality {n : Nat} {first second : Simplex.{u, v, w} n}
    (vertex : first.vertex = second.vertex)
    (edge : HEq first.edge second.edge)
    (triangle : HEq first.triangle second.triangle) :
    first = second := by
  cases first with
  | mk firstVertex firstEdge firstTriangle firstTetrahedron =>
      cases second with
      | mk secondVertex secondEdge secondTriangle secondTetrahedron =>
          dsimp at vertex edge triangle
          subst secondVertex
          cases eq_of_heq edge
          cases eq_of_heq triangle
          rfl

/-- Restrict a global Duskin simplex along a strictly monotone map of finite
ordinals. -/
def pullback {m n : Nat} (map : Fin (m + 1) ↪o Fin (n + 1))
    (simplex : Simplex n) : Simplex m where
  vertex i := simplex.vertex (map i)
  edge i j hij := simplex.edge (map i) (map j) (map.strictMono hij)
  triangle i j k hij hjk :=
    simplex.triangle (map i) (map j) (map k)
      (map.strictMono hij) (map.strictMono hjk)
  tetrahedron i j k l hij hjk hkl :=
    simplex.tetrahedron (map i) (map j) (map k) (map l)
      (map.strictMono hij) (map.strictMono hjk) (map.strictMono hkl)

@[simp]
theorem pullback_refl {n : Nat} (simplex : Simplex n) :
    pullback (OrderEmbedding.id (Fin (n + 1))) simplex = simplex := by
  cases simplex
  rfl

@[simp]
theorem pullback_trans {l m n : Nat}
    (first : Fin (l + 1) ↪o Fin (m + 1))
    (second : Fin (m + 1) ↪o Fin (n + 1))
    (simplex : Simplex n) :
    pullback (first.trans second) simplex =
      pullback first (pullback second simplex) := by
  cases simplex
  rfl

end Simplex

/-- Semi-simplicial sets are presheaves on the category of nonempty finite
ordinals and strictly monotone maps. -/
abbrev SemiSSet := SemiSimplexCategoryᵒᵖ ⥤
  Type (max (max (u + 1) (v + 1)) (w + 1))

/-- **Global semi-simplicial Duskin nerve.** Every face map is restriction
along an order embedding, so functoriality is exact rather than merely up to
isomorphism. -/
def nerve : SemiSSet.{u, v, w} where
  obj dimension := Simplex.{u, v, w} dimension.unop.len
  map map := ↾fun simplex ↦ Simplex.pullback
    (SemiSimplexCategory.homEquiv map.unop) simplex
  map_id dimension := by
    ext simplex
    exact Simplex.pullback_refl simplex
  map_comp first second := by
    ext simplex
    change Simplex.pullback
        (SemiSimplexCategory.homEquiv (first ≫ second).unop) simplex =
      Simplex.pullback (SemiSimplexCategory.homEquiv second.unop)
        (Simplex.pullback (SemiSimplexCategory.homEquiv first.unop) simplex)
    rw [unop_comp, SemiSimplexCategory.homEquiv_comp]
    exact Simplex.pullback_trans
      (SemiSimplexCategory.homEquiv second.unop)
      (SemiSimplexCategory.homEquiv first.unop) simplex

@[simp]
theorem nerve_map_apply
    {source target : SemiSimplexCategoryᵒᵖ}
    (map : source ⟶ target)
    (simplex : nerve.{u, v, w}.obj source) :
    nerve.{u, v, w}.map map simplex =
      Simplex.pullback (SemiSimplexCategory.homEquiv map.unop) simplex :=
  rfl

/-! ## Recovery of the explicit low-dimensional skeleton -/

/-- A global 2-simplex recovers the previously exposed Duskin triangle on its
three vertices. -/
def Simplex.toTriangle (simplex : Simplex.{u, v, w} 2) :
    TotalModelSimplicial.Triangle
      (simplex.vertex 0) (simplex.vertex 1) (simplex.vertex 2) where
  edge01 := simplex.edge 0 1 (by decide)
  edge12 := simplex.edge 1 2 (by decide)
  edge02 := simplex.edge 0 2 (by decide)
  cell012 := simplex.triangle 0 1 2 (by decide) (by decide)

@[simp]
theorem Simplex.toTriangle_cell (simplex : Simplex.{u, v, w} 2) :
    simplex.toTriangle.cell012 =
      simplex.triangle 0 1 2 (by decide) (by decide) :=
  rfl

/-- A global 3-simplex recovers the explicit coherent tetrahedron on its four
vertices. -/
def Simplex.toTetrahedron (simplex : Simplex.{u, v, w} 3) :
    TotalModelSimplicial.Tetrahedron
      (simplex.vertex 0) (simplex.vertex 1)
      (simplex.vertex 2) (simplex.vertex 3) where
  edge01 := simplex.edge 0 1 (by decide)
  edge12 := simplex.edge 1 2 (by decide)
  edge23 := simplex.edge 2 3 (by decide)
  edge02 := simplex.edge 0 2 (by decide)
  edge13 := simplex.edge 1 3 (by decide)
  edge03 := simplex.edge 0 3 (by decide)
  cell012 := simplex.triangle 0 1 2 (by decide) (by decide)
  cell123 := simplex.triangle 1 2 3 (by decide) (by decide)
  cell013 := simplex.triangle 0 1 3 (by decide) (by decide)
  cell023 := simplex.triangle 0 2 3 (by decide) (by decide)
  coherence := simplex.tetrahedron 0 1 2 3
    (by decide) (by decide) (by decide)

@[simp]
theorem Simplex.toTetrahedron_cell023 (simplex : Simplex.{u, v, w} 3) :
    simplex.toTetrahedron.cell023 =
      simplex.triangle 0 2 3 (by decide) (by decide) :=
  rfl

end TotalModelSemiSimplicial

end Ript.Higher
