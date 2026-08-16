import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Rational points in finite rational convex hulls

This file supplies the scalar-extension facts needed to use real
Hahn--Banach separation for finite polytopes whose vertices and target point
have rational coordinates.

The central boundary is exact rather than merely topological: a rational
point belongs to the real convex hull of finitely many rational vertices if
and only if it already belongs to their rational convex hull.  The proof uses
a minimum-cardinality Caratheodory support, reflects its affine span through
the embedding `ℚ → ℝ`, and then uses uniqueness of barycentric coordinates.

The final theorem rationalizes any strict real separator.  Strictness is an
open finite family of inequalities, so density of rational coordinate vectors
is sufficient once exact convex-hull reflection has been established.
-/

set_option autoImplicit false

namespace Ript.ForMathlib.RationalConvexHull

open scoped BigOperators

open Set

universe u v

variable {ι : Type u} {κ : Type v}

/-- Membership in the convex hull of a finite indexed family is equivalent
to an explicit simplex of weights on that same index type.  The forward
direction aggregates any finite convex representation along chosen vertex
preimages, so duplicate vertices are handled without an injectivity
hypothesis. -/
theorem mem_convexHull_range_iff_exists_weights
    {E : Type v} [AddCommGroup E] [Module ℚ E]
    [Fintype ι] (vertices : ι → E) (target : E) :
    target ∈ convexHull ℚ (Set.range vertices) ↔
      ∃ weight : ι → ℚ, (∀ i, 0 ≤ weight i) ∧
        ∑ i, weight i = 1 ∧ ∑ i, weight i • vertices i = target := by
  classical
  constructor
  · intro hmem
    obtain ⟨index, indexFintype, sourceWeight, sourceVertex,
      hsourceNonnegative, hsourceSum, hsourceVertex, hsourceLinear⟩ :=
      mem_convexHull_iff_exists_fintype.mp hmem
    let vertexIndex (i : index) : ι := Classical.choose (hsourceVertex i)
    have hvertexIndex (i : index) : vertices (vertexIndex i) = sourceVertex i :=
      Classical.choose_spec (hsourceVertex i)
    let weight : ι → ℚ := fun vertex =>
      ∑ i : index, if vertexIndex i = vertex then sourceWeight i else 0
    refine ⟨weight, ?_, ?_, ?_⟩
    · intro vertex
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact hsourceNonnegative i
      · exact le_rfl
    · calc
        ∑ vertex, weight vertex =
            ∑ vertex, ∑ i : index,
              if vertexIndex i = vertex then sourceWeight i else 0 := rfl
        _ = ∑ i : index, ∑ vertex,
              if vertexIndex i = vertex then sourceWeight i else 0 := Finset.sum_comm
        _ = ∑ i : index, sourceWeight i := by simp
        _ = 1 := hsourceSum
    · calc
        ∑ vertex, weight vertex • vertices vertex =
            ∑ vertex, ∑ i : index,
              (if vertexIndex i = vertex then sourceWeight i else 0) •
                vertices vertex := by
          apply Finset.sum_congr rfl
          intro vertex _
          rw [Finset.sum_smul]
        _ = ∑ i : index, ∑ vertex,
              (if vertexIndex i = vertex then sourceWeight i else 0) •
                vertices vertex := Finset.sum_comm
        _ = ∑ i : index, sourceWeight i • vertices (vertexIndex i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp
        _ = ∑ i : index, sourceWeight i • sourceVertex i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hvertexIndex]
        _ = target := hsourceLinear
  · rintro ⟨weight, hnonnegative, hsum, hlinear⟩
    exact mem_convexHull_of_exists_fintype weight vertices hnonnegative hsum
      (fun i => Set.mem_range_self i) hlinear

/-- Coordinatewise embedding of a rational vector into a real vector. -/
def ratCastVector (x : κ → ℚ) : κ → ℝ :=
  fun k => x k

/-- The standard finite dot-product functional. -/
def dotLinear [Fintype κ] (coefficient : κ → ℝ) : (κ → ℝ) →ₗ[ℝ] ℝ :=
  Fintype.linearCombination ℝ coefficient

@[simp]
theorem dotLinear_apply [Fintype κ] (coefficient x : κ → ℝ) :
    dotLinear coefficient x = ∑ k, x k * coefficient k := by
  simp [dotLinear, Fintype.linearCombination_apply]

/-- A rational linear functional on a finite coordinate space is the dot
product with its values on the standard basis. -/
theorem linearMap_eq_sum_basis [Fintype κ]
    (f : (κ → ℚ) →ₗ[ℚ] ℚ) (x : κ → ℚ) :
    f x = ∑ k, x k * f ((Pi.basisFun ℚ κ) k) := by
  classical
  conv_lhs => rw [← (Pi.basisFun ℚ κ).sum_repr x]
  simp [Pi.basisFun_repr, map_sum]

/-- Extending the standard-basis coefficients of a rational functional to
`ℝ` commutes with coordinatewise rational casting. -/
theorem dotLinear_ratCastVector [Fintype κ]
    (f : (κ → ℚ) →ₗ[ℚ] ℚ) (x : κ → ℚ) :
    dotLinear (fun k => (f ((Pi.basisFun ℚ κ) k) : ℝ)) (ratCastVector x) =
      (f x : ℝ) := by
  classical
  rw [linearMap_eq_sum_basis]
  simp [ratCastVector]

/-- Membership in the real span of rational generators reflects to
membership in their rational span. -/
theorem mem_span_of_ratCastVector_mem_span [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ)
    (hmem : ratCastVector target ∈
      Submodule.span ℝ (Set.range fun i => ratCastVector (vertices i))) :
    target ∈ Submodule.span ℚ (Set.range vertices) := by
  classical
  by_contra hnot
  obtain ⟨f, hftarget, hspan⟩ :=
    (Submodule.span ℚ (Set.range vertices)).exists_le_ker_of_notMem hnot
  let fReal : (κ → ℝ) →ₗ[ℝ] ℝ :=
    dotLinear (fun k => (f ((Pi.basisFun ℚ κ) k) : ℝ))
  have hgenerator :
      Set.range (fun i => ratCastVector (vertices i)) ⊆ LinearMap.ker fReal := by
    rintro _ ⟨i, rfl⟩
    change fReal (ratCastVector (vertices i)) = 0
    have hcast : fReal (ratCastVector (vertices i)) = (f (vertices i) : ℝ) := by
      dsimp [fReal]
      exact dotLinear_ratCastVector f (vertices i)
    rw [hcast]
    have hvi : vertices i ∈ Submodule.span ℚ (Set.range vertices) :=
      Submodule.subset_span (Set.mem_range_self i)
    have : f (vertices i) = 0 := by
      exact LinearMap.mem_ker.mp (hspan hvi)
    simp [this]
  have hrealSpan :
      Submodule.span ℝ (Set.range fun i => ratCastVector (vertices i)) ≤
        LinearMap.ker fReal :=
    Submodule.span_le.mpr hgenerator
  have hzero : fReal (ratCastVector target) = 0 :=
    LinearMap.mem_ker.mp (hrealSpan hmem)
  have hcast : fReal (ratCastVector target) = (f target : ℝ) := by
    dsimp [fReal]
    exact dotLinear_ratCastVector f target
  rw [hcast] at hzero
  apply hftarget
  exact_mod_cast hzero

/-- Membership in the real affine span of rational generators reflects to
membership in their rational affine span. -/
theorem mem_affineSpan_of_ratCastVector_mem_affineSpan
    [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ) (hι : Nonempty ι)
    (hmem : ratCastVector target ∈
      affineSpan ℝ (Set.range fun i => ratCastVector (vertices i))) :
    target ∈ affineSpan ℚ (Set.range vertices) := by
  classical
  let i₀ : ι := Classical.choice hι
  have hbaseReal : ratCastVector (vertices i₀) ∈
      affineSpan ℝ (Set.range fun i => ratCastVector (vertices i)) :=
    mem_affineSpan ℝ (Set.mem_range_self i₀)
  have hdifferenceReal :
      ratCastVector target - ratCastVector (vertices i₀) ∈
        (affineSpan ℝ
          (Set.range fun i => ratCastVector (vertices i))).direction :=
    (AffineSubspace.vsub_right_mem_direction_iff_mem hbaseReal
      (ratCastVector target)).mpr hmem
  rw [direction_affineSpan,
    vectorSpan_range_eq_span_range_vsub_right ℝ
      (fun i => ratCastVector (vertices i)) i₀] at hdifferenceReal
  have hspanReal : ratCastVector (target - vertices i₀) ∈
      Submodule.span ℝ
        (Set.range fun i => ratCastVector (vertices i - vertices i₀)) := by
    have htarget : ratCastVector (target - vertices i₀) =
        ratCastVector target - ratCastVector (vertices i₀) := by
      ext k
      simp [ratCastVector]
    have hvertices :
        (fun i => ratCastVector (vertices i - vertices i₀)) =
          (fun i => ratCastVector (vertices i) -
            ratCastVector (vertices i₀)) := by
      funext i k
      simp [ratCastVector]
    rw [htarget, hvertices]
    exact hdifferenceReal
  have hspanRat : target - vertices i₀ ∈
      Submodule.span ℚ (Set.range fun i => vertices i - vertices i₀) :=
    mem_span_of_ratCastVector_mem_span
      (fun i => vertices i - vertices i₀) (target - vertices i₀) hspanReal
  have hbaseRat : vertices i₀ ∈ affineSpan ℚ (Set.range vertices) :=
    mem_affineSpan ℚ (Set.mem_range_self i₀)
  apply (AffineSubspace.vsub_right_mem_direction_iff_mem hbaseRat target).mp
  rw [direction_affineSpan,
    vectorSpan_range_eq_span_range_vsub_right ℚ vertices i₀]
  exact hspanRat

/-- A rational point in the real convex hull of rational vertices already
belongs to their rational convex hull.  No finiteness assumption on the index
type is needed because convex-hull membership has finite support. -/
theorem mem_convexHull_of_ratCastVector_mem_convexHull
    [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ)
    (hmem : ratCastVector target ∈
      convexHull ℝ (Set.range fun i => ratCastVector (vertices i))) :
    target ∈ convexHull ℚ (Set.range vertices) := by
  classical
  let support : Finset (κ → ℝ) :=
    Caratheodory.minCardFinsetOfMemConvexHull hmem
  have hsupportSubset : (support : Set (κ → ℝ)) ⊆
      Set.range (fun i => ratCastVector (vertices i)) := by
    exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq hmem
  have hsupportMem : ratCastVector target ∈
      convexHull ℝ (support : Set (κ → ℝ)) := by
    exact Caratheodory.mem_minCardFinsetOfMemConvexHull hmem
  have hsupportNonempty : support.Nonempty :=
    Caratheodory.minCardFinsetOfMemConvexHull_nonempty hmem
  have hsupportIndependent :
      AffineIndependent ℝ ((↑) : support → κ → ℝ) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hmem
  let sourceIndex (point : support) : ι :=
    Classical.choose (hsupportSubset point.property)
  let rationalVertex (point : support) : κ → ℚ :=
    vertices (sourceIndex point)
  have hcastVertex (point : support) :
      ratCastVector (rationalVertex point) = point := by
    exact Classical.choose_spec (hsupportSubset point.property)
  have htargetAffineReal : ratCastVector target ∈
      affineSpan ℝ
        (Set.range fun point : support =>
          ratCastVector (rationalVertex point)) := by
    have hrange :
        (fun point : support => ratCastVector (rationalVertex point)) =
          ((↑) : support → κ → ℝ) := by
      funext point
      exact hcastVertex point
    rw [hrange]
    have hrangeSubtype : Set.range ((↑) : support → κ → ℝ) =
        (support : Set (κ → ℝ)) := by
      ext point
      simp
    rw [hrangeSubtype]
    exact convexHull_subset_affineSpan (support : Set (κ → ℝ)) hsupportMem
  have htargetAffineRat : target ∈
      affineSpan ℚ (Set.range rationalVertex) :=
    mem_affineSpan_of_ratCastVector_mem_affineSpan
      rationalVertex target hsupportNonempty.to_subtype htargetAffineReal
  obtain ⟨rationalWeight, hrationalWeightSum, htargetRational⟩ :=
    eq_affineCombination_of_mem_affineSpan_of_fintype htargetAffineRat
  have hrationalLinear :
      ∑ point : support, rationalWeight point • rationalVertex point = target := by
    rw [← Finset.affineCombination_eq_linear_combination
      Finset.univ rationalVertex rationalWeight hrationalWeightSum]
    exact htargetRational.symm
  rw [Finset.mem_convexHull'] at hsupportMem
  obtain ⟨ambientWeight, hambientWeightNonnegative,
    hambientWeightSum, hambientLinear⟩ := hsupportMem
  let realWeight : support → ℝ := fun point => ambientWeight point
  have hrealWeightNonnegative (point : support) : 0 ≤ realWeight point :=
    hambientWeightNonnegative point point.property
  have hrealWeightSum : ∑ point : support, realWeight point = 1 := by
    simpa only [realWeight, Finset.univ_eq_attach, Finset.sum_attach] using
      hambientWeightSum
  have hrealLinear :
      ∑ point : support, realWeight point • (point : κ → ℝ) =
        ratCastVector target := by
    change (∑ point : support,
      ambientWeight point • (point : κ → ℝ)) = ratCastVector target
    calc
      _ = ∑ point ∈ support.attach,
          ambientWeight point • (point : κ → ℝ) := by
        rw [Finset.univ_eq_attach]
      _ = ∑ point ∈ support, ambientWeight point • point :=
        Finset.sum_attach support (fun point => ambientWeight point • point)
      _ = ratCastVector target := hambientLinear
  let castRationalWeight : support → ℝ :=
    fun point => rationalWeight point
  have hcastRationalWeightSum :
      ∑ point : support, castRationalWeight point = 1 := by
    change (∑ point : support, (rationalWeight point : ℝ)) = 1
    exact_mod_cast hrationalWeightSum
  have hcastRationalLinear :
      ∑ point : support,
          castRationalWeight point • ratCastVector (rationalVertex point) =
        ratCastVector target := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      castRationalWeight, ratCastVector]
    have hcoordinate :
        ∑ point : support,
            rationalWeight point * rationalVertex point k = target k := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun hrationalLinear k
    exact_mod_cast hcoordinate
  have hcastIndependent :
      AffineIndependent ℝ
        (fun point : support => ratCastVector (rationalVertex point)) := by
    simpa only [hcastVertex] using hsupportIndependent
  have hweightEquality : castRationalWeight = realWeight := by
    apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ
      (fun point : support => ratCastVector (rationalVertex point))).mp
      hcastIndependent
    · exact hcastRationalWeightSum
    · exact hrealWeightSum
    · rw [Finset.affineCombination_eq_linear_combination
          Finset.univ _ _ hcastRationalWeightSum,
        Finset.affineCombination_eq_linear_combination
          Finset.univ _ _ hrealWeightSum,
        hcastRationalLinear]
      have hrealLinear' :
          ∑ point : support,
              realWeight point • ratCastVector (rationalVertex point) =
            ratCastVector target := by
        simpa only [hcastVertex] using hrealLinear
      exact hrealLinear'.symm
  have hrationalWeightNonnegative (point : support) :
      0 ≤ rationalWeight point := by
    have hcast : (rationalWeight point : ℝ) = realWeight point := by
      exact congrFun hweightEquality point
    have : (0 : ℝ) ≤ (rationalWeight point : ℝ) := by
      rw [hcast]
      exact hrealWeightNonnegative point
    exact_mod_cast this
  apply mem_convexHull_of_exists_fintype rationalWeight rationalVertex
  · exact hrationalWeightNonnegative
  · exact hrationalWeightSum
  · intro point
    exact Set.mem_range_self (sourceIndex point)
  · exact hrationalLinear

/-- Rational dot product on a finite coordinate space. -/
def rationalDot [Fintype κ] (coefficient point : κ → ℚ) : ℚ :=
  ∑ k, point k * coefficient k

/-- Coordinatewise casting commutes with the finite dot product. -/
theorem dotLinear_ratCastVector_pair [Fintype κ]
    (coefficient point : κ → ℚ) :
    dotLinear (ratCastVector coefficient) (ratCastVector point) =
      (rationalDot coefficient point : ℝ) := by
  simp [rationalDot, ratCastVector]

/-- The open set of real coefficient vectors that strictly place `target`
below every vertex. -/
def realStrictSeparatorSet [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ) : Set (κ → ℝ) :=
  {coefficient | ∀ i,
    dotLinear coefficient (ratCastVector target) <
      dotLinear coefficient (ratCastVector (vertices i))}

/-- Finite dot-product evaluation is continuous in its coefficient vector. -/
theorem continuous_dotLinear_coefficient [Fintype κ] (point : κ → ℝ) :
    Continuous (fun coefficient => dotLinear coefficient point) := by
  have heq : (fun coefficient => dotLinear coefficient point) = dotLinear point := by
    funext coefficient
    simp only [dotLinear_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
  rw [heq]
  exact LinearMap.continuous_of_finiteDimensional (dotLinear point)

/-- Strict finite separation is an open condition on the coefficient
vector. -/
theorem isOpen_realStrictSeparatorSet [Fintype ι] [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ) :
    IsOpen (realStrictSeparatorSet vertices target) := by
  have hopen : IsOpen (⋂ i : ι,
      {coefficient : κ → ℝ |
        dotLinear coefficient (ratCastVector target) <
          dotLinear coefficient (ratCastVector (vertices i))}) := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt
      (continuous_dotLinear_coefficient (ratCastVector target))
      (continuous_dotLinear_coefficient (ratCastVector (vertices i)))
  simpa only [realStrictSeparatorSet, Set.iInter_ofPred] using hopen

/-- Rational coordinate vectors are dense in the corresponding finite real
coordinate space. -/
theorem denseRange_ratCastVector :
    DenseRange (ratCastVector : (κ → ℚ) → κ → ℝ) := by
  have hdense := DenseRange.piMap (fun _ : κ => Rat.denseRange_cast (𝕜 := ℝ))
  have hmap : Pi.map (fun _ : κ => ((↑) : ℚ → ℝ)) =
      (ratCastVector : (κ → ℚ) → κ → ℝ) := by
    funext vector k
    rfl
  rw [← hmap]
  exact hdense

/-- Every strict real separator of finitely many rational points can be
replaced by a strict rational separator. -/
theorem exists_rational_strictSeparator_of_real
    [Fintype ι] [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ)
    {realCoefficient : κ → ℝ}
    (hreal : realCoefficient ∈ realStrictSeparatorSet vertices target) :
    ∃ rationalCoefficient : κ → ℚ, ∀ i,
      rationalDot rationalCoefficient target <
        rationalDot rationalCoefficient (vertices i) := by
  obtain ⟨rationalCoefficient, hcoefficient⟩ :=
    denseRange_ratCastVector.exists_mem_open
      (isOpen_realStrictSeparatorSet vertices target) ⟨realCoefficient, hreal⟩
  refine ⟨rationalCoefficient, fun i => ?_⟩
  have hstrict := hcoefficient i
  rw [dotLinear_ratCastVector_pair, dotLinear_ratCastVector_pair] at hstrict
  exact_mod_cast hstrict

/-- A linear functional on a finite real coordinate space is the dot product
with its values on the standard basis. -/
theorem dotLinear_basis_apply_real [Fintype κ]
    (f : (κ → ℝ) →ₗ[ℝ] ℝ) (x : κ → ℝ) :
    dotLinear (fun k => f ((Pi.basisFun ℝ κ) k)) x = f x := by
  classical
  conv_rhs => rw [← (Pi.basisFun ℝ κ).sum_repr x]
  simp [Pi.basisFun_repr, map_sum]

/-- **Finite rational strict separation.** A rational point outside the
rational convex hull of a finite rational vertex family admits a signed
rational linear functional that is strictly smaller on the point than on
every vertex. -/
theorem exists_rational_strictSeparator_of_not_mem_convexHull
    [Fintype ι] [Fintype κ]
    (vertices : ι → κ → ℚ) (target : κ → ℚ)
    (hnot : target ∉ convexHull ℚ (Set.range vertices)) :
    ∃ coefficient : κ → ℚ, ∀ i,
      rationalDot coefficient target < rationalDot coefficient (vertices i) := by
  have hnotReal : ratCastVector target ∉
      convexHull ℝ (Set.range fun i => ratCastVector (vertices i)) := by
    intro hmem
    exact hnot (mem_convexHull_of_ratCastVector_mem_convexHull
      vertices target hmem)
  obtain ⟨functional, threshold, htarget, hvertices⟩ :=
    geometric_hahn_banach_point_closed
      (convex_convexHull ℝ
        (Set.range fun i => ratCastVector (vertices i)))
      ((Set.finite_range (fun i => ratCastVector (vertices i))).isClosed_convexHull
        (𝕜 := ℝ))
      hnotReal
  let realCoefficient : κ → ℝ :=
    fun k => functional ((Pi.basisFun ℝ κ) k)
  have hreal : realCoefficient ∈ realStrictSeparatorSet vertices target := by
    intro i
    dsimp only [realCoefficient]
    have hevaluation (point : κ → ℝ) :
        dotLinear (fun k => functional ((Pi.basisFun ℝ κ) k)) point =
          functional point := by
      exact dotLinear_basis_apply_real functional.toLinearMap point
    rw [hevaluation, hevaluation]
    exact htarget.trans (hvertices _
      (subset_convexHull ℝ _ (Set.mem_range_self i)))
  exact exists_rational_strictSeparator_of_real
    vertices target hreal

end Ript.ForMathlib.RationalConvexHull
