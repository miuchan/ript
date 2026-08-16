import Mathlib.Probability.Kernel.Category.Stoch
import Ript.Models.FiniteStochastic

/-!
# Exact finite channels as Mathlib stochastic kernels

This semantic bridge interprets the executable exact-rational matrices from
`Ript.Models.FiniteStochastic` in Mathlib's measure-theoretic category `Stoch`.
Every finite carrier receives the discrete measurable space, and every matrix
row becomes the corresponding finite weighted sum of Dirac measures.

The executable source model remains independent of measure theory.  All
noncomputability in this file belongs to the semantic interpretation layer.
-/

set_option autoImplicit false

namespace Ript.Models.Probability.StochFunctor

open CategoryTheory MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MonoidalCategory ProbabilityTheory
open Ript.Models.FiniteStochastic

universe u

noncomputable section

/-- Casting a finite nonnegative-rational sum to `ℝ≥0∞` commutes with
summation. -/
theorem ennreal_coe_nnrat_finset_sum {ι : Type*} (s : Finset ι)
    (p : ι → ℚ≥0) :
    s.sum (fun i ↦ (p i : ℝ≥0∞)) =
      ((s.sum p : ℚ≥0) : ℝ≥0∞) := by
  classical
  have hnnreal :
      s.sum (fun i ↦ (p i : NNReal)) =
        ((s.sum p : ℚ≥0) : NNReal) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih]
  calc
    s.sum (fun i ↦ (p i : ℝ≥0∞)) =
        s.sum (fun i ↦ ((p i : NNReal) : ℝ≥0∞)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (ENNReal.coe_nnratCast (p i)).symm
    _ = ((s.sum (fun i ↦ (p i : NNReal)) : NNReal) : ℝ≥0∞) := by
      exact (map_sum ENNReal.ofNNRealHom (fun i ↦ (p i : NNReal)) s).symm
    _ = (((s.sum p : ℚ≥0) : NNReal) : ℝ≥0∞) :=
      congrArg ENNReal.ofNNReal hnnreal
    _ = ((s.sum p : ℚ≥0) : ℝ≥0∞) :=
      ENNReal.coe_nnratCast _

/-- Casting a product of nonnegative rationals to `ℝ≥0∞` commutes with
multiplication. -/
theorem ennreal_coe_nnrat_mul (a b : ℚ≥0) :
    ((a * b : ℚ≥0) : ℝ≥0∞) = (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
  calc
    ((a * b : ℚ≥0) : ℝ≥0∞) =
        (((a * b : ℚ≥0) : NNReal) : ℝ≥0∞) :=
      (ENNReal.coe_nnratCast _).symm
    _ = (((a : NNReal) * (b : NNReal) : NNReal) : ℝ≥0∞) := by
      rw [NNRat.cast_mul]
    _ = ((a : NNReal) : ℝ≥0∞) * ((b : NNReal) : ℝ≥0∞) :=
      ENNReal.coe_mul _ _
    _ = (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
      rw [ENNReal.coe_nnratCast, ENNReal.coe_nnratCast]

/-- The nonnegative-rational zero casts to the `ℝ≥0∞` zero. -/
@[simp]
theorem ennreal_coe_nnrat_zero : ((0 : ℚ≥0) : ℝ≥0∞) = 0 := by
  calc
    ((0 : ℚ≥0) : ℝ≥0∞) = (((0 : ℚ≥0) : NNReal) : ℝ≥0∞) :=
      (ENNReal.coe_nnratCast 0).symm
    _ = 0 := by simp

/-- The nonnegative-rational one casts to the `ℝ≥0∞` one. -/
@[simp]
theorem ennreal_coe_nnrat_one : ((1 : ℚ≥0) : ℝ≥0∞) = 1 := by
  calc
    ((1 : ℚ≥0) : ℝ≥0∞) = (((1 : ℚ≥0) : NNReal) : ℝ≥0∞) :=
      (ENNReal.coe_nnratCast 1).symm
    _ = 1 := by simp

/-- Fintype-specialized form of `ennreal_coe_nnrat_finset_sum`. -/
theorem ennreal_coe_nnrat_fintype_sum {ι : Type*} [Fintype ι]
    (p : ι → ℚ≥0) :
    ∑ i, (p i : ℝ≥0∞) = ((∑ i, p i : ℚ≥0) : ℝ≥0∞) := by
  simpa using ennreal_coe_nnrat_finset_sum Finset.univ p

/-- A finite executable carrier equipped with its discrete measurable space. -/
abbrev discreteSFinKer (X : Object.{u}) : SFinKer.{u} :=
  @SFinKer.of X ⊤

/-- A finite executable carrier regarded as an object of Mathlib's `Stoch`. -/
abbrev discreteStoch (X : Object.{u}) : Stoch.{u} :=
  ⟨discreteSFinKer X⟩

/-- The exact probability row of a finite stochastic matrix, interpreted as a
finite weighted sum of Dirac measures. -/
def rowMeasure {X Y : Object.{u}} (f : FinStoch X Y) (x : X) :
    @Measure Y ⊤ := by
  letI : MeasurableSpace Y := ⊤
  exact ∑ y : Y, (f.prob x y : ℝ≥0∞) • Measure.dirac y

/-- Evaluation of an interpreted row on an arbitrary set. -/
theorem rowMeasure_apply {X Y : Object.{u}} (f : FinStoch X Y) (x : X)
    (s : Set Y) :
    rowMeasure f x s =
      ∑ y : Y, (f.prob x y : ℝ≥0∞) * s.indicator 1 y := by
  simp [rowMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.of_discrete, smul_eq_mul]

/-- Interpreted rows retain the source matrix's normalization exactly. -/
theorem rowMeasure_univ {X Y : Object.{u}} (f : FinStoch X Y) (x : X) :
    rowMeasure f x Set.univ = 1 := by
  rw [rowMeasure_apply]
  simp only [Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  rw [ennreal_coe_nnrat_fintype_sum, f.normalized]
  calc
    ((1 : ℚ≥0) : ℝ≥0∞) = (((1 : ℚ≥0) : NNReal) : ℝ≥0∞) :=
      (ENNReal.coe_nnratCast 1).symm
    _ = 1 := by simp

/-- Singleton mass recovers the original exact matrix entry. -/
@[simp]
theorem rowMeasure_singleton {X Y : Object.{u}} (f : FinStoch X Y)
    (x : X) (y : Y) :
    rowMeasure f x {y} = (f.prob x y : ℝ≥0∞) := by
  rw [rowMeasure_apply]
  simp [Set.indicator, eq_comm]

/-- Integrating over an interpreted row is a finite exact weighted sum. -/
theorem lintegral_rowMeasure {X Y : Object.{u}} (f : FinStoch X Y)
    (x : X) (g : Y → ℝ≥0∞) :
    @lintegral Y ⊤ (rowMeasure f x) g =
      ∑ y : Y, (f.prob x y : ℝ≥0∞) * g y := by
  simp [rowMeasure, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac]

/-- Every interpreted exact row is a probability measure. -/
instance rowMeasureIsProbability {X Y : Object.{u}} (f : FinStoch X Y)
    (x : X) : IsProbabilityMeasure (rowMeasure f x) :=
  ⟨rowMeasure_univ f x⟩

/-- The Markov kernel induced by an exact finite stochastic channel. -/
def toKernel {X Y : Object.{u}} (f : FinStoch X Y) :
    @Kernel X Y ⊤ ⊤ := by
  letI : MeasurableSpace X := ⊤
  letI : MeasurableSpace Y := ⊤
  exact Kernel.ofFunOfCountable (rowMeasure f)

/-- The interpreted kernel is Markov because every source row is normalized. -/
instance toKernelIsMarkov {X Y : Object.{u}} (f : FinStoch X Y) :
    @IsMarkovKernel X Y ⊤ ⊤ (toKernel f) :=
  ⟨fun x ↦ rowMeasureIsProbability f x⟩

/-- Applying the interpreted kernel returns the interpreted source row. -/
@[simp]
theorem toKernel_apply {X Y : Object.{u}} (f : FinStoch X Y) (x : X) :
    toKernel f x = rowMeasure f x :=
  rfl

/-- Interpreting the finite identity matrix gives Mathlib's identity kernel. -/
theorem toKernel_identity (X : Object.{u}) :
    toKernel (FinStoch.identity X) = (@Kernel.id X ⊤) := by
  apply @Kernel.ext X X ⊤ ⊤
  intro x
  apply @Measure.ext_of_singleton X ⊤ (by infer_instance)
  intro y
  by_cases h : x = y <;>
    simp [Kernel.id_apply, FinStoch.identity, Set.indicator, h]

/-- Interpreting Chapman--Kolmogorov composition gives kernel composition. -/
theorem toKernel_comp {X Y Z : Object.{u}} (f : FinStoch X Y)
    (g : FinStoch Y Z) :
    toKernel (FinStoch.comp f g) = toKernel g ∘ₖ toKernel f := by
  apply @Kernel.ext X Z ⊤ ⊤
  intro x
  apply @Measure.ext_of_singleton Z ⊤ (by infer_instance)
  intro z
  rw [Kernel.comp_apply' _ _ _ MeasurableSpace.measurableSet_top]
  simp only [toKernel_apply, rowMeasure_singleton, lintegral_rowMeasure,
    FinStoch.comp]
  rw [← ennreal_coe_nnrat_fintype_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact ennreal_coe_nnrat_mul _ _

/-- An exact finite channel packaged as a morphism of Mathlib's `Stoch`. -/
def toStochHom {X Y : Object.{u}} (f : FinStoch X Y) :
    discreteStoch X ⟶ discreteStoch Y :=
  ⟨⟨toKernel f, inferInstance⟩, inferInstance⟩

/-- The measure-theoretic interpretation is a functor from exact executable
finite channels to Mathlib's category of stochastic kernels. -/
def toStoch : Object.{u} ⥤ Stoch.{u} where
  obj X := discreteStoch X
  map f := toStochHom f
  map_id X := by
    apply WideSubcategory.hom_ext
    apply SFinKer.hom_ext
    exact toKernel_identity X
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SFinKer.hom_ext
    exact toKernel_comp f g

/-- A finite function interpreted directly as Mathlib's deterministic
kernel between discrete measurable spaces. -/
def discreteDeterministicKernel {X Y : Object.{u}} (f : X → Y) :
    @Kernel X Y ⊤ ⊤ := by
  letI : MeasurableSpace X := ⊤
  letI : MeasurableSpace Y := ⊤
  exact Kernel.deterministic f Measurable.of_discrete

/-- A discrete deterministic kernel is Markov. -/
instance discreteDeterministicKernelIsMarkov {X Y : Object.{u}} (f : X → Y) :
    @IsMarkovKernel X Y ⊤ ⊤ (discreteDeterministicKernel f) := by
  unfold discreteDeterministicKernel
  apply Kernel.isMarkovKernel_deterministic

/-- Interpreting a finite Dirac channel agrees with Mathlib's deterministic
kernel constructor. -/
theorem toKernel_dirac {X Y : Object.{u}} (f : X → Y) :
    toKernel (FinStoch.dirac f) = discreteDeterministicKernel f := by
  apply @Kernel.ext X Y ⊤ ⊤
  intro x
  apply @Measure.ext_of_singleton Y ⊤ (by infer_instance)
  intro y
  by_cases h : f x = y <;>
    simp [discreteDeterministicKernel, Kernel.deterministic_apply,
      FinStoch.dirac, Set.indicator, h]

/-- A finite deterministic function packaged directly as a `Stoch`
morphism. -/
def discreteDeterministicHom {X Y : Object.{u}} (f : X → Y) :
    discreteStoch X ⟶ discreteStoch Y :=
  ⟨⟨discreteDeterministicKernel f, inferInstance⟩, inferInstance⟩

/-- The functor preserves deterministic channels: finite Dirac matrices map
to Mathlib deterministic kernels. -/
theorem toStoch_map_dirac {X Y : Object.{u}} (f : X → Y) :
    toStoch.map (FinStoch.dirac f) = discreteDeterministicHom f := by
  apply WideSubcategory.hom_ext
  apply SFinKer.hom_ext
  exact toKernel_dirac f

/-- The direct cast from nonnegative rationals into `ℝ≥0∞` is injective. -/
theorem ennreal_coe_nnrat_injective :
    Function.Injective (fun q : ℚ≥0 ↦ (q : ℝ≥0∞)) := by
  intro a b h
  have hnnreal : (a : NNReal) = (b : NNReal) := by
    apply ENNReal.coe_injective
    simpa only [ENNReal.coe_nnratCast] using h
  exact_mod_cast hnnreal

/-- A Markov kernel is s-finite, stated as an explicit theorem so semantic
bridges with two measurable structures on one carrier need not rely on
typeclass search choosing one of them. -/
theorem isSFiniteKernel_of_isMarkovKernel
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {κ : @Kernel α β mα mβ} (hκ : IsMarkovKernel κ) :
    IsSFiniteKernel κ := by
  let hzero : IsZeroOrMarkovKernel κ :=
    @IsMarkovKernel.IsZeroOrMarkovKernel α β mα mβ κ hκ
  let hfinite : IsFiniteKernel κ :=
    @IsZeroOrMarkovKernel.isFiniteKernel α β mα mβ κ hzero
  exact @Kernel.IsFiniteKernel.isSFiniteKernel α β mα mβ κ hfinite

/-- The semantic bridge is faithful: no exact finite matrix entries are lost
by passage to measure-theoretic kernels. -/
instance toStochFaithful : toStoch.Faithful where
  map_injective h := by
    apply FinStoch.ext
    intro x y
    have hk : toKernel _ = toKernel _ :=
      congrArg (fun k ↦ k.hom.hom) h
    have hentry := congrArg (fun k ↦ k x {y}) hk
    simp only [toKernel_apply, rowMeasure_singleton] at hentry
    exact ennreal_coe_nnrat_injective hentry

/-- Equality of interpreted stochastic kernels is equivalent to equality of
the source exact channels. -/
theorem toStoch_map_eq_iff {X Y : Object.{u}} (f g : FinStoch X Y) :
    toStoch.map f = toStoch.map g ↔ f = g := by
  constructor
  · intro h
    exact toStoch.map_injective h
  · intro h
    exact congrArg toStoch.map h

/-- On finite discrete carriers, Mathlib's product measurable space contains
every set and therefore equals the discrete top measurable space. -/
theorem productMeasurableSpace_eq_top (X Y : Object.{u}) :
    @MeasurableSpace.prod X Y ⊤ ⊤ = ⊤ := by
  apply le_antisymm le_top
  intro s _
  exact @MeasurableSet.of_discrete (X × Y)
    (@MeasurableSpace.prod X Y ⊤ ⊤) (by infer_instance) s

/-- The product measurable space induced by two explicit discrete spaces. -/
abbrev finiteProductMeasurableSpace (X Y : Object.{u}) :
    MeasurableSpace (X × Y) :=
  @MeasurableSpace.prod X Y ⊤ ⊤

/-- After identifying the finite product σ-algebra with `⊤`, tensoring two
interpreted objects is literally the interpreted finite product object. -/
theorem tensorObject_eq (X Y : Object.{u}) :
    discreteStoch X ⊗ discreteStoch Y =
      discreteStoch (Object.tensor X Y) := by
  have h := productMeasurableSpace_eq_top X Y
  exact congrArg
    (fun m : MeasurableSpace (X × Y) ↦
      (⟨@SFinKer.of (X × Y) m⟩ : Stoch)) h

/-- The identity map from Mathlib's product measurable structure to `⊤` is
measurable because the finite product space is discrete. -/
theorem tensorComparisonForwardMeasurable (X Y : Object.{u}) :
    @Measurable (X × Y) (X × Y)
      (finiteProductMeasurableSpace X Y) ⊤ id :=
  @Measurable.of_discrete (X × Y) (X × Y)
    (finiteProductMeasurableSpace X Y) ⊤ (by infer_instance) id

/-- The reverse identity map from `⊤` is measurable by definition. -/
theorem tensorComparisonBackwardMeasurable (X Y : Object.{u}) :
    @Measurable (X × Y) (X × Y) ⊤
      (finiteProductMeasurableSpace X Y) id := by
  intro _ _
  exact MeasurableSpace.measurableSet_top

/-- Identity kernel from Mathlib's product measurable structure to the
explicit top measurable structure on the same finite product carrier. -/
def tensorComparisonForwardKernel (X Y : Object.{u}) :
    @Kernel (X × Y) (X × Y) (finiteProductMeasurableSpace X Y) ⊤ :=
  Kernel.deterministic id (tensorComparisonForwardMeasurable X Y)

/-- The forward comparison kernel is Markov. -/
instance tensorComparisonForwardKernelIsMarkov (X Y : Object.{u}) :
    IsMarkovKernel (tensorComparisonForwardKernel X Y) := by
  unfold tensorComparisonForwardKernel
  apply Kernel.isMarkovKernel_deterministic

/-- The forward comparison kernel is s-finite. -/
instance tensorComparisonForwardKernelIsSFinite (X Y : Object.{u}) :
    IsSFiniteKernel (tensorComparisonForwardKernel X Y) :=
  isSFiniteKernel_of_isMarkovKernel
    (tensorComparisonForwardKernelIsMarkov X Y)

/-- Identity kernel in the reverse direction, from `⊤` to Mathlib's product
measurable structure. -/
def tensorComparisonBackwardKernel (X Y : Object.{u}) :
    @Kernel (X × Y) (X × Y) ⊤ (finiteProductMeasurableSpace X Y) :=
  Kernel.deterministic id (tensorComparisonBackwardMeasurable X Y)

/-- The backward comparison kernel is Markov. -/
instance tensorComparisonBackwardKernelIsMarkov (X Y : Object.{u}) :
    IsMarkovKernel (tensorComparisonBackwardKernel X Y) := by
  unfold tensorComparisonBackwardKernel
  apply Kernel.isMarkovKernel_deterministic

/-- The backward comparison kernel is s-finite. -/
instance tensorComparisonBackwardKernelIsSFinite (X Y : Object.{u}) :
    IsSFiniteKernel (tensorComparisonBackwardKernel X Y) :=
  isSFiniteKernel_of_isMarkovKernel
    (tensorComparisonBackwardKernelIsMarkov X Y)

/-- The two identity comparison kernels compose to the product-space identity. -/
theorem tensorComparison_forward_backward (X Y : Object.{u}) :
    tensorComparisonBackwardKernel X Y ∘ₖ
      tensorComparisonForwardKernel X Y =
        (@Kernel.id (X × Y) (finiteProductMeasurableSpace X Y)) := by
  unfold tensorComparisonForwardKernel tensorComparisonBackwardKernel
  rw [Kernel.deterministic_comp_deterministic]
  rfl

/-- The comparison kernels also compose to the explicitly discrete identity. -/
theorem tensorComparison_backward_forward (X Y : Object.{u}) :
    tensorComparisonForwardKernel X Y ∘ₖ
      tensorComparisonBackwardKernel X Y = (@Kernel.id (X × Y) ⊤) := by
  unfold tensorComparisonForwardKernel tensorComparisonBackwardKernel
  rw [Kernel.deterministic_comp_deterministic]
  rfl

/-- Forward comparison packaged as a `Stoch` morphism. -/
def tensorComparisonHom (X Y : Object.{u}) :
    (discreteStoch X ⊗ discreteStoch Y) ⟶
      discreteStoch (Object.tensor X Y) :=
  ⟨⟨tensorComparisonForwardKernel X Y,
      tensorComparisonForwardKernelIsSFinite X Y⟩,
    tensorComparisonForwardKernelIsMarkov X Y⟩

/-- Backward comparison packaged as a `Stoch` morphism. -/
def tensorComparisonInv (X Y : Object.{u}) :
    discreteStoch (Object.tensor X Y) ⟶
      (discreteStoch X ⊗ discreteStoch Y) :=
  ⟨⟨tensorComparisonBackwardKernel X Y,
      tensorComparisonBackwardKernelIsSFinite X Y⟩,
    tensorComparisonBackwardKernelIsMarkov X Y⟩

/-- Canonical stochastic isomorphism comparing the product measurable object
with the explicitly discrete interpretation of the finite product carrier. -/
def tensorComparison (X Y : Object.{u}) :
    (discreteStoch X ⊗ discreteStoch Y) ≅
      discreteStoch (Object.tensor X Y) where
  hom := tensorComparisonHom X Y
  inv := tensorComparisonInv X Y
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply SFinKer.hom_ext
    change tensorComparisonBackwardKernel X Y ∘ₖ
      tensorComparisonForwardKernel X Y = Kernel.id
    exact tensorComparison_forward_backward X Y
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply SFinKer.hom_ext
    change tensorComparisonForwardKernel X Y ∘ₖ
      tensorComparisonBackwardKernel X Y = Kernel.id
    exact tensorComparison_backward_forward X Y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Singleton evaluation of an interpreted tensor channel, with the finite
product carriers exposed explicitly for later kernel calculations. -/
theorem toKernel_tensor_singleton
    {W X Y Z : Object.{u}} (f : FinStoch W X) (g : FinStoch Y Z)
    (input : Object.tensor W Y) (output : Object.tensor X Z) :
    (toKernel (FinStoch.tensor f g) input) {output} =
      ((FinStoch.tensor f g).prob input output : ℝ≥0∞) := by
  rw [toKernel_apply, rowMeasure_singleton]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The semantic functor preserves independent parallel composition, up to
the canonical identification between Mathlib's product measurable object and
the explicit finite discrete product object. -/
theorem toStoch_map_tensor
    {W X Y Z : Object.{u}} (f : FinStoch W X) (g : FinStoch Y Z) :
    (toStoch.map f ⊗ₘ toStoch.map g) ≫ (tensorComparison X Z).hom =
      (tensorComparison W Y).hom ≫ toStoch.map (FinStoch.tensor f g) := by
  apply WideSubcategory.hom_ext
  apply SFinKer.hom_ext
  apply Kernel.ext
  intro input
  change Object.tensor W Y at input
  apply @Measure.ext_of_singleton (X × Z) ⊤ (by infer_instance)
  intro output
  change Object.tensor X Z at output
  dsimp [tensorComparison, tensorComparisonHom, toStoch, toStochHom]
  simp only [SFinKer.comp_hom, MonoidalCategory.tensorHom_def,
    SFinKer.whiskerRight_hom, SFinKer.whiskerLeft_hom]
  rw [Kernel.id_parallelComp_comp_parallelComp_id]
  change
    ((tensorComparisonForwardKernel X Z ∘ₖ
        (toKernel f ∥ₖ toKernel g)) input) {output} =
      ((toKernel (FinStoch.tensor f g) ∘ₖ
        tensorComparisonForwardKernel W Y) input) {output}
  unfold tensorComparisonForwardKernel
  rw [Kernel.deterministic_comp_eq_map,
    Kernel.map_apply' _ (tensorComparisonForwardMeasurable X Z) _
      MeasurableSpace.measurableSet_top]
  simp only [Set.preimage_id]
  rw [Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply _ (tensorComparisonForwardMeasurable W Y)]
  have hsingleton : {output} = {output.1} ×ˢ {output.2} := by
    rcases output with ⟨x, z⟩
    exact Set.singleton_prod_singleton.symm
  conv_lhs => rw [hsingleton]
  rw [Kernel.parallelComp_apply_prod]
  simp only [toKernel_apply, rowMeasure_singleton, id_eq]
  have htensor :=
    @toKernel_tensor_singleton W X Y Z f g input output
  calc
    (f.prob input.1 output.1 : ℝ≥0∞) *
          (g.prob input.2 output.2 : ℝ≥0∞) =
        ((FinStoch.tensor f g).prob input output : ℝ≥0∞) := by
      rw [FinStoch.tensor_apply]
      exact (ennreal_coe_nnrat_mul _ _).symm
    _ = (toKernel (FinStoch.tensor f g) input) {output} :=
      htensor.symm



end

end Ript.Models.Probability.StochFunctor
