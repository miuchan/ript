import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Ript.Models.FiniteDistribution
import Ript.Models.Quantum.CompletePositivity

/-!
# Classical stochastic channels inside finite quantum theory

This file realizes an exact finite stochastic channel as a measurement--
preparation quantum channel.  The Kraus operator labelled by `(x, y)` is

`sqrt(P(y | x)) |y><x|`.

Consequently the channel measures in the distinguished classical basis and
prepares a diagonal output state.  In particular, the stochastic identity is
represented by dephasing rather than by the identity on every quantum state.
The categorical embedding below therefore targets the dephasing-idempotent
classical subcategory of quantum channels; this distinction prevents a false
claim that measurement--preparation preserves the ambient quantum identity.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum.ClassicalEmbedding

open Matrix TensorProduct
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker TensorProduct

open CategoryTheory
open Ript.Models.FiniteStochastic

universe u

/-- Regard a finite classical object as a quantum system with its classical
basis as the distinguished orthonormal basis. -/
abbrev classicalObject (X : FiniteStochastic.Object.{u}) : Object.{u} :=
  ⟨X, inferInstance, inferInstance⟩

/-- Nonnegative real square root of an exact rational probability, embedded
in the complex scalars. -/
noncomputable def probabilityAmplitude (p : ℚ≥0) : ℂ :=
  (Real.sqrt (p : ℝ) : ℂ)

/-- The squared magnitude of the chosen probability amplitude is the original
exact rational probability. -/
theorem probabilityAmplitude_star_mul (p : ℚ≥0) :
    star (probabilityAmplitude p) * probabilityAmplitude p = (p : ℂ) := by
  rw [probabilityAmplitude]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
  · norm_cast
  · exact_mod_cast p.coe_nonneg

/-- The reverse-ordered squared magnitude of a probability amplitude is also
the original probability. -/
theorem probabilityAmplitude_mul_star (p : ℚ≥0) :
    probabilityAmplitude p * star (probabilityAmplitude p) = (p : ℂ) := by
  rw [mul_comm, probabilityAmplitude_star_mul]

/-- Multiplication by a probability amplitude and its conjugate scales an
arbitrary complex entry by the corresponding probability. -/
theorem probabilityAmplitude_mul_middle_star (p : ℚ≥0) (z : ℂ) :
    probabilityAmplitude p * z * star (probabilityAmplitude p) =
      (p : ℂ) * z := by
  calc
    probabilityAmplitude p * z * star (probabilityAmplitude p) =
        (probabilityAmplitude p * star (probabilityAmplitude p)) * z := by
      ring
    _ = (p : ℂ) * z := by rw [probabilityAmplitude_mul_star]

variable {X Y Z : FiniteStochastic.Object.{u}}

/-- Embed an exact finite distribution as the diagonal density matrix in the
distinguished classical basis. -/
noncomputable def diagonalDensity
    (p : FiniteDistribution.FinDist X) : DensityMatrix (classicalObject X) where
  matrix := Matrix.diagonal fun x ↦ (p.prob x : ℂ)
  posSemidef := Matrix.PosSemidef.diagonal (by
    intro x
    change (0 : ℂ) ≤ (((p.prob x : ℚ) : ℝ) : ℂ)
    rw [Complex.zero_le_real]
    exact_mod_cast (p.prob x).coe_nonneg)
  trace_one := by
    rw [Matrix.trace_diagonal, ← NNRat.cast_sum, p.normalized]
    norm_num

/-- The underlying matrix of a diagonal classical density operator. -/
@[simp]
theorem diagonalDensity_matrix (p : FiniteDistribution.FinDist X) :
    (diagonalDensity p).matrix = Matrix.diagonal fun x ↦ (p.prob x : ℂ) :=
  rfl

/-- The rank-one Kraus operator associated with a classical transition
`x ↦ y`. -/
noncomputable def transitionOperator (f : FinStoch X Y) (pair : X × Y) :
    Matrix (classicalObject Y) (classicalObject X) ℂ :=
  Matrix.single pair.2 pair.1
    (probabilityAmplitude (f.prob pair.1 pair.2))

/-- The transition operators of a normalized stochastic matrix satisfy the
Kraus completeness equation. -/
theorem transitionOperator_complete (f : FinStoch X Y) :
    ∑ pair : X × Y,
        (transitionOperator f pair)ᴴ * transitionOperator f pair = 1 := by
  ext x x'
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [transitionOperator, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same, Matrix.single_apply,
    probabilityAmplitude_star_mul]
  by_cases h : x = x'
  · subst x'
    simp
    rw [← NNRat.cast_sum, f.normalized]
    norm_num
  · have hpair : ∀ a : X, ¬(a = x ∧ a = x') := by
      intro a ha
      exact h (ha.1.symm.trans ha.2)
    simp only [hpair, if_false, Finset.sum_const_zero]
    rw [Matrix.one_apply]
    simp [h]

/-- Measurement in the input classical basis followed by preparation in the
output classical basis, with probabilities supplied by `f`. -/
noncomputable def measurementPreparation (f : FinStoch X Y) :
    KrausChannel (classicalObject X) (classicalObject Y) :=
  KrausChannel.ofOperators
    (transitionOperator f) (transitionOperator_complete f)

/-- Operational matrix-entry formula for a measurement--preparation channel.
All coherences are discarded, and the diagonal evolves by the stochastic
matrix. -/
theorem measurementPreparation_map_apply (f : FinStoch X Y)
    (ρ : Matrix (classicalObject X) (classicalObject X) ℂ) (y y' : Y) :
    (measurementPreparation f).map ρ y y' =
      if y = y' then ∑ x, (f.prob x y : ℂ) * ρ x x else 0 := by
  rw [measurementPreparation]
  simp only [KrausChannel.ofOperators, Matrix.sum_apply,
    transitionOperator, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single, Matrix.single_apply,
    probabilityAmplitude_mul_middle_star]
  rw [Fintype.sum_prod_type]
  by_cases h : y = y'
  · subst y'
    simp
  · have hpair : ∀ b : Y, ¬(b = y ∧ b = y') := by
      intro b hb
      exact h (hb.1.symm.trans hb.2)
    rw [if_neg h]
    simp [hpair]

/-- On diagonal classical states, measurement--preparation agrees exactly with
finite-distribution pushforward through the stochastic channel. -/
theorem measurementPreparation_diagonalDensity
    (p : FiniteDistribution.FinDist X) (f : FinStoch X Y) :
    (measurementPreparation f).applyDensity (diagonalDensity p) =
      diagonalDensity (p.push f) := by
  apply DensityMatrix.ext
  ext y y'
  rw [KrausChannel.applyDensity_matrix, diagonalDensity_matrix,
    measurementPreparation_map_apply, diagonalDensity_matrix]
  by_cases h : y = y'
  · subst y'
    simp only [ite_true, Matrix.diagonal_apply_eq,
      FiniteDistribution.FinDist.push_apply, NNRat.cast_sum,
      NNRat.cast_mul]
    apply Fintype.sum_congr
    intro x
    ring
  · simp [h]

/-- Measurement--preparation respects Chapman--Kolmogorov composition as an
equality of quantum channels. -/
theorem measurementPreparation_comp (f : FinStoch X Y) (g : FinStoch Y Z) :
    measurementPreparation (FinStoch.comp f g) =
      KrausChannel.comp (measurementPreparation f)
        (measurementPreparation g) := by
  apply KrausChannel.ext
  funext ρ
  ext z z'
  rw [measurementPreparation_map_apply, KrausChannel.comp_map,
    measurementPreparation_map_apply]
  by_cases h : z = z'
  · subst z'
    simp only [ite_true]
    simp_rw [measurementPreparation_map_apply, if_pos]
    simp only [FinStoch.comp, NNRat.cast_sum, NNRat.cast_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro y
    apply Fintype.sum_congr
    intro x
    ring
  · rw [if_neg h]
    simp [h]

/-- Measurement--preparation is faithful: all stochastic entries can be
recovered by evaluating the channel on classical basis projectors. -/
theorem measurementPreparation_faithful {f g : FinStoch X Y}
    (h : measurementPreparation f = measurementPreparation g) : f = g := by
  apply FinStoch.ext
  intro x y
  have hEntry := congrArg
    (fun channel ↦ channel.map (Matrix.single x x 1) y y) h
  rw [measurementPreparation_map_apply, measurementPreparation_map_apply]
    at hEntry
  simp only [ite_true, Matrix.single_apply] at hEntry
  simp at hEntry
  exact NNRat.cast_injective hEntry

private theorem linearMap_ext_kronecker
    {W X Y Z : FiniteStochastic.Object.{u}}
    {f g : Matrix (W × X) (W × X) ℂ →ₗ[ℂ]
      Matrix (Y × Z) (Y × Z) ℂ}
    (h : ∀ (ρ : Matrix W W ℂ) (σ : Matrix X X ℂ),
      f (ρ ⊗ₖ σ) = g (ρ ⊗ₖ σ)) : f = g := by
  apply LinearMap.ext
  intro τ
  let e : Matrix W W ℂ ⊗[ℂ] Matrix X X ℂ ≃ₗ[ℂ]
      Matrix (W × X) (W × X) ℂ := kroneckerLinearEquiv W W X X ℂ
  rw [← e.apply_symm_apply τ]
  induction e.symm τ using TensorProduct.induction_on with
  | zero => simp
  | tmul ρ σ =>
      simp only [e, kroneckerLinearEquiv_tmul]
      exact h ρ σ
  | add a b ha hb => rw [e.map_add, f.map_add, g.map_add, ha, hb]

/-- Measurement--preparation preserves independent parallel composition as an
equality of quantum channels on every matrix, including entangled inputs. -/
theorem measurementPreparation_tensor
    {W X Y Z : FiniteStochastic.Object.{u}}
    (f : FinStoch W X) (g : FinStoch Y Z) :
    measurementPreparation (FinStoch.tensor f g) =
      KrausChannel.tensor (measurementPreparation f)
        (measurementPreparation g) := by
  apply KrausChannel.ext
  funext τ
  have hLinear :
      (measurementPreparation (FinStoch.tensor f g)).toLinearMap =
        (KrausChannel.tensor (measurementPreparation f)
          (measurementPreparation g)).toLinearMap := by
    apply linearMap_ext_kronecker
    intro ρ σ
    change (measurementPreparation (FinStoch.tensor f g)).map (ρ ⊗ₖ σ) =
      (KrausChannel.tensor (measurementPreparation f)
        (measurementPreparation g)).map (ρ ⊗ₖ σ)
    rw [KrausChannel.tensor_map_kronecker]
    ext ⟨x, z⟩ ⟨x', z'⟩
    let ρσ : Matrix
        (classicalObject (FiniteStochastic.Object.tensor W Y))
        (classicalObject (FiniteStochastic.Object.tensor W Y)) ℂ :=
      ρ ⊗ₖ σ
    change (measurementPreparation (FinStoch.tensor f g)).map ρσ
        (x, z) (x', z') =
      (measurementPreparation f).map ρ x x' *
        (measurementPreparation g).map σ z z'
    have hLeft := measurementPreparation_map_apply
      (FinStoch.tensor f g) ρσ (x, z) (x', z')
    rw [hLeft]
    rw [measurementPreparation_map_apply, measurementPreparation_map_apply]
    simp only [ρσ, FiniteStochastic.Object.tensor]
    by_cases hx : x = x' <;> by_cases hz : z = z'
    · subst x'
      subst z'
      simp only [ite_true, FinStoch.tensor_apply, NNRat.cast_mul]
      change (∑ input : W × Y,
          ((f.prob input.1 x : ℂ) * (g.prob input.2 z : ℂ)) *
            (ρ input.1 input.1 * σ input.2 input.2)) =
        (∑ w, (f.prob w x : ℂ) * ρ w w) *
          ∑ y, (g.prob y z : ℂ) * σ y y
      rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
      apply Fintype.sum_congr
      intro w
      apply Fintype.sum_congr
      intro y
      ring
    · simp [hx, hz]
    · simp [hx, hz]
    · simp [hx, hz]
  exact congrArg (fun linear ↦ linear τ) hLinear

/-- Complete dephasing in the distinguished classical basis.  It is the image
of the classical stochastic identity, not the ambient quantum identity. -/
noncomputable def dephase (X : FiniteStochastic.Object.{u}) :
    KrausChannel (classicalObject X) (classicalObject X) :=
  measurementPreparation (FinStoch.identity X)

/-- Complete dephasing is idempotent. -/
theorem dephase_idempotent (X : FiniteStochastic.Object.{u}) :
    KrausChannel.comp (dephase X) (dephase X) = dephase X := by
  simp only [dephase]
  rw [← measurementPreparation_comp]
  congr 1
  apply FinStoch.ext
  intro x y
  simp [FinStoch.comp, FinStoch.identity]

/-- Dephasing the product basis is the tensor product of the factor
dephasing channels. -/
theorem dephase_tensor (X Y : FiniteStochastic.Object.{u}) :
    dephase (FiniteStochastic.Object.tensor X Y) =
      KrausChannel.tensor (dephase X) (dephase Y) := by
  calc
    dephase (FiniteStochastic.Object.tensor X Y) =
        measurementPreparation
          (FinStoch.identity (FiniteStochastic.Object.tensor X Y)) := rfl
    _ = measurementPreparation
          (FinStoch.tensor (FinStoch.identity X) (FinStoch.identity Y)) := by
      congr 1
      exact (FinStoch.tensor_id X Y).symm
    _ = KrausChannel.tensor (dephase X) (dephase Y) := by
      simpa only [dephase] using
        (measurementPreparation_tensor (FinStoch.identity X)
          (FinStoch.identity Y))

/-! ## The dephasing-idempotent classical quantum category -/

namespace ClassicalQuantum

/-- A classical quantum object is a finite classical basis, interpreted as a
quantum system together with its canonical dephasing idempotent. -/
structure Object where
  /-- The finite classical carrier and its executable structure. -/
  classical : FiniteStochastic.Object.{u}

/-- The ambient finite quantum object underlying a classical quantum object. -/
abbrev quantumObject (X : Object.{u}) : Quantum.Object.{u} :=
  classicalObject X.classical

/-- A classical quantum channel is an ambient Kraus channel invariant under
source and target dephasing.  Equivalently, it is a morphism in the full
dephasing-idempotent (Karoubi-style) subcategory. -/
structure Channel (X Y : Object.{u}) where
  /-- The underlying completely positive trace-preserving Kraus channel. -/
  toKraus : KrausChannel (quantumObject X) (quantumObject Y)
  /-- Precomposing by source dephasing does not change the channel. -/
  source_dephase :
    KrausChannel.comp (dephase X.classical) toKraus = toKraus
  /-- Postcomposing by target dephasing does not change the channel. -/
  target_dephase :
    KrausChannel.comp toKraus (dephase Y.classical) = toKraus

/-- Classical quantum channels are equal when their ambient Kraus channels
are equal. -/
@[ext]
theorem Channel.ext {X Y : Object.{u}} (f g : Channel X Y)
    (h : f.toKraus = g.toKraus) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity in the classical quantum category is the object's dephasing
idempotent. -/
noncomputable def Channel.identity (X : Object.{u}) : Channel X X where
  toKraus := dephase X.classical
  source_dephase := dephase_idempotent X.classical
  target_dephase := dephase_idempotent X.classical

/-- Serial composition of dephasing-compatible channels. -/
noncomputable def Channel.comp {X Y Z : Object.{u}}
    (f : Channel X Y) (g : Channel Y Z) : Channel X Z where
  toKraus := KrausChannel.comp f.toKraus g.toKraus
  source_dephase := by
    apply KrausChannel.ext
    funext ρ
    change g.toKraus.map
        (f.toKraus.map ((dephase X.classical).map ρ)) =
      g.toKraus.map (f.toKraus.map ρ)
    have h := congrArg (fun channel ↦ channel.map ρ) f.source_dephase
    exact congrArg g.toKraus.map h
  target_dephase := by
    apply KrausChannel.ext
    funext ρ
    change (dephase Z.classical).map
        (g.toKraus.map (f.toKraus.map ρ)) =
      g.toKraus.map (f.toKraus.map ρ)
    exact congrArg (fun channel ↦ channel.map (f.toKraus.map ρ))
      g.target_dephase

/-- Classical quantum objects and dephasing-compatible Kraus channels form a
category. -/
noncomputable instance : Category Object where
  Hom := Channel
  id := Channel.identity
  comp := Channel.comp
  id_comp := by
    intro X Y f
    apply Channel.ext
    exact f.source_dephase
  comp_id := by
    intro X Y f
    apply Channel.ext
    exact f.target_dephase
  assoc := by
    intro W X Y Z f g h
    apply Channel.ext
    apply KrausChannel.ext
    rfl

/-- Regard a finite stochastic object as a classical quantum object. -/
abbrev ofClassical (X : FiniteStochastic.Object.{u}) : Object.{u} :=
  ⟨X⟩

/-- Regard a finite stochastic channel as a dephasing-compatible
measurement--preparation channel. -/
noncomputable def ofChannel {X Y : FiniteStochastic.Object.{u}}
    (f : FinStoch X Y) : Channel (ofClassical X) (ofClassical Y) where
  toKraus := measurementPreparation f
  source_dephase := by
    rw [dephase, ← measurementPreparation_comp]
    congr 1
    apply FinStoch.ext
    intro x y
    simp [FinStoch.comp, FinStoch.identity]
  target_dephase := by
    rw [dephase, ← measurementPreparation_comp]
    congr 1
    apply FinStoch.ext
    intro x y
    simp [FinStoch.comp, FinStoch.identity]

/-- Faithful categorical embedding of exact finite stochastic channels into
the dephasing-idempotent classical subcategory of finite Kraus channels. -/
noncomputable def embedding :
    FiniteStochastic.Object.{u} ⥤ Object.{u} where
  obj := ofClassical
  map := ofChannel
  map_id X := by
    apply Channel.ext
    rfl
  map_comp f g := by
    apply Channel.ext
    exact measurementPreparation_comp f g

/-- The classical measurement--preparation embedding is faithful. -/
instance embedding_faithful : embedding.Faithful where
  map_injective h :=
    measurementPreparation_faithful (congrArg Channel.toKraus h)

/-- Parallel composition of classical quantum objects uses the product
basis. -/
abbrev Object.tensor (X Y : Object.{u}) : Object.{u} :=
  ⟨FiniteStochastic.Object.tensor X.classical Y.classical⟩

/-- Parallel composition of dephasing-compatible channels. -/
noncomputable def Channel.tensor {W X Y Z : Object.{u}}
    (f : Channel W X) (g : Channel Y Z) :
    Channel (Object.tensor W Y) (Object.tensor X Z) where
  toKraus := KrausChannel.tensor f.toKraus g.toKraus
  source_dephase := by
    rw [dephase_tensor, ← KrausChannel.tensor_comp,
      f.source_dephase, g.source_dephase]
  target_dephase := by
    rw [dephase_tensor, ← KrausChannel.tensor_comp,
      f.target_dephase, g.target_dephase]

/-- Tensoring two categorical identities gives the identity on the product
classical quantum object. -/
theorem Channel.tensor_identity (X Y : Object.{u}) :
    Channel.tensor (Channel.identity X) (Channel.identity Y) =
      Channel.identity (Object.tensor X Y) := by
  apply Channel.ext
  exact (dephase_tensor X.classical Y.classical).symm

/-- Parallel composition satisfies interchange with serial composition in the
classical quantum category. -/
theorem Channel.tensor_comp
    {A B C D E F : Object.{u}}
    (f : Channel A B) (f' : Channel B C)
    (g : Channel D E) (g' : Channel E F) :
    Channel.tensor (Channel.comp f f') (Channel.comp g g') =
      Channel.comp (Channel.tensor f g) (Channel.tensor f' g') := by
  apply Channel.ext
  exact KrausChannel.tensor_comp f.toKraus f'.toKraus g.toKraus g'.toKraus

/-- Independent parallel composition is a bifunctor on the classical quantum
category. -/
noncomputable def tensorFunctor : Object.{u} × Object.{u} ⥤ Object.{u} where
  obj pair := Object.tensor pair.1 pair.2
  map pair := Channel.tensor pair.1 pair.2
  map_id pair := Channel.tensor_identity pair.1 pair.2
  map_comp f g := Channel.tensor_comp f.1 g.1 f.2 g.2

/-- The classical embedding preserves tensor products of objects
definitionally. -/
theorem embedding_obj_tensor (X Y : FiniteStochastic.Object.{u}) :
    embedding.obj (FiniteStochastic.Object.tensor X Y) =
      Object.tensor (embedding.obj X) (embedding.obj Y) := rfl

/-- The classical embedding preserves tensor products of stochastic
channels. -/
theorem embedding_map_tensor
    {W X Y Z : FiniteStochastic.Object.{u}}
    (f : FinStoch W X) (g : FinStoch Y Z) :
    embedding.map (FinStoch.tensor f g) =
      Channel.tensor (embedding.map f) (embedding.map g) := by
  apply Channel.ext
  exact measurementPreparation_tensor f g

end ClassicalQuantum

end Ript.Models.Quantum.ClassicalEmbedding
