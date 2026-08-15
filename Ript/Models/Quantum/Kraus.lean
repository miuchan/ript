import Mathlib.CategoryTheory.Category.Basic
import Ript.Models.Quantum.Basic

/-!
# Finite Kraus channels

A `KrausChannel X Y` stores its operational action on matrices together with a
propositionally truncated finite Kraus representation.  This design makes
channel equality extensional in the action rather than intensional in a
non-unique Kraus family.  The completeness equation

`∑ i, Kᵢᴴ Kᵢ = I`

is used to prove trace preservation, while positivity follows from closure of
positive-semidefinite matrices under `K ρ Kᴴ` and finite sums.  Consequently
every channel maps density matrices to density matrices.  Identity and serial
composition receive explicit Kraus certificates and form a category.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

universe u

/-- A finite Kraus certificate for an operational matrix map. -/
structure KrausRepresentation (X Y : Object.{u})
    (map : Matrix X X ℂ → Matrix Y Y ℂ) where
  /-- Finite labels for the Kraus operators. -/
  index : Type u
  /-- Executable enumeration of Kraus labels. -/
  fintype : Fintype index
  /-- Kraus operators from the source basis to the target basis. -/
  operators : index → Matrix Y X ℂ
  /-- The operational map is exactly the Kraus sum. -/
  map_eq : ∀ ρ, map ρ = ∑ i, operators i * ρ * (operators i)ᴴ
  /-- Trace-preserving completeness equation. -/
  completeness : ∑ i, (operators i)ᴴ * operators i = 1

namespace KrausRepresentation

attribute [instance] KrausRepresentation.fintype

variable {X Y : Object.{u}} {map : Matrix X X ℂ → Matrix Y Y ℂ}

/-- A Kraus map preserves positive semidefiniteness. -/
theorem map_posSemidef (rep : KrausRepresentation X Y map)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) : (map ρ).PosSemidef := by
  rw [rep.map_eq]
  apply Matrix.posSemidef_sum Finset.univ
  intro i _
  exact hρ.mul_mul_conjTranspose_same (rep.operators i)

/-- The Kraus completeness equation implies trace preservation. -/
theorem map_trace (rep : KrausRepresentation X Y map)
    (ρ : Matrix X X ℂ) : (map ρ).trace = ρ.trace := by
  rw [rep.map_eq, Matrix.trace_sum]
  calc
    ∑ i ∈ Finset.univ, (rep.operators i * ρ * (rep.operators i)ᴴ).trace =
        ∑ i, (((rep.operators i)ᴴ * rep.operators i) * ρ).trace := by
          apply Fintype.sum_congr
          intro i
          rw [Matrix.trace_mul_cycle]
    _ = (∑ i, ((rep.operators i)ᴴ * rep.operators i) * ρ).trace := by
      exact (Matrix.trace_sum Finset.univ
        (fun i ↦ ((rep.operators i)ᴴ * rep.operators i) * ρ)).symm
    _ = ((∑ i, (rep.operators i)ᴴ * rep.operators i) * ρ).trace := by
      congr 1
      rw [Matrix.sum_mul]
    _ = ρ.trace := by rw [rep.completeness, one_mul]

/-- A Kraus representation acts additively on matrices. -/
theorem map_add (rep : KrausRepresentation X Y map)
    (ρ σ : Matrix X X ℂ) : map (ρ + σ) = map ρ + map σ := by
  rw [rep.map_eq, rep.map_eq, rep.map_eq]
  simp_rw [Matrix.mul_add, Matrix.add_mul]
  exact Finset.sum_add_distrib

/-- A Kraus representation sends the zero matrix to zero. -/
theorem map_zero (rep : KrausRepresentation X Y map) : map 0 = 0 := by
  rw [rep.map_eq]
  simp

/-- A Kraus representation commutes with complex scalar multiplication. -/
theorem map_smul (rep : KrausRepresentation X Y map) (c : ℂ)
    (ρ : Matrix X X ℂ) : map (c • ρ) = c • map ρ := by
  rw [rep.map_eq, rep.map_eq]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Finset.smul_sum]

end KrausRepresentation

/-- A matrix transformation equipped with the mere existence of a finite
trace-preserving Kraus representation.  The certificate is propositionally
truncated so different Kraus families for the same action define the same
channel. -/
structure KrausChannel (X Y : Object.{u}) where
  /-- Operational action on arbitrary source matrices. -/
  map : Matrix X X ℂ → Matrix Y Y ℂ
  /-- A finite Kraus certificate for the operational action. -/
  has_representation : Nonempty (KrausRepresentation X Y map)

namespace KrausChannel

variable {W X Y Z : Object.{u}}

/-- Build a channel from an explicit finite Kraus family satisfying the
completeness equation. -/
def ofOperators {I : Type u} [Fintype I]
    (operators : I → Matrix Y X ℂ)
    (completeness : ∑ i, (operators i)ᴴ * operators i = 1) :
    KrausChannel X Y where
  map ρ := ∑ i, operators i * ρ * (operators i)ᴴ
  has_representation := ⟨
    { index := I
      fintype := inferInstance
      operators := operators
      map_eq := fun _ ↦ rfl
      completeness := completeness }⟩

/-- Kraus channels are equal when their operational matrix maps are equal. -/
@[ext]
theorem ext (f g : KrausChannel X Y) (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Every Kraus channel preserves positive semidefiniteness. -/
theorem map_posSemidef (channel : KrausChannel X Y)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) :
    (channel.map ρ).PosSemidef :=
  channel.has_representation.elim fun rep ↦ rep.map_posSemidef hρ

/-- Every Kraus channel preserves the matrix trace. -/
theorem map_trace (channel : KrausChannel X Y) (ρ : Matrix X X ℂ) :
    (channel.map ρ).trace = ρ.trace :=
  channel.has_representation.elim fun rep ↦ rep.map_trace ρ

/-- Every Kraus channel acts additively on matrices. -/
theorem map_add (channel : KrausChannel X Y) (ρ σ : Matrix X X ℂ) :
    channel.map (ρ + σ) = channel.map ρ + channel.map σ :=
  channel.has_representation.elim fun rep ↦ rep.map_add ρ σ

/-- Every Kraus channel sends the zero matrix to zero. -/
theorem map_zero (channel : KrausChannel X Y) : channel.map 0 = 0 :=
  channel.has_representation.elim fun rep ↦ rep.map_zero

/-- Every Kraus channel commutes with complex scalar multiplication. -/
theorem map_smul (channel : KrausChannel X Y) (c : ℂ) (ρ : Matrix X X ℂ) :
    channel.map (c • ρ) = c • channel.map ρ :=
  channel.has_representation.elim fun rep ↦ rep.map_smul c ρ

/-- The canonical complex-linear map underlying a Kraus channel. -/
def toLinearMap (channel : KrausChannel X Y) :
    Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ where
  toFun := channel.map
  map_add' := channel.map_add
  map_smul' := channel.map_smul

/-- Coercing the canonical linear map recovers the operational channel map. -/
@[simp]
theorem toLinearMap_apply (channel : KrausChannel X Y) (ρ : Matrix X X ℂ) :
    channel.toLinearMap ρ = channel.map ρ := rfl

/-- The one-operator Kraus family `{I}` is the identity channel. -/
def identity (X : Object.{u}) : KrausChannel X X :=
  ofOperators (I := PUnit) (fun _ ↦ 1) (by simp)

/-- Serial composition of Kraus channels uses all pairwise products `Lⱼ Kᵢ`
as a Kraus family. -/
def comp (f : KrausChannel X Y) (g : KrausChannel Y Z) :
    KrausChannel X Z where
  map ρ := g.map (f.map ρ)
  has_representation := f.has_representation.elim fun frep ↦
    g.has_representation.elim fun grep ↦ ⟨
      { index := grep.index × frep.index
        fintype := inferInstance
        operators := fun pair ↦ grep.operators pair.1 * frep.operators pair.2
        map_eq := fun ρ ↦ by
          rw [grep.map_eq, frep.map_eq, Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro j
          rw [Matrix.mul_sum, Matrix.sum_mul]
          apply Fintype.sum_congr
          intro i
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        completeness := by
          rw [Fintype.sum_prod_type]
          calc
            ∑ j, ∑ i,
                (grep.operators j * frep.operators i)ᴴ *
                  (grep.operators j * frep.operators i) =
                ∑ i, ∑ j,
                  (grep.operators j * frep.operators i)ᴴ *
                    (grep.operators j * frep.operators i) := Finset.sum_comm
            _ = ∑ i, (frep.operators i)ᴴ *
                  (∑ j, (grep.operators j)ᴴ * grep.operators j) *
                    frep.operators i := by
              apply Fintype.sum_congr
              intro i
              rw [Matrix.mul_sum, Matrix.sum_mul]
              apply Fintype.sum_congr
              intro j
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
            _ = ∑ i, (frep.operators i)ᴴ * frep.operators i := by
              rw [grep.completeness]
              simp
            _ = 1 := frep.completeness }⟩

/-- Finite quantum objects and trace-preserving Kraus channels form a
category. -/
instance category : CategoryTheory.Category.{u} Object.{u} where
  Hom := KrausChannel
  id := identity
  comp := comp
  id_comp := by
    intro X Y f
    apply ext
    funext ρ
    simp [comp, identity, ofOperators]
  comp_id := by
    intro X Y f
    apply ext
    funext ρ
    simp [comp, identity, ofOperators]
  assoc := by
    intro V W X Y f g h
    apply ext
    funext ρ
    rfl

/-- Apply a Kraus channel to a density matrix.  The result is a density
matrix by positivity and trace preservation. -/
def applyDensity (channel : KrausChannel X Y) (ρ : DensityMatrix X) :
    DensityMatrix Y where
  matrix := channel.map ρ.matrix
  posSemidef := channel.map_posSemidef ρ.posSemidef
  trace_one := channel.map_trace ρ.matrix |>.trans ρ.trace_one

/-- The underlying matrix of channel application is its operational map. -/
@[simp]
theorem applyDensity_matrix (channel : KrausChannel X Y) (ρ : DensityMatrix X) :
    (channel.applyDensity ρ).matrix = channel.map ρ.matrix := rfl

/-- The identity Kraus channel acts identically on matrices. -/
@[simp]
theorem identity_map (X : Object.{u}) (ρ : Matrix X X ℂ) :
    (identity X).map ρ = ρ := by
  simp [identity, ofOperators]

/-- The canonical linear map of the identity channel is the identity linear
map. -/
@[simp]
theorem identity_toLinearMap (X : Object.{u}) :
    (identity X).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro ρ
  simp

/-- Serial channel application is operational function composition. -/
@[simp]
theorem comp_map (f : KrausChannel X Y) (g : KrausChannel Y Z)
    (ρ : Matrix X X ℂ) :
    (comp f g).map ρ = g.map (f.map ρ) := rfl

/-- Applying the identity channel leaves a density matrix unchanged. -/
@[simp]
theorem identity_applyDensity (ρ : DensityMatrix X) :
    (identity X).applyDensity ρ = ρ := by
  apply DensityMatrix.ext
  simp

/-- Applying a composite channel agrees with successive density-matrix
evolution. -/
@[simp]
theorem comp_applyDensity (f : KrausChannel X Y) (g : KrausChannel Y Z)
    (ρ : DensityMatrix X) :
    (comp f g).applyDensity ρ = g.applyDensity (f.applyDensity ρ) := by
  apply DensityMatrix.ext
  rfl

end KrausChannel

end Ript.Models.Quantum
