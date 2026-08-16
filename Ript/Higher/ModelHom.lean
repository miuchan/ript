import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Ript.Core.StructuralCost

/-!
# Resource-indexed process models and strong model morphisms

This file bundles the zero- and one-dimensional data used by Ript's model
bicategory.  A `ProcessModel R` is a symmetric monoidal category whose serial,
parallel, and structural costs all take values in the same ordered additive
commutative monoid `R`.

A `ModelHom M N` is a resource-nonincreasing strong braided monoidal functor.
Its strongness is represented without choosing redundant inverse tensorators:
the lax unit and tensor comparison maps are required to be isomorphisms.  This
is the standard property-based presentation of a strong monoidal functor and
is stable under identity and composition.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open Ript.Core

universe u v w

/-- A resource-indexed process model with serial and parallel cost accounting
and free symmetric-monoidal structural rewiring.  The universes are uniform so
that these models can be assembled into one bicategory. -/
structure ProcessModel (R : Type w) [AddCommMonoid R] [PartialOrder R] where
  /-- Processes are morphisms between objects of `Carrier`. -/
  Carrier : Type u
  /-- The sequential process category. -/
  category : Category.{v} Carrier
  /-- Parallel composition of processes. -/
  monoidal : letI := category; MonoidalCategory Carrier
  /-- Exchange of parallel factors. -/
  symmetric : letI := category; letI := monoidal; SymmetricCategory Carrier
  /-- Serial process costs valued in `R`. -/
  costed : letI := category; HasProcessCost Carrier R
  /-- Parallel composition is subadditive. -/
  parallelCost : letI := category; letI := monoidal; letI := costed
    HasParallelProcessCost Carrier R
  /-- Associators, unitors, and symmetry are free rewiring. -/
  structuralCost : letI := category; letI := monoidal; letI := symmetric
    letI := costed; HasFreeStructuralCost Carrier R

namespace ProcessModel

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- A bundled process model coerces to its object type. -/
instance : CoeSort (ProcessModel.{u, v, w} R) (Type u) :=
  ⟨ProcessModel.Carrier⟩

instance (M : ProcessModel.{u, v, w} R) : Category.{v} M := M.category
instance (M : ProcessModel.{u, v, w} R) : MonoidalCategory M := M.monoidal
instance (M : ProcessModel.{u, v, w} R) : SymmetricCategory M := M.symmetric
instance (M : ProcessModel.{u, v, w} R) : HasProcessCost M R := M.costed
instance (M : ProcessModel.{u, v, w} R) : HasParallelProcessCost M R := M.parallelCost
instance (M : ProcessModel.{u, v, w} R) : HasFreeStructuralCost M R := M.structuralCost

end ProcessModel

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- A resource-nonincreasing strong braided monoidal functor between process
models.  Strongness means that the lax unit and tensor comparison maps are
isomorphisms; the two `IsIso` fields are propositions. -/
structure ModelHom (M N : ProcessModel.{u, v, w} R) where
  /-- The underlying lax braided monoidal functor. -/
  toLaxBraided : LaxBraidedFunctor M N
  /-- The unit comparison map is invertible. -/
  unit_isIso : IsIso (Functor.LaxMonoidal.ε toLaxBraided.toFunctor) := by infer_instance
  /-- Every tensor comparison map is invertible. -/
  tensor_isIso : ∀ X Y : M,
    IsIso (Functor.LaxMonoidal.μ toLaxBraided.toFunctor X Y) := by infer_instance
  /-- Mapping a process never increases its cost. -/
  map_cost_le : ∀ {X Y : M} (f : X ⟶ Y),
    processCost (R := R) (toLaxBraided.toFunctor.map f) ≤ processCost (R := R) f

namespace ModelHom

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]
variable {M N P Q : ProcessModel.{u, v, w} R}

/-- The underlying ordinary functor. -/
abbrev toFunctor (F : ModelHom M N) : M ⥤ N := F.toLaxBraided.toFunctor

instance (F : ModelHom M N) :
    IsIso (Functor.LaxMonoidal.ε F.toFunctor) :=
  F.unit_isIso

instance (F : ModelHom M N) (X Y : M) :
    IsIso (Functor.LaxMonoidal.μ F.toFunctor X Y) :=
  F.tensor_isIso X Y

/-- Equality of the structured functor determines equality of model
morphisms; the remaining fields are propositions. -/
@[ext]
theorem ext {F G : ModelHom M N} (h : F.toLaxBraided = G.toLaxBraided) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- The identity strong model morphism. -/
def id (M : ProcessModel.{u, v, w} R) : ModelHom M M where
  toLaxBraided := LaxBraidedFunctor.of (𝟭 M)
  unit_isIso := by
    change IsIso (𝟙 _)
    infer_instance
  tensor_isIso := by
    intro X Y
    change IsIso (𝟙 _)
    infer_instance
  map_cost_le _ := le_rfl

/-- Composition of resource-nonincreasing strong model morphisms. -/
def comp (F : ModelHom M N) (G : ModelHom N P) : ModelHom M P where
  toLaxBraided := LaxBraidedFunctor.of (F.toFunctor ⋙ G.toFunctor)
  unit_isIso := by
    change IsIso
      (Functor.LaxMonoidal.ε G.toFunctor ≫
        G.toFunctor.map (Functor.LaxMonoidal.ε F.toFunctor))
    infer_instance
  tensor_isIso := by
    intro X Y
    change IsIso
      (Functor.LaxMonoidal.μ G.toFunctor _ _ ≫
        G.toFunctor.map (Functor.LaxMonoidal.μ F.toFunctor X Y))
    infer_instance
  map_cost_le f :=
    (G.map_cost_le (F.toFunctor.map f)).trans (F.map_cost_le f)

@[simp]
theorem id_toFunctor (M : ProcessModel.{u, v, w} R) :
    (id M).toFunctor = 𝟭 M := rfl

@[simp]
theorem comp_toFunctor (F : ModelHom M N) (G : ModelHom N P) :
    (comp F G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp]
theorem id_obj (X : M) : (id M).toFunctor.obj X = X := rfl

@[simp]
theorem id_map {X Y : M} (f : X ⟶ Y) : (id M).toFunctor.map f = f := rfl

@[simp]
theorem comp_obj (F : ModelHom M N) (G : ModelHom N P) (X : M) :
    (comp F G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := rfl

@[simp]
theorem comp_map (F : ModelHom M N) (G : ModelHom N P) {X Y : M} (f : X ⟶ Y) :
    (comp F G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) := rfl

/-- The strong monoidal structure can be recovered canonically from the
invertible lax comparison maps. -/
@[instance_reducible]
noncomputable def monoidal (F : ModelHom M N) : F.toFunctor.Monoidal :=
  Functor.Monoidal.ofLaxMonoidal F.toFunctor

end ModelHom

end Ript.Higher
