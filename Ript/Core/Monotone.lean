import Mathlib.CategoryTheory.Functor.Basic
import Ript.Core.CostedProcess

/-!
# Resource-nonincreasing functors

`ResourceMonotoneFunctor` bundles an ordinary functor with the assertion that
mapping a process never increases its cost. Monoidal, copying, causal, and other
capabilities remain separate structures.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ w

/-- A functor between costed categories that never increases process cost. -/
structure ResourceMonotoneFunctor (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] (R : Type w) [AddCommMonoid R] [Preorder R]
    [HasProcessCost C R] [HasProcessCost D R] where
  /-- The underlying functor between process categories. -/
  toFunctor : C ⥤ D
  /-- Mapping a process does not increase its resource cost. -/
  map_cost_le : ∀ {X Y : C} (f : X ⟶ Y),
    processCost (R := R) (toFunctor.map f) ≤ processCost (R := R) f

namespace ResourceMonotoneFunctor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable [HasProcessCost C R] [HasProcessCost D R] [HasProcessCost E R]

/-- Resource-nonincreasing functors are equal when their underlying functors
are equal; the cost witnesses are propositions and hence proof-irrelevant. -/
@[ext]
theorem ext {F G : ResourceMonotoneFunctor C D R}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- The identity functor is resource-nonincreasing. -/
def id : ResourceMonotoneFunctor C C R where
  toFunctor := 𝟭 C
  map_cost_le _ := le_rfl

/-- Resource-nonincreasing functors are closed under composition. -/
def comp (F : ResourceMonotoneFunctor C D R)
    (G : ResourceMonotoneFunctor D E R) : ResourceMonotoneFunctor C E R where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  map_cost_le f := (G.map_cost_le (F.toFunctor.map f)).trans (F.map_cost_le f)

@[simp]
theorem id_obj (X : C) : (id (C := C) (R := R)).toFunctor.obj X = X :=
  rfl

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) :
    (id (C := C) (R := R)).toFunctor.map f = f :=
  rfl

@[simp]
theorem comp_obj (F : ResourceMonotoneFunctor C D R)
    (G : ResourceMonotoneFunctor D E R) (X : C) :
    (F.comp G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) :=
  rfl

@[simp]
theorem comp_map (F : ResourceMonotoneFunctor C D R)
    (G : ResourceMonotoneFunctor D E R) {X Y : C} (f : X ⟶ Y) :
    (F.comp G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) :=
  rfl

end ResourceMonotoneFunctor

end Ript.Core
