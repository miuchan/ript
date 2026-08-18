import Mathlib.Algebra.Order.Hom.Monoid
import Ript.Core.Monotone

/-!
# Functors that change resource algebras

Models of one process theory need not report costs in the same resource
algebra.  A `ResourceChangeFunctor C D R S φ` maps processes from `C` to `D`
and compares their `S`-valued target cost with the image, under the ordered
additive homomorphism `φ : R →+o S`, of their `R`-valued source cost.

This is the one-dimensional change-of-resources operation needed to compare
heterogeneous probabilistic, computational, causal, quantum, semantic, and
thermodynamic models without first collapsing all costs into one fixed type.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

/-- A functor whose target cost is bounded by an ordered additive translation
of its source cost. -/
structure ResourceChangeFunctor
    (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D]
    (R : Type w₁) [AddCommMonoid R] [Preorder R]
    (S : Type w₂) [AddCommMonoid S] [Preorder S]
    [HasProcessCost C R] [HasProcessCost D S]
    (φ : R →+o S) where
  /-- The underlying map of process categories. -/
  toFunctor : C ⥤ D
  /-- Target cost is bounded by translated source cost. -/
  map_cost_le : ∀ {X Y : C} (f : X ⟶ Y),
    processCost (R := S) (toFunctor.map f) ≤ φ (processCost (R := R) f)

namespace ResourceChangeFunctor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {R : Type w₁} [AddCommMonoid R] [Preorder R]
variable {S : Type w₂} [AddCommMonoid S] [Preorder S]
variable {T : Type w₃} [AddCommMonoid T] [Preorder T]
variable [HasProcessCost C R] [HasProcessCost D S] [HasProcessCost E T]

/-- Resource-changing functors are determined by their underlying functors;
cost-law witnesses are proof-irrelevant. -/
@[ext]
theorem ext {φ : R →+o S} {F G : ResourceChangeFunctor C D R S φ}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Identity changes resources along the identity ordered additive map. -/
def id : ResourceChangeFunctor C C R R (OrderAddMonoidHom.id R) where
  toFunctor := 𝟭 C
  map_cost_le _ := le_rfl

/-- Resource-changing functors compose while their resource translations
compose in the same order. -/
def comp {φ : R →+o S} {ψ : S →+o T}
    (F : ResourceChangeFunctor C D R S φ)
    (G : ResourceChangeFunctor D E S T ψ) :
    ResourceChangeFunctor C E R T (ψ.comp φ) where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  map_cost_le f := by
    calc
      processCost (R := T) (G.toFunctor.map (F.toFunctor.map f)) ≤
          ψ (processCost (R := S) (F.toFunctor.map f)) :=
        G.map_cost_le (F.toFunctor.map f)
      _ ≤ ψ (φ (processCost (R := R) f)) :=
        OrderHomClass.monotone ψ (F.map_cost_le f)
      _ = (ψ.comp φ) (processCost (R := R) f) := rfl

/-- A same-resource monotone functor is the identity-resource special case. -/
def ofResourceMonotoneFunctor [HasProcessCost D R]
    (F : ResourceMonotoneFunctor C D R) :
    ResourceChangeFunctor C D R R (OrderAddMonoidHom.id R) where
  toFunctor := F.toFunctor
  map_cost_le := F.map_cost_le

/-- Recover the original same-resource interface from the identity-resource
special case. -/
def toResourceMonotoneFunctor
    [HasProcessCost D R]
    (F : ResourceChangeFunctor C D R R (OrderAddMonoidHom.id R)) :
    ResourceMonotoneFunctor C D R where
  toFunctor := F.toFunctor
  map_cost_le := F.map_cost_le

@[simp]
theorem id_obj (X : C) :
    (id (C := C) (R := R)).toFunctor.obj X = X :=
  rfl

@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) :
    (id (C := C) (R := R)).toFunctor.map f = f :=
  rfl

@[simp]
theorem comp_obj {φ : R →+o S} {ψ : S →+o T}
    (F : ResourceChangeFunctor C D R S φ)
    (G : ResourceChangeFunctor D E S T ψ) (X : C) :
    (F.comp G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) :=
  rfl

@[simp]
theorem comp_map {φ : R →+o S} {ψ : S →+o T}
    (F : ResourceChangeFunctor C D R S φ)
    (G : ResourceChangeFunctor D E S T ψ) {X Y : C} (f : X ⟶ Y) :
    (F.comp G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) :=
  rfl

@[simp]
theorem toResourceMonotoneFunctor_toFunctor
    [HasProcessCost D R]
    (F : ResourceChangeFunctor C D R R (OrderAddMonoidHom.id R)) :
    F.toResourceMonotoneFunctor.toFunctor = F.toFunctor :=
  rfl

@[simp]
theorem ofResourceMonotoneFunctor_toFunctor
    [HasProcessCost D R]
    (F : ResourceMonotoneFunctor C D R) :
    (ofResourceMonotoneFunctor F).toFunctor = F.toFunctor :=
  rfl

@[simp]
theorem toResourceMonotoneFunctor_ofResourceMonotoneFunctor
    [HasProcessCost D R] (F : ResourceMonotoneFunctor C D R) :
    (ofResourceMonotoneFunctor F).toResourceMonotoneFunctor = F := by
  apply ResourceMonotoneFunctor.ext
  rfl

@[simp]
theorem ofResourceMonotoneFunctor_toResourceMonotoneFunctor
    [HasProcessCost D R]
    (F : ResourceChangeFunctor C D R R (OrderAddMonoidHom.id R)) :
    ofResourceMonotoneFunctor F.toResourceMonotoneFunctor = F := by
  apply ResourceChangeFunctor.ext
  rfl

end ResourceChangeFunctor

end Ript.Core
