import Ript.Higher.ModelHom
import Ript.Resource.Reindexing

/-!
# Higher model morphisms across resource algebras

The fixed-resource bicategory is only one fibre of the intended theory.  This
file adds change of resource algebra at both object and one-cell level:

* a process model can be reindexed along `φ : R →+o S`;
* a strong braided monoidal model morphism can compare an `R`-model with an
  `S`-model when target costs are bounded by translated source costs;
* these heterogeneous morphisms have identity and associative composition at
  the level of their resource maps and underlying functors.

This is the first formal layer of the total higher category of models over
varying resource algebras.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open Ript.Core
open Ript.Resource

universe u v w₁ w₂ w₃

namespace ProcessModel

variable {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
variable {S : Type w₂} [AddCommMonoid S] [PartialOrder S]

/-- Reindex every cost law of a process model along an ordered additive
resource homomorphism.  The process category and its symmetric monoidal
structure are unchanged. -/
def reindex (φ : R →+o S) (M : ProcessModel.{u, v, w₁} R) :
    ProcessModel.{u, v, w₂} S := by
  letI : Category.{v} M.Carrier := M.category
  letI : MonoidalCategory M.Carrier := M.monoidal
  letI : SymmetricCategory M.Carrier := M.symmetric
  letI : HasProcessCost M.Carrier R := M.costed
  let targetCost : HasProcessCost M.Carrier S :=
    reindexProcessCost (C := M.Carrier) (R := R) (S := S) φ
  let targetParallel : @HasParallelProcessCost M.Carrier _ _ S _ _ targetCost :=
    reindexParallelProcessCost (C := M.Carrier) (R := R) (S := S) φ
  let targetStructural : @HasFreeStructuralCost M.Carrier _ _ _ S _ _ targetCost :=
    reindexFreeStructuralCost (C := M.Carrier) (R := R) (S := S) φ
  exact
    { Carrier := M.Carrier
      category := M.category
      monoidal := M.monoidal
      symmetric := M.symmetric
      costed := targetCost
      parallelCost := targetParallel
      structuralCost := targetStructural }

@[simp]
theorem reindex_carrier (φ : R →+o S) (M : ProcessModel.{u, v, w₁} R) :
    (M.reindex φ).Carrier = M.Carrier :=
  rfl

@[simp]
theorem reindex_cost (φ : R →+o S) (M : ProcessModel.{u, v, w₁} R)
    {X Y : M.Carrier} (f : X ⟶ Y) :
    (M.reindex φ).costed.cost f = φ (M.costed.cost f) :=
  rfl

end ProcessModel

/-- A strong braided monoidal morphism between models with possibly different
resource algebras.  The ordered additive map `φ` states how source budgets are
interpreted in the target model. -/
structure ResourceChangeModelHom
    {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
    {S : Type w₂} [AddCommMonoid S] [PartialOrder S]
    (φ : R →+o S)
    (M : ProcessModel.{u, v, w₁} R) (N : ProcessModel.{u, v, w₂} S) where
  /-- The underlying lax braided monoidal functor. -/
  toLaxBraided : LaxBraidedFunctor M N
  /-- The unit comparison is invertible. -/
  unit_isIso : IsIso (Functor.LaxMonoidal.ε toLaxBraided.toFunctor) := by
    infer_instance
  /-- Every tensor comparison is invertible. -/
  tensor_isIso : ∀ X Y : M,
    IsIso (Functor.LaxMonoidal.μ toLaxBraided.toFunctor X Y) := by
    infer_instance
  /-- Target cost is bounded by translated source cost. -/
  map_cost_le : ∀ {X Y : M} (f : X ⟶ Y),
    processCost (R := S) (toLaxBraided.toFunctor.map f) ≤
      φ (processCost (R := R) f)

namespace ResourceChangeModelHom

variable {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
variable {S : Type w₂} [AddCommMonoid S] [PartialOrder S]
variable {T : Type w₃} [AddCommMonoid T] [PartialOrder T]
variable {M : ProcessModel.{u, v, w₁} R}
variable {N : ProcessModel.{u, v, w₂} S}
variable {P : ProcessModel.{u, v, w₃} T}

/-- The underlying ordinary functor. -/
abbrev toFunctor {φ : R →+o S} (F : ResourceChangeModelHom φ M N) : M ⥤ N :=
  F.toLaxBraided.toFunctor

instance {φ : R →+o S} (F : ResourceChangeModelHom φ M N) :
    IsIso (Functor.LaxMonoidal.ε F.toFunctor) :=
  F.unit_isIso

instance {φ : R →+o S} (F : ResourceChangeModelHom φ M N) (X Y : M) :
    IsIso (Functor.LaxMonoidal.μ F.toFunctor X Y) :=
  F.tensor_isIso X Y

/-- Equality of structured functors determines equality; all remaining fields
are propositions. -/
@[ext]
theorem ext {φ : R →+o S} {F G : ResourceChangeModelHom φ M N}
    (h : F.toLaxBraided = G.toLaxBraided) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Identity heterogeneous model morphism over the identity resource map. -/
def id (M : ProcessModel.{u, v, w₁} R) :
    ResourceChangeModelHom (OrderAddMonoidHom.id R) M M where
  toLaxBraided := LaxBraidedFunctor.of (𝟭 M)
  unit_isIso := by
    change IsIso (𝟙 _)
    infer_instance
  tensor_isIso := by
    intro X Y
    change IsIso (𝟙 _)
    infer_instance
  map_cost_le _ := le_rfl

/-- Composition combines the strong model maps and composes their resource
translations. -/
def comp {φ : R →+o S} {ψ : S →+o T}
    (F : ResourceChangeModelHom φ M N)
    (G : ResourceChangeModelHom ψ N P) :
    ResourceChangeModelHom (ψ.comp φ) M P where
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
  map_cost_le f := by
    calc
      processCost (R := T) (G.toFunctor.map (F.toFunctor.map f)) ≤
          ψ (processCost (R := S) (F.toFunctor.map f)) :=
        G.map_cost_le (F.toFunctor.map f)
      _ ≤ ψ (φ (processCost (R := R) f)) :=
        OrderHomClass.monotone ψ (F.map_cost_le f)
      _ = (ψ.comp φ) (processCost (R := R) f) := rfl

/-- An ordinary same-resource model hom is the identity-resource case. -/
def ofModelHom {M' N' : ProcessModel.{u, v, w₁} R} (F : ModelHom M' N') :
    ResourceChangeModelHom (OrderAddMonoidHom.id R) M' N' where
  toLaxBraided := F.toLaxBraided
  unit_isIso := F.unit_isIso
  tensor_isIso := F.tensor_isIso
  map_cost_le := F.map_cost_le

/-- Recover the fixed-resource model-hom interface from the identity-resource
special case. -/
def toModelHom {M' N' : ProcessModel.{u, v, w₁} R}
    (F : ResourceChangeModelHom (OrderAddMonoidHom.id R) M' N') :
    ModelHom M' N' where
  toLaxBraided := F.toLaxBraided
  unit_isIso := F.unit_isIso
  tensor_isIso := F.tensor_isIso
  map_cost_le := F.map_cost_le

@[simp]
theorem toModelHom_toLaxBraided
    {M' N' : ProcessModel.{u, v, w₁} R}
    (F : ResourceChangeModelHom (OrderAddMonoidHom.id R) M' N') :
    F.toModelHom.toLaxBraided = F.toLaxBraided :=
  rfl

@[simp]
theorem ofModelHom_toLaxBraided
    {M' N' : ProcessModel.{u, v, w₁} R} (F : ModelHom M' N') :
    (ofModelHom F).toLaxBraided = F.toLaxBraided :=
  rfl

@[simp]
theorem toModelHom_ofModelHom
    {M' N' : ProcessModel.{u, v, w₁} R} (F : ModelHom M' N') :
    (ofModelHom F).toModelHom = F := by
  apply ModelHom.ext
  rfl

@[simp]
theorem ofModelHom_toModelHom
    {M' N' : ProcessModel.{u, v, w₁} R}
    (F : ResourceChangeModelHom (OrderAddMonoidHom.id R) M' N') :
    ofModelHom F.toModelHom = F := by
  apply ResourceChangeModelHom.ext
  rfl

@[simp]
theorem id_toFunctor (M : ProcessModel.{u, v, w₁} R) :
    (id M).toFunctor = 𝟭 M :=
  rfl

@[simp]
theorem comp_toFunctor {φ : R →+o S} {ψ : S →+o T}
    (F : ResourceChangeModelHom φ M N)
    (G : ResourceChangeModelHom ψ N P) :
    (F.comp G).toFunctor = F.toFunctor ⋙ G.toFunctor :=
  rfl

@[simp]
theorem comp_map {φ : R →+o S} {ψ : S →+o T}
    (F : ResourceChangeModelHom φ M N)
    (G : ResourceChangeModelHom ψ N P) {X Y : M} (f : X ⟶ Y) :
    (F.comp G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) :=
  rfl

/-- A heterogeneous strong model morphism transports every checked source
budget to its image under the resource translation. -/
theorem map_withinBudget {φ : R →+o S}
    (F : ResourceChangeModelHom φ M N)
    {X Y : M} {r : R} {f : X ⟶ Y}
    (hf : WithinBudget (R := R) r f) :
    WithinBudget (R := S) (φ r) (F.toFunctor.map f) :=
  (F.map_cost_le f).trans (OrderHomClass.monotone φ hf)

/-- Transport a packaged process and its machine-checked budget through a
heterogeneous strong model morphism. -/
def mapBudgetedHom {φ : R →+o S}
    (F : ResourceChangeModelHom φ M N)
    {X Y : M} {r : R} (f : BudgetedHom (R := R) r X Y) :
    BudgetedHom (R := S) (φ r) (F.toFunctor.obj X) (F.toFunctor.obj Y) :=
  ⟨F.toFunctor.map f.hom, F.map_withinBudget f.within⟩

@[simp]
theorem mapBudgetedHom_hom {φ : R →+o S}
    (F : ResourceChangeModelHom φ M N)
    {X Y : M} {r : R} (f : BudgetedHom (R := R) r X Y) :
    (F.mapBudgetedHom f).hom = F.toFunctor.map f.hom :=
  rfl

end ResourceChangeModelHom

/-- A monoidal 2-cell between parallel model morphisms over the same resource
translation.  Fixing `φ` is necessary: a 2-cell compares two realizations of
one and the same interpretation of resource values. -/
structure ResourceChangeModelTransformation
    {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
    {S : Type w₂} [AddCommMonoid S] [PartialOrder S]
    {φ : R →+o S}
    {M : ProcessModel.{u, v, w₁} R} {N : ProcessModel.{u, v, w₂} S}
    (F G : ResourceChangeModelHom φ M N) where
  /-- The underlying natural transformation. -/
  toNatTrans : F.toFunctor ⟶ G.toFunctor
  /-- Compatibility with lax unit and tensor comparison maps. -/
  isMonoidal : NatTrans.IsMonoidal toNatTrans := by infer_instance

namespace ResourceChangeModelTransformation

attribute [instance] isMonoidal

variable {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
variable {S : Type w₂} [AddCommMonoid S] [PartialOrder S]
variable {φ : R →+o S}
variable {M : ProcessModel.{u, v, w₁} R} {N : ProcessModel.{u, v, w₂} S}
variable {F G H : ResourceChangeModelHom φ M N}

/-- Bundle a monoidal natural transformation as a heterogeneous model
2-cell. -/
def ofNatTrans (eta : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal eta] :
    ResourceChangeModelTransformation F G :=
  ⟨eta, inferInstance⟩

/-- Heterogeneous model 2-cells are determined by their underlying natural
transformations. -/
@[ext]
theorem ext {eta theta : ResourceChangeModelTransformation F G}
    (h : eta.toNatTrans = theta.toNatTrans) : eta = theta := by
  cases eta
  cases theta
  cases h
  rfl

/-- Vertical identities and composition make every fixed-resource-map
hom-type a category. -/
instance homCategory (φ : R →+o S)
    (M : ProcessModel.{u, v, w₁} R) (N : ProcessModel.{u, v, w₂} S) :
    Category (ResourceChangeModelHom φ M N) where
  Hom := ResourceChangeModelTransformation
  id F := ofNatTrans (𝟙 F.toFunctor)
  comp eta theta := ofNatTrans (eta.toNatTrans ≫ theta.toNatTrans)
  id_comp eta := by
    apply ext
    exact Category.id_comp eta.toNatTrans
  comp_id eta := by
    apply ext
    exact Category.comp_id eta.toNatTrans
  assoc eta theta kappa := by
    apply ext
    exact Category.assoc eta.toNatTrans theta.toNatTrans kappa.toNatTrans

@[simp]
theorem id_toNatTrans (F : ResourceChangeModelHom φ M N) :
    (𝟙 F : F ⟶ F).toNatTrans = 𝟙 F.toFunctor :=
  rfl

@[simp]
theorem comp_toNatTrans {F G H : ResourceChangeModelHom φ M N}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    (eta ≫ theta).toNatTrans = eta.toNatTrans ≫ theta.toNatTrans :=
  rfl

end ResourceChangeModelTransformation

end Ript.Higher
