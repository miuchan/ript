import Mathlib.CategoryTheory.Bicategory.Basic
import Ript.Higher.ResourceChange

/-!
# The total bicategory of resource-valued process models

`ProcessModel R` and its bicategory organize one fixed resource algebra at a
time.  This file packages the resource algebra together with the model and
uses `ResourceChangeModelHom` as the one-cells between packages.  A one-cell
therefore carries both an ordered additive resource translation and a strong
braided model morphism whose cost comparison lies over that translation.

Two-cells record equality of the resource translations together with a
monoidal natural transformation.  The equality field makes horizontal
composition well typed while proof irrelevance keeps the local categories
extensional in their underlying natural transformations.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open Ript.Core

universe u v w

/-- A resource algebra bundled with one symmetric monoidal process model over
that algebra.  Uniform universes make these packages the objects of one Lean
bicategory. -/
structure ResourceModel where
  /-- The model's resource-value type. -/
  Resource : Type w
  /-- Additive composition of resource values. -/
  addCommMonoid : AddCommMonoid Resource
  /-- The resource comparison order. -/
  partialOrder : PartialOrder Resource
  /-- The process model valued in the bundled resource algebra. -/
  model : letI := addCommMonoid; letI := partialOrder
    ProcessModel.{u, v, w} Resource

namespace ResourceModel

instance (M : ResourceModel.{u, v, w}) : AddCommMonoid M.Resource :=
  M.addCommMonoid

instance (M : ResourceModel.{u, v, w}) : PartialOrder M.Resource :=
  M.partialOrder

/-- The underlying fixed-resource process model. -/
abbrev toProcessModel (M : ResourceModel.{u, v, w}) :
    ProcessModel.{u, v, w} M.Resource :=
  M.model

/-- A bundled resource model coerces to its process-object type. -/
instance : CoeSort ResourceModel.{u, v, w} (Type u) :=
  ⟨fun M ↦ M.model.Carrier⟩

instance (M : ResourceModel.{u, v, w}) : Category.{v} M :=
  M.model.category

instance (M : ResourceModel.{u, v, w}) : MonoidalCategory M :=
  M.model.monoidal

instance (M : ResourceModel.{u, v, w}) : SymmetricCategory M :=
  M.model.symmetric

instance (M : ResourceModel.{u, v, w}) : HasProcessCost M M.Resource :=
  M.model.costed

instance (M : ResourceModel.{u, v, w}) : HasParallelProcessCost M M.Resource :=
  M.model.parallelCost

instance (M : ResourceModel.{u, v, w}) : HasFreeStructuralCost M M.Resource :=
  M.model.structuralCost

end ResourceModel

/-- A one-cell in the total model bicategory: an ordered additive change of
resource algebra together with a strong braided model morphism over it. -/
structure ResourceModelHom (M N : ResourceModel.{u, v, w}) where
  /-- Translation from source resource values to target resource values. -/
  resourceMap : M.Resource →+o N.Resource
  /-- The model morphism controlled by `resourceMap`. -/
  modelMap : ResourceChangeModelHom resourceMap M.model N.model

namespace ResourceModelHom

variable {M N P Q : ResourceModel.{u, v, w}}

/-- The underlying ordinary functor between process categories. -/
abbrev toFunctor (F : ResourceModelHom M N) : M ⥤ N :=
  F.modelMap.toFunctor

instance (F : ResourceModelHom M N) :
    IsIso (Functor.LaxMonoidal.ε F.toFunctor) :=
  F.modelMap.unit_isIso

instance (F : ResourceModelHom M N) (X Y : M) :
    IsIso (Functor.LaxMonoidal.μ F.toFunctor X Y) :=
  F.modelMap.tensor_isIso X Y

/-- The identity total model morphism. -/
def id (M : ResourceModel.{u, v, w}) : ResourceModelHom M M where
  resourceMap := OrderAddMonoidHom.id M.Resource
  modelMap := ResourceChangeModelHom.id M.model

/-- Composition simultaneously composes resource translations and strong
model morphisms. -/
def comp (F : ResourceModelHom M N) (G : ResourceModelHom N P) :
    ResourceModelHom M P where
  resourceMap := G.resourceMap.comp F.resourceMap
  modelMap := F.modelMap.comp G.modelMap

@[simp]
theorem id_toFunctor (M : ResourceModel.{u, v, w}) :
    (id M).toFunctor = 𝟭 M :=
  rfl

@[simp]
theorem comp_toFunctor (F : ResourceModelHom M N) (G : ResourceModelHom N P) :
    (F.comp G).toFunctor = F.toFunctor ⋙ G.toFunctor :=
  rfl

@[simp]
theorem comp_resourceMap (F : ResourceModelHom M N)
    (G : ResourceModelHom N P) :
    (F.comp G).resourceMap = G.resourceMap.comp F.resourceMap :=
  rfl

end ResourceModelHom

/-- Total resource models form a quiver under heterogeneous strong model
morphisms. -/
instance : Quiver ResourceModel.{u, v, w} where
  Hom := ResourceModelHom

/-- A two-cell between total model morphisms.  Parallel one-cells must induce
the same resource translation, while their model maps are related by a
monoidal natural transformation. -/
structure ResourceModelTransformation {M N : ResourceModel.{u, v, w}}
    (F G : ResourceModelHom M N) where
  /-- Equality of the resource translations. -/
  resource_eq : F.resourceMap = G.resourceMap
  /-- The underlying natural transformation of process functors. -/
  toNatTrans : F.toFunctor ⟶ G.toFunctor
  /-- Compatibility with lax unit and tensor comparison maps. -/
  isMonoidal : NatTrans.IsMonoidal toNatTrans := by infer_instance

namespace ResourceModelTransformation

attribute [instance] isMonoidal

variable {M N P Q : ResourceModel.{u, v, w}}
variable {F G H I : ResourceModelHom M N}

/-- Bundle a resource-map equality and monoidal natural transformation. -/
def ofNatTrans (resource_eq : F.resourceMap = G.resourceMap)
    (eta : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal eta] :
    ResourceModelTransformation F G :=
  ⟨resource_eq, eta, inferInstance⟩

/-- Total model two-cells are determined by their underlying natural
transformations; equality proofs are proof-irrelevant. -/
@[ext]
theorem ext {eta theta : ResourceModelTransformation F G}
    (h : eta.toNatTrans = theta.toNatTrans) : eta = theta := by
  cases eta
  cases theta
  cases h
  rfl

/-- Vertical identity and composition make each total model hom-type a
category. -/
instance homCategory (M N : ResourceModel.{u, v, w}) :
    Category (ResourceModelHom M N) where
  Hom := ResourceModelTransformation
  id F := ofNatTrans rfl (𝟙 F.toFunctor)
  comp eta theta := ofNatTrans (eta.resource_eq.trans theta.resource_eq)
    (eta.toNatTrans ≫ theta.toNatTrans)
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
theorem id_toNatTrans (F : ResourceModelHom M N) :
    (𝟙 F : F ⟶ F).toNatTrans = 𝟙 F.toFunctor :=
  rfl

theorem id_resource_eq (F : ResourceModelHom M N) :
    (𝟙 F : F ⟶ F).resource_eq = rfl :=
  rfl

@[simp]
theorem comp_toNatTrans {F G H : ResourceModelHom M N}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    (eta ≫ theta).toNatTrans = eta.toNatTrans ≫ theta.toNatTrans :=
  rfl

set_option linter.style.haveILetI false in
/-- Left whiskering composes equal target resource maps with the fixed source
resource map. -/
def whiskerLeft (F : ResourceModelHom M N)
    {G H : ResourceModelHom N P} (eta : G ⟶ H) :
    F.comp G ⟶ F.comp H where
  resource_eq := congrArg
    (fun resourceMap ↦ resourceMap.comp F.resourceMap) eta.resource_eq
  toNatTrans := Functor.whiskerLeft F.toFunctor eta.toNatTrans
  isMonoidal := by
    letI : F.toFunctor.LaxMonoidal :=
      F.modelMap.toLaxBraided.laxBraided.toLaxMonoidal
    letI : G.toFunctor.LaxMonoidal :=
      G.modelMap.toLaxBraided.laxBraided.toLaxMonoidal
    letI : H.toFunctor.LaxMonoidal :=
      H.modelMap.toLaxBraided.laxBraided.toLaxMonoidal
    haveI : NatTrans.IsMonoidal eta.toNatTrans := eta.isMonoidal
    exact NatTrans.IsMonoidal.whiskerLeft eta.toNatTrans

set_option linter.style.haveILetI false in
/-- Right whiskering composes equal source resource maps with the fixed target
resource map. -/
def whiskerRight {F G : ResourceModelHom M N} (eta : F ⟶ G)
    (H : ResourceModelHom N P) :
    F.comp H ⟶ G.comp H where
  resource_eq := congrArg
    (fun resourceMap ↦ H.resourceMap.comp resourceMap) eta.resource_eq
  toNatTrans := Functor.whiskerRight eta.toNatTrans H.toFunctor
  isMonoidal := by
    letI : F.toFunctor.LaxMonoidal :=
      F.modelMap.toLaxBraided.laxBraided.toLaxMonoidal
    letI : G.toFunctor.LaxMonoidal :=
      G.modelMap.toLaxBraided.laxBraided.toLaxMonoidal
    letI : H.toFunctor.LaxMonoidal :=
      H.modelMap.toLaxBraided.laxBraided.toLaxMonoidal
    haveI : NatTrans.IsMonoidal eta.toNatTrans := eta.isMonoidal
    exact NatTrans.IsMonoidal.whiskerRight eta.toNatTrans

/-- Lift a monoidal natural isomorphism and equality of resource maps to an
isomorphism in a total-model local category. -/
def isoMk (resource_eq : F.resourceMap = G.resourceMap)
    (e : F.toFunctor ≅ G.toFunctor) [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := ofNatTrans resource_eq e.hom
  inv := ofNatTrans resource_eq.symm e.inv
  hom_inv_id := by
    apply ResourceModelTransformation.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply ResourceModelTransformation.ext
    exact e.inv_hom_id

@[simp]
theorem whiskerLeft_toNatTrans (F : ResourceModelHom M N)
    {G H : ResourceModelHom N P} (eta : G ⟶ H) :
    (whiskerLeft F eta).toNatTrans =
      Functor.whiskerLeft F.toFunctor eta.toNatTrans :=
  rfl

@[simp]
theorem whiskerRight_toNatTrans {F G : ResourceModelHom M N}
    (eta : F ⟶ G) (H : ResourceModelHom N P) :
    (whiskerRight eta H).toNatTrans =
      Functor.whiskerRight eta.toNatTrans H.toFunctor :=
  rfl

end ResourceModelTransformation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bicategory whose objects may use different resource algebras and whose
one-cells carry explicit ordered additive changes of resources. -/
instance resourceModelBicategory : Bicategory ResourceModel.{u, v, w} where
  id := ResourceModelHom.id
  comp := ResourceModelHom.comp
  homCategory := fun M N ↦ ResourceModelTransformation.homCategory M N
  whiskerLeft F _ _ eta := ResourceModelTransformation.whiskerLeft F eta
  whiskerRight eta H := ResourceModelTransformation.whiskerRight eta H
  associator F G H := ResourceModelTransformation.isoMk (by
      ext r
      rfl)
    (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
  leftUnitor F := ResourceModelTransformation.isoMk (by
      ext r
      rfl)
    (Functor.leftUnitor F.toFunctor)
  rightUnitor F := ResourceModelTransformation.isoMk (by
      ext r
      rfl)
    (Functor.rightUnitor F.toFunctor)
  whiskerLeft_id := by
    intro a b c f g
    apply ResourceModelTransformation.ext
    change Functor.whiskerLeft f.toFunctor (𝟙 g.toFunctor) =
      𝟙 (f.toFunctor ⋙ g.toFunctor)
    rfl
  whiskerLeft_comp := by
    intro a b c f g h i eta theta
    apply ResourceModelTransformation.ext
    change Functor.whiskerLeft f.toFunctor (eta.toNatTrans ≫ theta.toNatTrans) =
      Functor.whiskerLeft f.toFunctor eta.toNatTrans ≫
        Functor.whiskerLeft f.toFunctor theta.toNatTrans
    rfl
  id_whiskerLeft := by
    intro a b f g eta
    apply ResourceModelTransformation.ext
    change Functor.whiskerLeft (𝟭 a) eta.toNatTrans =
      (Functor.leftUnitor f.toFunctor).hom ≫ eta.toNatTrans ≫
        (Functor.leftUnitor g.toFunctor).inv
    ext X
    simp
  comp_whiskerLeft := by
    intro a b c d f g h h' eta
    apply ResourceModelTransformation.ext
    change Functor.whiskerLeft (f.toFunctor ⋙ g.toFunctor) eta.toNatTrans =
      (Functor.associator f.toFunctor g.toFunctor h.toFunctor).hom ≫
        Functor.whiskerLeft f.toFunctor
          (Functor.whiskerLeft g.toFunctor eta.toNatTrans) ≫
        (Functor.associator f.toFunctor g.toFunctor h'.toFunctor).inv
    ext X
    simp
  id_whiskerRight := by
    intro a b c f g
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight (𝟙 f.toFunctor) g.toFunctor =
      𝟙 (f.toFunctor ⋙ g.toFunctor)
    ext X
    simp
  comp_whiskerRight := by
    intro a b c f g h eta theta i
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight (eta.toNatTrans ≫ theta.toNatTrans) i.toFunctor =
      Functor.whiskerRight eta.toNatTrans i.toFunctor ≫
        Functor.whiskerRight theta.toNatTrans i.toFunctor
    ext X
    simp
  whiskerRight_id := by
    intro a b f g eta
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight eta.toNatTrans (𝟭 b) =
      (Functor.rightUnitor f.toFunctor).hom ≫ eta.toNatTrans ≫
        (Functor.rightUnitor g.toFunctor).inv
    ext X
    simp
  whiskerRight_comp := by
    intro a b c d f f' eta g h
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight eta.toNatTrans (g.toFunctor ⋙ h.toFunctor) =
      (Functor.associator f.toFunctor g.toFunctor h.toFunctor).inv ≫
        Functor.whiskerRight
          (Functor.whiskerRight eta.toNatTrans g.toFunctor) h.toFunctor ≫
        (Functor.associator f'.toFunctor g.toFunctor h.toFunctor).hom
    ext X
    simp
  whisker_assoc := by
    intro a b c d f g g' eta h
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight
        (Functor.whiskerLeft f.toFunctor eta.toNatTrans) h.toFunctor =
      (Functor.associator f.toFunctor g.toFunctor h.toFunctor).hom ≫
        Functor.whiskerLeft f.toFunctor
          (Functor.whiskerRight eta.toNatTrans h.toFunctor) ≫
        (Functor.associator f.toFunctor g'.toFunctor h.toFunctor).inv
    ext X
    simp
  whisker_exchange := by
    intro a b c f g h i eta theta
    apply ResourceModelTransformation.ext
    change Functor.whiskerLeft f.toFunctor theta.toNatTrans ≫
        Functor.whiskerRight eta.toNatTrans i.toFunctor =
      Functor.whiskerRight eta.toNatTrans h.toFunctor ≫
        Functor.whiskerLeft g.toFunctor theta.toNatTrans
    ext X
    exact (theta.toNatTrans.naturality (eta.toNatTrans.app X)).symm
  pentagon := by
    intro a b c d e f g h i
    apply ResourceModelTransformation.ext
    change Functor.whiskerRight
          (Functor.associator f.toFunctor g.toFunctor h.toFunctor).hom i.toFunctor ≫
        (Functor.associator f.toFunctor (g.toFunctor ⋙ h.toFunctor) i.toFunctor).hom ≫
        Functor.whiskerLeft f.toFunctor
          (Functor.associator g.toFunctor h.toFunctor i.toFunctor).hom =
      (Functor.associator (f.toFunctor ⋙ g.toFunctor) h.toFunctor i.toFunctor).hom ≫
        (Functor.associator f.toFunctor g.toFunctor (h.toFunctor ⋙ i.toFunctor)).hom
    ext X
    simp
  triangle := by
    intro a b c f g
    apply ResourceModelTransformation.ext
    change (Functor.associator f.toFunctor (𝟭 b) g.toFunctor).hom ≫
        Functor.whiskerLeft f.toFunctor (Functor.leftUnitor g.toFunctor).hom =
      Functor.whiskerRight (Functor.rightUnitor f.toFunctor).hom g.toFunctor
    ext X
    simp

end Ript.Higher
