import Mathlib.CategoryTheory.Bicategory.Basic
import Ript.Higher.ModelHom

/-!
# The bicategory of resource-indexed process models

For a fixed resource type `R`, this file constructs the bicategory whose

* objects are `ProcessModel R` values;
* 1-cells are resource-nonincreasing strong braided monoidal `ModelHom`s;
* 2-cells are monoidal natural transformations.

The local categories use ordinary vertical composition of natural
transformations.  Whiskering, associators, and unitors are inherited from the
underlying functors.  All bicategory laws are proved by reduction to the
corresponding componentwise functor equations.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- Process models form a quiver whose arrows are strong, resource-
nonincreasing model morphisms. -/
instance : Quiver (ProcessModel.{u, v, w} R) where
  Hom := ModelHom

/-- A monoidal natural transformation between parallel model morphisms. -/
structure ModelTransformation {M N : ProcessModel.{u, v, w} R}
    (F G : ModelHom M N) where
  /-- The underlying natural transformation. -/
  toNatTrans : F.toFunctor ⟶ G.toFunctor
  /-- Compatibility with the lax unit and tensor comparison maps. -/
  isMonoidal : NatTrans.IsMonoidal toNatTrans := by infer_instance

namespace ModelTransformation

attribute [instance] isMonoidal

variable {M N P : ProcessModel.{u, v, w} R}
variable {F G H : ModelHom M N}

/-- Bundle a monoidal natural transformation as a model 2-cell. -/
def ofNatTrans (eta : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal eta] :
    ModelTransformation F G :=
  ⟨eta, inferInstance⟩

/-- Model 2-cells are determined by their underlying natural transformations. -/
@[ext]
theorem ext {eta theta : ModelTransformation F G}
    (h : eta.toNatTrans = theta.toNatTrans) : eta = theta := by
  cases eta
  cases theta
  cases h
  rfl

/-- Vertical identity and composition make every model hom-type a category. -/
instance homCategory (M N : ProcessModel.{u, v, w} R) : Category (ModelHom M N) where
  Hom := ModelTransformation
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
theorem id_toNatTrans (F : ModelHom M N) :
    (𝟙 F : F ⟶ F).toNatTrans = 𝟙 F.toFunctor := rfl

@[simp]
theorem comp_toNatTrans {F G H : ModelHom M N} (eta : F ⟶ G)
    (theta : G ⟶ H) :
    (eta ≫ theta).toNatTrans = eta.toNatTrans ≫ theta.toNatTrans := rfl

/-- Lift a monoidal natural isomorphism to an isomorphism in a local model-hom
category.  Monoidality of the inverse follows from monoidality of the forward
map. -/
def isoMk (e : F.toFunctor ≅ G.toFunctor) [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := ofNatTrans e.hom
  inv := ofNatTrans e.inv
  hom_inv_id := by
    apply ModelTransformation.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply ModelTransformation.ext
    exact e.inv_hom_id

@[simp]
theorem isoMk_hom_toNatTrans (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).hom.toNatTrans = e.hom := rfl

@[simp]
theorem isoMk_inv_toNatTrans (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : (isoMk e).inv.toNatTrans = e.inv := rfl

end ModelTransformation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bicategory of resource-indexed symmetric monoidal process models. -/
instance modelBicategory : Bicategory (ProcessModel.{u, v, w} R) where
  id := ModelHom.id
  comp := ModelHom.comp
  homCategory := fun M N ↦ ModelTransformation.homCategory M N
  whiskerLeft F _ _ eta := ModelTransformation.ofNatTrans
    (Functor.whiskerLeft F.toFunctor eta.toNatTrans)
  whiskerRight eta H := ModelTransformation.ofNatTrans
    (Functor.whiskerRight eta.toNatTrans H.toFunctor)
  associator F G H := ModelTransformation.isoMk
    (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
  leftUnitor F := ModelTransformation.isoMk (Functor.leftUnitor F.toFunctor)
  rightUnitor F := ModelTransformation.isoMk (Functor.rightUnitor F.toFunctor)
  whiskerLeft_id := by
    intro a b c f g
    apply ModelTransformation.ext
    change Functor.whiskerLeft f.toFunctor (𝟙 g.toFunctor) =
      𝟙 (f.toFunctor ⋙ g.toFunctor)
    rfl
  whiskerLeft_comp := by
    intro a b c f g h i eta theta
    apply ModelTransformation.ext
    change Functor.whiskerLeft f.toFunctor (eta.toNatTrans ≫ theta.toNatTrans) =
      Functor.whiskerLeft f.toFunctor eta.toNatTrans ≫
        Functor.whiskerLeft f.toFunctor theta.toNatTrans
    rfl
  id_whiskerLeft := by
    intro a b f g eta
    apply ModelTransformation.ext
    change Functor.whiskerLeft (𝟭 a) eta.toNatTrans =
      (Functor.leftUnitor f.toFunctor).hom ≫ eta.toNatTrans ≫
        (Functor.leftUnitor g.toFunctor).inv
    ext X
    simp
  comp_whiskerLeft := by
    intro a b c d f g h h' eta
    apply ModelTransformation.ext
    change Functor.whiskerLeft (f.toFunctor ⋙ g.toFunctor) eta.toNatTrans =
      (Functor.associator f.toFunctor g.toFunctor h.toFunctor).hom ≫
        Functor.whiskerLeft f.toFunctor
          (Functor.whiskerLeft g.toFunctor eta.toNatTrans) ≫
        (Functor.associator f.toFunctor g.toFunctor h'.toFunctor).inv
    ext X
    simp
  id_whiskerRight := by
    intro a b c f g
    apply ModelTransformation.ext
    change Functor.whiskerRight (𝟙 f.toFunctor) g.toFunctor =
      𝟙 (f.toFunctor ⋙ g.toFunctor)
    ext X
    simp
  comp_whiskerRight := by
    intro a b c f g h eta theta i
    apply ModelTransformation.ext
    change Functor.whiskerRight (eta.toNatTrans ≫ theta.toNatTrans) i.toFunctor =
      Functor.whiskerRight eta.toNatTrans i.toFunctor ≫
        Functor.whiskerRight theta.toNatTrans i.toFunctor
    ext X
    simp
  whiskerRight_id := by
    intro a b f g eta
    apply ModelTransformation.ext
    change Functor.whiskerRight eta.toNatTrans (𝟭 b) =
      (Functor.rightUnitor f.toFunctor).hom ≫ eta.toNatTrans ≫
        (Functor.rightUnitor g.toFunctor).inv
    ext X
    simp
  whiskerRight_comp := by
    intro a b c d f f' eta g h
    apply ModelTransformation.ext
    change Functor.whiskerRight eta.toNatTrans (g.toFunctor ⋙ h.toFunctor) =
      (Functor.associator f.toFunctor g.toFunctor h.toFunctor).inv ≫
        Functor.whiskerRight
          (Functor.whiskerRight eta.toNatTrans g.toFunctor) h.toFunctor ≫
        (Functor.associator f'.toFunctor g.toFunctor h.toFunctor).hom
    ext X
    simp
  whisker_assoc := by
    intro a b c d f g g' eta h
    apply ModelTransformation.ext
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
    apply ModelTransformation.ext
    change Functor.whiskerLeft f.toFunctor theta.toNatTrans ≫
        Functor.whiskerRight eta.toNatTrans i.toFunctor =
      Functor.whiskerRight eta.toNatTrans h.toFunctor ≫
        Functor.whiskerLeft g.toFunctor theta.toNatTrans
    ext X
    exact (theta.toNatTrans.naturality (eta.toNatTrans.app X)).symm
  pentagon := by
    intro a b c d e f g h i
    apply ModelTransformation.ext
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
    apply ModelTransformation.ext
    change (Functor.associator f.toFunctor (𝟭 b) g.toFunctor).hom ≫
        Functor.whiskerLeft f.toFunctor (Functor.leftUnitor g.toFunctor).hom =
      Functor.whiskerRight (Functor.rightUnitor f.toFunctor).hom g.toFunctor
    ext X
    simp

end Ript.Higher
