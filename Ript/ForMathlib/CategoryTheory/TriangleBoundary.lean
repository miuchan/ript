import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Ript.ForMathlib.AlgebraicTopology.ReedyMatching
import Ript.ForMathlib.CategoryTheory.Isofibration

/-!
# The categorical boundary of a two-simplex

`TriangleBoundary C` records three vertices and the three oriented boundary
edges independently.  In particular, it does not identify the long edge with
the composite of the two short edges.  Restriction from
`ComposableArrows C 2` therefore expresses the genuine degree-two matching
map: its image consists precisely of the fillable triangular boundaries.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Opposite Simplicial
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory

universe v u

/-- Three vertices and three independently specified oriented boundary
edges of a two-simplex. -/
structure TriangleBoundary (C : Type u) [Category.{v} C] where
  /-- Initial vertex. -/
  vertex0 : C
  /-- Middle vertex. -/
  vertex1 : C
  /-- Final vertex. -/
  vertex2 : C
  /-- Short edge from the initial to the middle vertex. -/
  edge01 : vertex0 ⟶ vertex1
  /-- Short edge from the middle to the final vertex. -/
  edge12 : vertex1 ⟶ vertex2
  /-- Independent long edge from the initial to the final vertex. -/
  edge02 : vertex0 ⟶ vertex2

namespace TriangleBoundary

variable {C : Type u} [Category.{v} C]

/-- Extensionality for triangular boundary objects. -/
theorem obj_ext {X Y : TriangleBoundary C}
    (h0 : X.vertex0 = Y.vertex0)
    (h1 : X.vertex1 = Y.vertex1)
    (h2 : X.vertex2 = Y.vertex2)
    (h01 : HEq X.edge01 Y.edge01)
    (h12 : HEq X.edge12 Y.edge12)
    (h02 : HEq X.edge02 Y.edge02) : X = Y := by
  cases X
  cases Y
  simp_all

/-- A morphism of triangle boundaries is a triple of vertex maps commuting
with all three boundary edges. -/
structure Hom (X Y : TriangleBoundary C) where
  /-- Component at the initial vertex. -/
  app0 : X.vertex0 ⟶ Y.vertex0
  /-- Component at the middle vertex. -/
  app1 : X.vertex1 ⟶ Y.vertex1
  /-- Component at the final vertex. -/
  app2 : X.vertex2 ⟶ Y.vertex2
  naturality01 : X.edge01 ≫ app1 = app0 ≫ Y.edge01
  naturality12 : X.edge12 ≫ app2 = app1 ≫ Y.edge12
  naturality02 : X.edge02 ≫ app2 = app0 ≫ Y.edge02

@[ext]
theorem hom_ext {X Y : TriangleBoundary C} {f g : Hom X Y}
    (h0 : f.app0 = g.app0) (h1 : f.app1 = g.app1)
    (h2 : f.app2 = g.app2) : f = g := by
  cases f
  cases g
  simp_all

instance category : Category.{v} (TriangleBoundary C) where
  Hom := Hom
  id X := {
    app0 := 𝟙 _
    app1 := 𝟙 _
    app2 := 𝟙 _
    naturality01 := by simp
    naturality12 := by simp
    naturality02 := by simp }
  comp f g := {
    app0 := f.app0 ≫ g.app0
    app1 := f.app1 ≫ g.app1
    app2 := f.app2 ≫ g.app2
    naturality01 := by
      rw [← Category.assoc, f.naturality01, Category.assoc,
        g.naturality01, ← Category.assoc]
    naturality12 := by
      rw [← Category.assoc, f.naturality12, Category.assoc,
        g.naturality12, ← Category.assoc]
    naturality02 := by
      rw [← Category.assoc, f.naturality02, Category.assoc,
        g.naturality02, ← Category.assoc] }
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

@[simp]
theorem id_app0 (X : TriangleBoundary C) :
    (𝟙 X : X ⟶ X).app0 = 𝟙 X.vertex0 :=
  rfl

@[simp]
theorem id_app1 (X : TriangleBoundary C) :
    (𝟙 X : X ⟶ X).app1 = 𝟙 X.vertex1 :=
  rfl

@[simp]
theorem id_app2 (X : TriangleBoundary C) :
    (𝟙 X : X ⟶ X).app2 = 𝟙 X.vertex2 :=
  rfl

@[simp]
theorem comp_app0 {X Y Z : TriangleBoundary C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).app0 = f.app0 ≫ g.app0 :=
  rfl

@[simp]
theorem comp_app1 {X Y Z : TriangleBoundary C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).app1 = f.app1 ≫ g.app1 :=
  rfl

@[simp]
theorem comp_app2 {X Y Z : TriangleBoundary C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).app2 = f.app2 ≫ g.app2 :=
  rfl

/-- Constructor exposing all three independent boundary edges. -/
def ofEdges {X0 X1 X2 : C}
    (f01 : X0 ⟶ X1) (f12 : X1 ⟶ X2) (f02 : X0 ⟶ X2) :
    TriangleBoundary C where
  vertex0 := X0
  vertex1 := X1
  vertex2 := X2
  edge01 := f01
  edge12 := f12
  edge02 := f02

/-- A boundary whose long edge equals the composite of its short edges is
definitionally represented by the corresponding `ofEdges` constructor. -/
theorem ofEdges_comp_eq (Y : TriangleBoundary C)
    (h : Y.edge01 ≫ Y.edge12 = Y.edge02) :
    ofEdges Y.edge01 Y.edge12 (Y.edge01 ≫ Y.edge12) = Y := by
  cases Y with
  | mk X0 X1 X2 f01 f12 f02 =>
      dsimp at h ⊢
      cases h
      rfl

/-- Construct an isomorphism of triangle boundaries componentwise. -/
def isoMk {X Y : TriangleBoundary C}
    (app0 : X.vertex0 ≅ Y.vertex0)
    (app1 : X.vertex1 ≅ Y.vertex1)
    (app2 : X.vertex2 ≅ Y.vertex2)
    (w01 : X.edge01 ≫ app1.hom = app0.hom ≫ Y.edge01)
    (w12 : X.edge12 ≫ app2.hom = app1.hom ≫ Y.edge12)
    (w02 : X.edge02 ≫ app2.hom = app0.hom ≫ Y.edge02) : X ≅ Y where
  hom := {
    app0 := app0.hom
    app1 := app1.hom
    app2 := app2.hom
    naturality01 := w01
    naturality12 := w12
    naturality02 := w02 }
  inv := {
    app0 := app0.inv
    app1 := app1.inv
    app2 := app2.inv
    naturality01 := by
      rw [← cancel_epi app0.hom, ← Category.assoc, ← w01,
        Category.assoc, app1.hom_inv_id, Category.comp_id,
        ← Category.assoc, app0.hom_inv_id, Category.id_comp]
    naturality12 := by
      rw [← cancel_epi app1.hom, ← Category.assoc, ← w12,
        Category.assoc, app2.hom_inv_id, Category.comp_id,
        ← Category.assoc, app1.hom_inv_id, Category.id_comp]
    naturality02 := by
      rw [← cancel_epi app0.hom, ← Category.assoc, ← w02,
        Category.assoc, app2.hom_inv_id, Category.comp_id,
        ← Category.assoc, app0.hom_inv_id, Category.id_comp] }
  hom_inv_id := by apply hom_ext <;> simp
  inv_hom_id := by apply hom_ext <;> simp

/-- The component isomorphism at the first vertex of a boundary isomorphism. -/
def isoApp0 {X Y : TriangleBoundary C} (e : X ≅ Y) :
    X.vertex0 ≅ Y.vertex0 where
  hom := e.hom.app0
  inv := e.inv.app0
  hom_inv_id := by
    have h := congrArg (fun f : X ⟶ X => f.app0) e.hom_inv_id
    change e.hom.app0 ≫ e.inv.app0 = 𝟙 X.vertex0 at h
    exact h
  inv_hom_id := by
    have h := congrArg (fun f : Y ⟶ Y => f.app0) e.inv_hom_id
    change e.inv.app0 ≫ e.hom.app0 = 𝟙 Y.vertex0 at h
    exact h

/-- The component isomorphism at the middle vertex of a boundary isomorphism. -/
def isoApp1 {X Y : TriangleBoundary C} (e : X ≅ Y) :
    X.vertex1 ≅ Y.vertex1 where
  hom := e.hom.app1
  inv := e.inv.app1
  hom_inv_id := by
    have h := congrArg (fun f : X ⟶ X => f.app1) e.hom_inv_id
    change e.hom.app1 ≫ e.inv.app1 = 𝟙 X.vertex1 at h
    exact h
  inv_hom_id := by
    have h := congrArg (fun f : Y ⟶ Y => f.app1) e.inv_hom_id
    change e.inv.app1 ≫ e.hom.app1 = 𝟙 Y.vertex1 at h
    exact h

/-- The component isomorphism at the last vertex of a boundary isomorphism. -/
def isoApp2 {X Y : TriangleBoundary C} (e : X ≅ Y) :
    X.vertex2 ≅ Y.vertex2 where
  hom := e.hom.app2
  inv := e.inv.app2
  hom_inv_id := by
    have h := congrArg (fun f : X ⟶ X => f.app2) e.hom_inv_id
    change e.hom.app2 ≫ e.inv.app2 = 𝟙 X.vertex2 at h
    exact h
  inv_hom_id := by
    have h := congrArg (fun f : Y ⟶ Y => f.app2) e.inv_hom_id
    change e.inv.app2 ≫ e.hom.app2 = 𝟙 Y.vertex2 at h
    exact h

/-- A triangle-boundary morphism is invertible when its three vertex
components are invertible. -/
instance homIsIso_of_components {X Y : TriangleBoundary C}
    (f : X ⟶ Y) [IsIso f.app0] [IsIso f.app1] [IsIso f.app2] : IsIso f := by
  let e : X ≅ Y := isoMk (asIso f.app0) (asIso f.app1) (asIso f.app2)
    f.naturality01 f.naturality12 f.naturality02
  have h : f = e.hom := by apply hom_ext <;> rfl
  rw [h]
  infer_instance

/-- The first vertex component of an invertible boundary morphism is
invertible. -/
instance app0IsIso {X Y : TriangleBoundary C} (f : X ⟶ Y) [IsIso f] :
    IsIso f.app0 := by
  change IsIso (isoApp0 (asIso f)).hom
  infer_instance

/-- The middle vertex component of an invertible boundary morphism is
invertible. -/
instance app1IsIso {X Y : TriangleBoundary C} (f : X ⟶ Y) [IsIso f] :
    IsIso f.app1 := by
  change IsIso (isoApp1 (asIso f)).hom
  infer_instance

/-- The final vertex component of an invertible boundary morphism is
invertible. -/
instance app2IsIso {X Y : TriangleBoundary C} (f : X ⟶ Y) [IsIso f] :
    IsIso f.app2 := by
  change IsIso (isoApp2 (asIso f)).hom
  infer_instance

/-- Restrict a composable two-arrow diagram to its three boundary edges. -/
def restrictionFunctor :
    ComposableArrows C 2 ⥤ TriangleBoundary C where
  obj F := ofEdges (F.map' 0 1) (F.map' 1 2) (F.map' 0 2)
  map η := {
    app0 := η.app 0
    app1 := η.app 1
    app2 := η.app 2
    naturality01 := ComposableArrows.naturality' η 0 1
    naturality12 := ComposableArrows.naturality' η 1 2
    naturality02 := ComposableArrows.naturality' η 0 2 }
  map_id _ := by apply hom_ext <;> rfl
  map_comp _ _ := by apply hom_ext <;> rfl

@[simp]
theorem restrictionFunctor_obj_vertex0 (F : ComposableArrows C 2) :
    ((restrictionFunctor (C := C)).obj F).vertex0 = F.obj' 0 :=
  rfl

@[simp]
theorem restrictionFunctor_obj_vertex1 (F : ComposableArrows C 2) :
    ((restrictionFunctor (C := C)).obj F).vertex1 = F.obj' 1 :=
  rfl

@[simp]
theorem restrictionFunctor_obj_vertex2 (F : ComposableArrows C 2) :
    ((restrictionFunctor (C := C)).obj F).vertex2 = F.obj' 2 :=
  rfl

@[simp]
theorem restrictionFunctor_map_app0
    {F G : ComposableArrows C 2} (η : F ⟶ G) :
    ((restrictionFunctor (C := C)).map η).app0 = η.app 0 :=
  rfl

@[simp]
theorem restrictionFunctor_map_app1
    {F G : ComposableArrows C 2} (η : F ⟶ G) :
    ((restrictionFunctor (C := C)).map η).app1 = η.app 1 :=
  rfl

@[simp]
theorem restrictionFunctor_map_app2
    {F G : ComposableArrows C 2} (η : F ⟶ G) :
    ((restrictionFunctor (C := C)).map η).app2 = η.app 2 :=
  rfl

section FunctorBoundary

variable {T : Type*} [Category T]

/-- Turn a functor-valued family of triangle boundaries into one triangle
boundary internal to the functor category. -/
def curryFunctor (F : T ⥤ TriangleBoundary C) :
    TriangleBoundary (T ⥤ C) where
  vertex0 := {
    obj X := (F.obj X).vertex0
    map f := (F.map f).app0
    map_id X := by
      have h := congrArg (fun g : F.obj X ⟶ F.obj X => g.app0)
        (F.map_id X)
      exact h.trans (id_app0 (F.obj X))
    map_comp f g := by
      have h := congrArg (fun k : F.obj _ ⟶ F.obj _ => k.app0)
        (F.map_comp f g)
      exact h.trans (comp_app0 (F.map f) (F.map g)) }
  vertex1 := {
    obj X := (F.obj X).vertex1
    map f := (F.map f).app1
    map_id X := by
      have h := congrArg (fun g : F.obj X ⟶ F.obj X => g.app1)
        (F.map_id X)
      exact h.trans (id_app1 (F.obj X))
    map_comp f g := by
      have h := congrArg (fun k : F.obj _ ⟶ F.obj _ => k.app1)
        (F.map_comp f g)
      exact h.trans (comp_app1 (F.map f) (F.map g)) }
  vertex2 := {
    obj X := (F.obj X).vertex2
    map f := (F.map f).app2
    map_id X := by
      have h := congrArg (fun g : F.obj X ⟶ F.obj X => g.app2)
        (F.map_id X)
      exact h.trans (id_app2 (F.obj X))
    map_comp f g := by
      have h := congrArg (fun k : F.obj _ ⟶ F.obj _ => k.app2)
        (F.map_comp f g)
      exact h.trans (comp_app2 (F.map f) (F.map g)) }
  edge01 := {
    app X := (F.obj X).edge01
    naturality := by
      intro X Y f
      exact (F.map f).naturality01.symm }
  edge12 := {
    app X := (F.obj X).edge12
    naturality := by
      intro X Y f
      exact (F.map f).naturality12.symm }
  edge02 := {
    app X := (F.obj X).edge02
    naturality := by
      intro X Y f
      exact (F.map f).naturality02.symm }

/-- Evaluate an internal triangle boundary in a functor category pointwise. -/
def uncurryFunctor (Y : TriangleBoundary (T ⥤ C)) :
    T ⥤ TriangleBoundary C where
  obj X := ofEdges (Y.edge01.app X) (Y.edge12.app X) (Y.edge02.app X)
  map f := {
    app0 := Y.vertex0.map f
    app1 := Y.vertex1.map f
    app2 := Y.vertex2.map f
    naturality01 := (Y.edge01.naturality f).symm
    naturality12 := (Y.edge12.naturality f).symm
    naturality02 := (Y.edge02.naturality f).symm }
  map_id X := by
    apply hom_ext
    · exact Y.vertex0.map_id X
    · exact Y.vertex1.map_id X
    · exact Y.vertex2.map_id X
  map_comp f g := by
    apply hom_ext
    · exact Y.vertex0.map_comp f g
    · exact Y.vertex1.map_comp f g
    · exact Y.vertex2.map_comp f g

/-- Currying and pointwise evaluation are mutually inverse.  This is the
hom-wise representability statement for triangular boundary data. -/
def functorBoundaryEquiv :
    (T ⥤ TriangleBoundary C) ≃ TriangleBoundary (T ⥤ C) where
  toFun := curryFunctor
  invFun := uncurryFunctor
  left_inv F := by
    let hObj : ∀ X, (uncurryFunctor (curryFunctor F)).obj X = F.obj X :=
      fun X => obj_ext rfl rfl rfl (HEq.refl _) (HEq.refl _) (HEq.refl _)
    apply CategoryTheory.Functor.hext hObj
    intro X Y f
    cases hObj X
    cases hObj Y
    apply heq_of_eq
    apply hom_ext <;> rfl
  right_inv Y := by
    apply obj_ext
    · apply CategoryTheory.Functor.hext
      · intro X
        rfl
      · intro X Z f
        rfl
    · apply CategoryTheory.Functor.hext
      · intro X
        rfl
      · intro X Z f
        rfl
    · apply CategoryTheory.Functor.hext
      · intro X
        rfl
      · intro X Z f
        rfl
    · apply heq_of_eq
      apply NatTrans.ext
      funext X
      rfl
    · apply heq_of_eq
      apply NatTrans.ext
      funext X
      rfl
    · apply heq_of_eq
      apply NatTrans.ext
      funext X
      rfl

end FunctorBoundary

section RestrictionAlongBoundary

/-- Vertex of a triangular boundary selected by an element of `Fin 3`. -/
def vertexAt (Y : TriangleBoundary C) : Fin 3 → C
  | ⟨0, _⟩ => Y.vertex0
  | ⟨1, _⟩ => Y.vertex1
  | ⟨2, _⟩ => Y.vertex2

@[simp]
theorem vertexAt_zero (Y : TriangleBoundary C) : vertexAt Y 0 = Y.vertex0 :=
  rfl

@[simp]
theorem vertexAt_one (Y : TriangleBoundary C) : vertexAt Y 1 = Y.vertex1 :=
  rfl

@[simp]
theorem vertexAt_two (Y : TriangleBoundary C) : vertexAt Y 2 = Y.vertex2 :=
  rfl

private theorem not_fin3_one_le_zero : ¬ ((1 : Fin 3) ≤ 0) := by decide

private theorem not_fin3_two_le_zero : ¬ ((2 : Fin 3) ≤ 0) := by decide

private theorem not_fin3_two_le_one : ¬ ((2 : Fin 3) ≤ 1) := by decide

/-- Boundary edge selected by an ordered pair of vertices. -/
def edgeAt (Y : TriangleBoundary C) (i j : Fin 3) (h : i ≤ j) :
    vertexAt Y i ⟶ vertexAt Y j :=
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩ => Y.edge01
  | ⟨0, _⟩, ⟨2, _⟩ => Y.edge02
  | ⟨1, _⟩, ⟨0, _⟩ => False.elim
      (not_fin3_one_le_zero h)
  | ⟨1, _⟩, ⟨1, _⟩ => 𝟙 _
  | ⟨1, _⟩, ⟨2, _⟩ => Y.edge12
  | ⟨2, _⟩, ⟨0, _⟩ => False.elim
      (not_fin3_two_le_zero h)
  | ⟨2, _⟩, ⟨1, _⟩ => False.elim
      (not_fin3_two_le_one h)
  | ⟨2, _⟩, ⟨2, _⟩ => 𝟙 _

/-- Component of a boundary morphism at a selected vertex. -/
def appAt {X Y : TriangleBoundary C} (η : X ⟶ Y) (i : Fin 3) :
    vertexAt X i ⟶ vertexAt Y i :=
  match i with
  | ⟨0, _⟩ => η.app0
  | ⟨1, _⟩ => η.app1
  | ⟨2, _⟩ => η.app2

@[simp]
theorem appAt_zero {X Y : TriangleBoundary C} (η : X ⟶ Y) :
    appAt η 0 = η.app0 :=
  rfl

@[simp]
theorem appAt_one {X Y : TriangleBoundary C} (η : X ⟶ Y) :
    appAt η 1 = η.app1 :=
  rfl

@[simp]
theorem appAt_two {X Y : TriangleBoundary C} (η : X ⟶ Y) :
    appAt η 2 = η.app2 :=
  rfl

/-- Every selected vertex component of an invertible boundary morphism is
invertible. -/
instance appAtIsIso {X Y : TriangleBoundary C} (η : X ⟶ Y) [IsIso η]
    (i : Fin 3) : IsIso (appAt η i) := by
  fin_cases i
  · exact app0IsIso η
  · exact app1IsIso η
  · exact app2IsIso η

/-- Naturality of a boundary morphism along every selected boundary edge. -/
theorem edgeAt_naturality {X Y : TriangleBoundary C} (η : X ⟶ Y)
    (i j : Fin 3) (h : i ≤ j) :
    edgeAt X i j h ≫ appAt η j =
      appAt η i ≫ edgeAt Y i j h := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp only [Fin.mk_le_mk] at h
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hiCases with rfl | rfl | rfl <;>
    rcases hjCases with rfl | rfl | rfl <;>
      simp_all [edgeAt, appAt, η.naturality01, η.naturality12,
        η.naturality02]

/-- Vertex selection after restricting a full two-simplex recovers the
corresponding object of the original composable-arrow functor. -/
theorem vertexAt_restrictionFunctor
    (F : ComposableArrows C 2) (i : Fin 3) :
    vertexAt ((restrictionFunctor (C := C)).obj F) i = F.obj i := by
  fin_cases i <;> rfl

/-- A component of a natural transformation is unchanged by restricting to
the triangular boundary, up to the dependent endpoint identification. -/
theorem appAt_restrictionFunctor
    {F G : ComposableArrows C 2} (η : F ⟶ G) (i : Fin 3) :
    HEq (appAt ((restrictionFunctor (C := C)).map η) i) (η.app i) := by
  fin_cases i <;> rfl

/-- Every selected edge of the boundary of a full two-simplex is the
corresponding map of the original functor. -/
theorem edgeAt_restrictionFunctor
    (F : ComposableArrows C 2) (i j : Fin 3) (h : i ≤ j) :
    HEq (edgeAt ((restrictionFunctor (C := C)).obj F) i j h)
      (F.map (homOfLE h)) := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp only [Fin.mk_le_mk] at h
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hiCases with rfl | rfl | rfl <;>
    rcases hjCases with rfl | rfl | rfl <;>
      simp_all [edgeAt, restrictionFunctor, ofEdges]

/-- Selected identity edges are identities. -/
theorem edgeAt_self (Y : TriangleBoundary C) (i : Fin 3) :
    edgeAt Y i i (le_refl i) = 𝟙 _ := by
  fin_cases i <;> rfl

/-- Boundary-edge composition is strict unless the three selected vertices
are exactly `0,1,2`; that excluded case is the missing two-simplex interior. -/
theorem edgeAt_comp_of_not_three
    (Y : TriangleBoundary C) (i j k : Fin 3)
    (hij : i ≤ j) (hjk : j ≤ k)
    (hthree : ¬ (i = 0 ∧ j = 1 ∧ k = 2)) :
    edgeAt Y i k (hij.trans hjk) =
      edgeAt Y i j hij ≫ edgeAt Y j k hjk := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only [Fin.mk_le_mk] at hij hjk
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hiCases with rfl | rfl | rfl <;>
    rcases hjCases with rfl | rfl | rfl <;>
      rcases hkCases with rfl | rfl | rfl <;>
        simp_all [edgeAt]

@[simp]
theorem appAt_id (Y : TriangleBoundary C) (i : Fin 3) :
    appAt (𝟙 Y) i = 𝟙 _ := by
  fin_cases i <;> rfl

@[simp]
theorem appAt_comp {X Y Z : TriangleBoundary C}
    (η : X ⟶ Y) (θ : Y ⟶ Z) (i : Fin 3) :
    appAt (η ≫ θ) i = appAt η i ≫ appAt θ i := by
  fin_cases i <;> rfl

/-- A non-surjective simplex in `Δ[2]` cannot contain the ordered triple of
all three vertices. -/
theorem not_three_of_not_surjective {m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ)
    (i j k : Fin (m + 1)) :
    ¬ (σ i = 0 ∧ σ j = 1 ∧ σ k = 2) := by
  rintro ⟨hi, hj, hk⟩
  apply hσ
  intro x
  fin_cases x
  · exact ⟨i, hi⟩
  · exact ⟨j, hj⟩
  · exact ⟨k, hk⟩

/-- Restrict one triangular boundary along a non-surjective simplex of
`Δ[2]`.  Non-surjectivity is exactly what makes composition strict without a
chosen filler for the missing interior. -/
def restrictAlong {m : ℕ} (Y : TriangleBoundary C)
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ) : ComposableArrows C m where
  obj i := vertexAt Y (σ i)
  map := fun {i j} f => edgeAt Y (σ i) (σ j)
    (σ.toOrderHom.monotone (leOfHom f))
  map_id i := by
    apply edgeAt_self
  map_comp := fun {i j k} f g => by
    apply edgeAt_comp_of_not_three
    exact not_three_of_not_surjective σ hσ i j k

/-- Restricting the boundary of a full two-simplex along any boundary simplex
is exactly precomposition of the original composable-arrow functor. -/
theorem restrictAlong_restrictionFunctor {m : ℕ}
    (F : ComposableArrows C 2)
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ) :
    restrictAlong ((restrictionFunctor (C := C)).obj F) σ hσ =
      (ComposableArrows.whiskerLeftFunctor
        (SimplexCategory.toCat.map σ).toFunctor).obj F := by
  apply CategoryTheory.Functor.hext
  · intro i
    exact vertexAt_restrictionFunctor F (σ i)
  · intro i j f
    change edgeAt ((restrictionFunctor (C := C)).obj F) (σ i) (σ j) _ ≍
      F.map (homOfLE (σ.toOrderHom.monotone (leOfHom f)))
    exact edgeAt_restrictionFunctor F _ _ _

/-- Restriction along a fixed non-surjective simplex is functorial in the
triangular boundary. -/
def restrictAlongFunctor {m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ) :
    TriangleBoundary C ⥤ ComposableArrows C m where
  obj Y := restrictAlong Y σ hσ
  map η := {
    app i := appAt η (σ i)
    naturality := by
      intro i j f
      exact edgeAt_naturality η (σ i) (σ j)
        (σ.toOrderHom.monotone (leOfHom f)) }
  map_id Y := by
    apply NatTrans.ext
    funext i
    apply appAt_id
  map_comp η θ := by
    apply NatTrans.ext
    funext i
    apply appAt_comp

/-- Restricting full two-simplices to triangular boundaries and then along a
fixed boundary simplex is strictly the ordinary precomposition functor. -/
theorem restrictionFunctor_comp_restrictAlongFunctor {m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ) :
    restrictionFunctor (C := C) ⋙ restrictAlongFunctor (C := C) σ hσ =
      ComposableArrows.whiskerLeftFunctor
        (SimplexCategory.toCat.map σ).toFunctor := by
  let hobj : ∀ F : ComposableArrows C 2,
      (restrictionFunctor (C := C) ⋙
          restrictAlongFunctor (C := C) σ hσ).obj F =
        (ComposableArrows.whiskerLeftFunctor
          (SimplexCategory.toCat.map σ).toFunctor).obj F :=
    fun F => restrictAlong_restrictionFunctor F σ hσ
  let e :
      restrictionFunctor (C := C) ⋙ restrictAlongFunctor (C := C) σ hσ ≅
        ComposableArrows.whiskerLeftFunctor
          (SimplexCategory.toCat.map σ).toFunctor :=
    NatIso.ofComponents (fun F => eqToIso (hobj F)) (by
      intro F G η
      apply NatTrans.ext
      funext i
      simp only [NatTrans.comp_app, Functor.comp_map, eqToIso.hom,
        eqToHom_app]
      rw [comp_eqToHom_iff]
      rw [Category.assoc]
      apply (conj_eqToHom_iff_heq _ _ _ _).2
      change HEq (appAt ((restrictionFunctor (C := C)).map η) (σ i))
        (η.app (σ i))
      exact appAt_restrictionFunctor η (σ i)
      exact congrArg (fun H : ComposableArrows C m => H.obj i) (hobj G))
  exact CategoryTheory.Functor.ext_of_iso e hobj (by
    intro F
    rfl)

/-- Precomposition preserves non-surjectivity into the triangle. -/
theorem notSurjective_comp {l m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ)
    (τ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) :
    ¬ Function.Surjective (τ ≫ σ) := by
  intro h
  apply hσ
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨τ x, hx⟩

/-- Restriction along a boundary simplex commutes strictly with
precomposition. -/
theorem restrictAlongFunctor_comp {l m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ)
    (τ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) :
    restrictAlongFunctor (C := C) σ hσ ⋙
        ComposableArrows.whiskerLeftFunctor
          (SimplexCategory.toCat.map τ).toFunctor =
      restrictAlongFunctor (C := C) (τ ≫ σ)
        (notSurjective_comp σ hσ τ) := by
  apply CategoryTheory.Functor.hext
  · intro Y
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      rfl
  · intro X Y η
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    rfl

end RestrictionAlongBoundary

/-- A triangular boundary determines a simplicial map from the boundary of
the standard two-simplex into the categorical nerve. -/
def toBoundaryNerveMap (Y : TriangleBoundary C) :
    (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C where
  app Δ := ↾fun s ↦ restrictAlong Y
    (SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ s)) s.property
  naturality := by
    intro Δ Γ f
    ext s
    let σ := SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ s)
    let τ := f.unop
    have hσ : ¬ Function.Surjective σ := s.property
    have hfun := restrictAlongFunctor_comp (C := C) σ hσ τ
    have hobj := congrArg (fun F => F.obj Y) hfun
    have hs : SSet.stdSimplex.objEquiv
        ((SSet.boundary 2).ι.app Γ
          ((SSet.boundary 2).toSSet.map f s)) =
      τ ≫ σ := by
      apply SSet.stdSimplex.objEquiv.symm.injective
      dsimp [σ, τ]
      rw [← SSet.stdSimplex.map_apply]
      rw [← NatTrans.naturality_apply (SSet.boundary 2).ι f s]
      exact Equiv.symm_apply_apply _ _
    change restrictAlong Y
        (SSet.stdSimplex.objEquiv
          ((SSet.boundary 2).ι.app Γ
            ((SSet.boundary 2).toSSet.map f s)))
          ((SSet.boundary 2).toSSet.map f s).property =
      (ComposableArrows.whiskerLeftFunctor
        (SimplexCategory.toCat.map τ).toFunctor).obj
          (restrictAlong Y σ hσ)
    cases hs
    exact hobj.symm

/-- Canonical edge simplex extracted from a boundary-to-nerve map. -/
def boundaryNerveFace
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (i : Fin 3) : ComposableArrows C 1 :=
  φ.app _
    (SSet.degreeTwoBoundaryFaceElement.{max u v} i).unop.unop.snd

/-- Every coface of the standard two-simplex misses one vertex. -/
theorem degreeTwoCoface_not_surjective (i : Fin 3) :
    ¬ Function.Surjective (SimplexCategory.δ i) := by
  fin_cases i <;> decide

/-- A factorization of a non-surjective simplex in `Δ[2]` through one of its
three canonical one-dimensional cofaces. -/
structure CofaceFactorization {m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2) where
  /-- The omitted vertex, hence the selected coface. -/
  i : Fin 3
  /-- The residual simplex in the selected edge. -/
  τ : SimplexCategory.mk m ⟶ SimplexCategory.mk 1
  /-- The original simplex is the residual simplex followed by the coface. -/
  fac : τ ≫ SimplexCategory.δ i = σ

/-- Every non-surjective simplex of `Δ[2]` factors through one of its three
edges. -/
theorem cofaceFactorization_nonempty {m : ℕ}
    (σ : SimplexCategory.mk m ⟶ SimplexCategory.mk 2)
    (hσ : ¬ Function.Surjective σ) :
    Nonempty (CofaceFactorization σ) := by
  classical
  simp only [Function.Surjective] at hσ
  push Not at hσ
  obtain ⟨i, hi⟩ := hσ
  fin_cases i
  · refine ⟨{
      i := 0
      τ := σ ≫ SimplexCategory.σ 0
      fac := ?_ }⟩
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext x
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact Fin.succAbove_predAbove (p := (0 : Fin 2)) (i := σ x)
      (by simpa using hi x)
  · refine ⟨{
      i := 1
      τ := σ ≫ SimplexCategory.σ 1
      fac := ?_ }⟩
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext x
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact Fin.succAbove_predAbove (p := (1 : Fin 2)) (i := σ x)
      (by simpa using hi x)
  · refine ⟨{
      i := 2
      τ := σ ≫ SimplexCategory.σ 1
      fac := ?_ }⟩
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext x
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact Fin.succ_succAbove_predAbove (p := (1 : Fin 2)) (i := σ x)
      (by simpa using hi x)

/-- A boundary simplex is obtained by precomposing the canonical edge selected
by any of its coface factorizations. -/
theorem boundarySimplex_eq_coface_map {m : ℕ}
    (s : (∂Δ[2] : SSet.{u}).obj (op (SimplexCategory.mk m)))
    (e : CofaceFactorization
      (SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app _ s))) :
    (SSet.boundary 2).toSSet.map e.τ.op
        (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd = s := by
  apply Subtype.ext
  change (SSet.boundary 2).ι.app _
      ((SSet.boundary 2).toSSet.map e.τ.op
        (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd) =
    (SSet.boundary 2).ι.app _ s
  have hn := (SSet.boundary 2).ι.naturality e.τ.op
  have h := ConcreteCategory.congr_hom hn
    (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd
  have h' : (SSet.boundary 2).ι.app _
        ((SSet.boundary 2).toSSet.map e.τ.op
          (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd) =
      (SSet.stdSimplex.obj (SimplexCategory.mk 2)).map e.τ.op
        ((SSet.boundary 2).ι.app _
          (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd) := by
    change (SSet.boundary 2).ι.app _
        ((SSet.boundary 2).toSSet.map e.τ.op
          (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd) =
      (SSet.stdSimplex.obj (SimplexCategory.mk 2)).map e.τ.op
        ((SSet.boundary 2).ι.app _
          (SSet.degreeTwoBoundaryFaceElement.{u} e.i).unop.unop.snd) at h
    exact h
  rw [h']
  apply SSet.stdSimplex.objEquiv.{u}.injective
  rw [SSet.stdSimplex.map_apply]
  change e.τ ≫ SimplexCategory.δ e.i =
    SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app _ s)
  exact e.fac

/-- Extracting a canonical face from an encoded triangle boundary recovers
restriction along the corresponding coface.  The explicit equality
elimination handles the dependent non-surjectivity witness. -/
theorem boundaryNerveFace_toBoundaryNerveMap
    (Y : TriangleBoundary C) (i : Fin 3) :
    boundaryNerveFace (toBoundaryNerveMap Y) i =
      restrictAlong Y (SimplexCategory.δ i)
        (degreeTwoCoface_not_surjective i) := by
  change restrictAlong Y
      (SSet.boundaryMatchingSimplex.{max u v} 2
        (SSet.degreeTwoBoundaryFaceElement.{max u v} i))
      (SSet.boundaryMatchingSimplex_not_surjective.{max u v} 2
        (SSet.degreeTwoBoundaryFaceElement.{max u v} i)) = _
  have h :=
    SSet.boundaryMatchingSimplex_degreeTwoBoundaryFaceElement.{max u v} i
  cases h
  rfl

/-- Canonical vertex simplex extracted from a boundary-to-nerve map. -/
def boundaryNerveVertex
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (r : Fin 3) : ComposableArrows C 0 :=
  φ.app _
    (SSet.degreeTwoBoundaryVertexElement.{max u v} r).unop.unop.snd

/-- Naturality along a canonical face-to-vertex incidence identifies the
extracted vertex with the corresponding endpoint restriction of the edge. -/
theorem boundaryNerveFace_endpoint
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (i : Fin 3) (t : Fin 2) :
    boundaryNerveVertex φ ((SimplexCategory.δ i) t) =
      (ComposableArrows.whiskerLeftFunctor
        (SimplexCategory.toCat.map
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk 1) t)).toFunctor).obj
        (boundaryNerveFace φ i) := by
  let q := SSet.degreeTwoBoundaryFaceToVertex.{max u v} i t
  let face := (SSet.degreeTwoBoundaryFaceElement.{max u v} i).unop.unop
  have hn := φ.naturality q.unop.unop.val
  have h := ConcreteCategory.congr_hom hn face.snd
  change boundaryNerveVertex φ ((SimplexCategory.δ i) t) =
    (ComposableArrows.whiskerLeftFunctor
      (SimplexCategory.toCat.map
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk 1) t)).toFunctor).obj
      (boundaryNerveFace φ i) at h
  exact h

/-- Object of `C` represented by a canonical extracted boundary vertex. -/
def boundaryNerveVertexObject
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (r : Fin 3) : C :=
  (boundaryNerveVertex φ r).obj' 0

/-- Object-level endpoint equality extracted from incidence naturality. -/
theorem boundaryNerveFace_endpoint_obj
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (i : Fin 3) (t : Fin 2) :
    boundaryNerveVertexObject φ ((SimplexCategory.δ i) t) =
      (boundaryNerveFace φ i).obj t := by
  exact congrArg (fun F : ComposableArrows C 0 => F.obj' 0)
    (boundaryNerveFace_endpoint φ i t)

/-- Extracted edge transported to the corresponding canonical vertex
objects. -/
def boundaryNerveEdge
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (i : Fin 3) :
    boundaryNerveVertexObject φ ((SimplexCategory.δ i) 0) ⟶
      boundaryNerveVertexObject φ ((SimplexCategory.δ i) 1) :=
  eqToHom (boundaryNerveFace_endpoint_obj φ i 0) ≫
    (boundaryNerveFace φ i).hom ≫
      eqToHom (boundaryNerveFace_endpoint_obj φ i 1).symm

/-- Transporting an extracted face edge to the canonical vertex objects does
not change the underlying morphism, up to heterogeneous equality. -/
theorem boundaryNerveEdge_heq_boundaryNerveFace
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (i : Fin 3) :
    HEq (boundaryNerveEdge φ i) (boundaryNerveFace φ i).hom := by
  unfold boundaryNerveEdge
  simp

/-- Decode a simplicial boundary map into its three vertices and three
independent edges. -/
def ofBoundaryNerveMap
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) :
    TriangleBoundary C where
  vertex0 := boundaryNerveVertexObject φ 0
  vertex1 := boundaryNerveVertexObject φ 1
  vertex2 := boundaryNerveVertexObject φ 2
  edge01 := boundaryNerveEdge φ 2
  edge12 := boundaryNerveEdge φ 0
  edge02 := boundaryNerveEdge φ 1

/-- Restricting a decoded boundary map back to any canonical coface recovers
the original extracted one-simplex exactly. -/
theorem restrictAlong_ofBoundaryNerveMap_coface
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C)
    (i : Fin 3) :
    restrictAlong (ofBoundaryNerveMap φ) (SimplexCategory.δ i)
        (degreeTwoCoface_not_surjective i) = boundaryNerveFace φ i := by
  fin_cases i
  · refine ComposableArrows.ext₁
      (boundaryNerveFace_endpoint_obj φ 0 0)
      (boundaryNerveFace_endpoint_obj φ 0 1) ?_
    rfl
  · refine ComposableArrows.ext₁
      (boundaryNerveFace_endpoint_obj φ 1 0)
      (boundaryNerveFace_endpoint_obj φ 1 1) ?_
    rfl
  · refine ComposableArrows.ext₁
      (boundaryNerveFace_endpoint_obj φ 2 0)
      (boundaryNerveFace_endpoint_obj φ 2 1) ?_
    rfl

/-- Vertices of the canonical encoding decode to the original selected
vertices. -/
theorem boundaryNerveVertexObject_toBoundaryNerveMap
    (Y : TriangleBoundary C) (r : Fin 3) :
    boundaryNerveVertexObject (toBoundaryNerveMap Y) r = vertexAt Y r := by
  rcases r with ⟨r, hr⟩
  have hCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

/-- The canonical edge `01` survives boundary encoding and decoding exactly. -/
theorem boundaryNerveEdge_toBoundaryNerveMap_edge01
    (Y : TriangleBoundary C) :
    boundaryNerveEdge (toBoundaryNerveMap Y) 2 = Y.edge01 := by
  apply eq_of_heq
  exact (boundaryNerveEdge_heq_boundaryNerveFace _ _).trans (by
    have h := boundaryNerveFace_toBoundaryNerveMap Y 2
    cases h
    rfl)

/-- The canonical edge `12` survives boundary encoding and decoding exactly. -/
theorem boundaryNerveEdge_toBoundaryNerveMap_edge12
    (Y : TriangleBoundary C) :
    boundaryNerveEdge (toBoundaryNerveMap Y) 0 = Y.edge12 := by
  apply eq_of_heq
  exact (boundaryNerveEdge_heq_boundaryNerveFace _ _).trans (by
    have h := boundaryNerveFace_toBoundaryNerveMap Y 0
    cases h
    rfl)

/-- The canonical edge `02` survives boundary encoding and decoding exactly. -/
theorem boundaryNerveEdge_toBoundaryNerveMap_edge02
    (Y : TriangleBoundary C) :
    boundaryNerveEdge (toBoundaryNerveMap Y) 1 = Y.edge02 := by
  apply eq_of_heq
  exact (boundaryNerveEdge_heq_boundaryNerveFace _ _).trans (by
    have h := boundaryNerveFace_toBoundaryNerveMap Y 1
    cases h
    rfl)

/-- Decoding the complete simplicial boundary encoding is a strict left
inverse on triangular boundaries. -/
theorem ofBoundaryNerveMap_toBoundaryNerveMap (Y : TriangleBoundary C) :
    ofBoundaryNerveMap (toBoundaryNerveMap Y) = Y := by
  apply obj_ext
  · exact boundaryNerveVertexObject_toBoundaryNerveMap Y 0
  · exact boundaryNerveVertexObject_toBoundaryNerveMap Y 1
  · exact boundaryNerveVertexObject_toBoundaryNerveMap Y 2
  · exact heq_of_eq (boundaryNerveEdge_toBoundaryNerveMap_edge01 Y)
  · exact heq_of_eq (boundaryNerveEdge_toBoundaryNerveMap_edge12 Y)
  · exact heq_of_eq (boundaryNerveEdge_toBoundaryNerveMap_edge02 Y)

/-- Encoding the decoded data of an arbitrary simplicial boundary map
recovers that map in every degree.  The proof factors each boundary simplex
through one canonical edge and then uses simplicial naturality. -/
theorem toBoundaryNerveMap_ofBoundaryNerveMap
    (φ : (∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) :
    toBoundaryNerveMap (ofBoundaryNerveMap φ) = φ := by
  ext Δ s
  let σ := SSet.stdSimplex.objEquiv
    ((SSet.boundary 2).ι.app Δ s)
  have hσ : ¬ Function.Surjective σ := s.property
  obtain ⟨e⟩ := cofaceFactorization_nonempty σ hσ
  have hs := boundarySimplex_eq_coface_map s e
  rw [← hs]
  let face : (∂Δ[2] : SSet.{max u v}).obj
      (op (SimplexCategory.mk 1)) :=
    (SSet.degreeTwoBoundaryFaceElement.{max u v} e.i).unop.unop.snd
  have hleft := ConcreteCategory.congr_hom
    ((toBoundaryNerveMap (ofBoundaryNerveMap φ)).naturality e.τ.op) face
  have hright := ConcreteCategory.congr_hom
    (φ.naturality e.τ.op) face
  change (toBoundaryNerveMap (ofBoundaryNerveMap φ)).app _
      ((SSet.boundary 2).toSSet.map e.τ.op face) =
    (CategoryTheory.nerve C).map e.τ.op
      ((toBoundaryNerveMap (ofBoundaryNerveMap φ)).app _ face) at hleft
  change φ.app _ ((SSet.boundary 2).toSSet.map e.τ.op face) =
    (CategoryTheory.nerve C).map e.τ.op (φ.app _ face) at hright
  have hface :
      boundaryNerveFace (toBoundaryNerveMap (ofBoundaryNerveMap φ)) e.i =
        boundaryNerveFace φ e.i := by
    rw [boundaryNerveFace_toBoundaryNerveMap,
      restrictAlong_ofBoundaryNerveMap_coface]
  change (toBoundaryNerveMap (ofBoundaryNerveMap φ)).app _ face =
    φ.app _ face at hface
  change (toBoundaryNerveMap (ofBoundaryNerveMap φ)).app _
      ((SSet.boundary 2).toSSet.map e.τ.op face) =
    φ.app _ ((SSet.boundary 2).toSSet.map e.τ.op face)
  calc
    _ = (CategoryTheory.nerve C).map e.τ.op
        ((toBoundaryNerveMap (ofBoundaryNerveMap φ)).app _ face) := hleft
    _ = (CategoryTheory.nerve C).map e.τ.op (φ.app _ face) := by
      rw [hface]
    _ = _ := hright.symm

/-- Triangular boundary data are exactly simplicial maps from the boundary of
the standard two-simplex into the categorical nerve. -/
def boundaryNerveEquiv :
    TriangleBoundary C ≃
      ((∂Δ[2] : SSet.{max u v}) ⟶ CategoryTheory.nerve C) where
  toFun := toBoundaryNerveMap
  invFun := ofBoundaryNerveMap
  left_inv := ofBoundaryNerveMap_toBoundaryNerveMap
  right_inv := toBoundaryNerveMap_ofBoundaryNerveMap

/-- A triangle boundary is fillable when its long edge is exactly the
composite of its two short edges. -/
def Fillable (Y : TriangleBoundary C) : Prop :=
  Y.edge01 ≫ Y.edge12 = Y.edge02

/-- **Degree-two boundary representation theorem.**  A boundary is in the
strict image of restriction from a composable two-arrow diagram exactly when
its long edge is the composite of its short edges. -/
theorem fillable_iff_exists_extension (Y : TriangleBoundary C) :
    Fillable Y ↔
      ∃ F : ComposableArrows C 2,
        (restrictionFunctor (C := C)).obj F = Y := by
  constructor
  · intro h
    exact ⟨ComposableArrows.mk₂ Y.edge01 Y.edge12,
      ofEdges_comp_eq Y h⟩
  · rintro ⟨F, rfl⟩
    exact (F.map'_comp 0 1 2).symm

/-- Fillability is invariant under boundary isomorphism.  In particular, any
boundary isomorphic to the restriction of a two-simplex is itself strictly
fillable. -/
theorem fillable_of_iso_restriction
    (F : ComposableArrows C 2) (Y : TriangleBoundary C)
    (e : (restrictionFunctor (C := C)).obj F ≅ Y) : Fillable Y := by
  let α0 : F.obj' 0 ≅ Y.vertex0 := isoApp0 e
  let α1 : F.obj' 1 ≅ Y.vertex1 := isoApp1 e
  let α2 : F.obj' 2 ≅ Y.vertex2 := isoApp2 e
  have h01 : F.map' 0 1 ≫ α1.hom = α0.hom ≫ Y.edge01 := by
    exact e.hom.naturality01
  have h12 : F.map' 1 2 ≫ α2.hom = α1.hom ≫ Y.edge12 := by
    exact e.hom.naturality12
  have h02 : F.map' 0 2 ≫ α2.hom = α0.hom ≫ Y.edge02 := by
    exact e.hom.naturality02
  change Y.edge01 ≫ Y.edge12 = Y.edge02
  rw [← cancel_epi α0.hom, ← Category.assoc, ← h01,
    Category.assoc, ← h12, ← Category.assoc,
    ← F.map'_comp 0 1 2, h02]

/-- The degree-two boundary restriction between maximal subgroupoids. -/
def coreRestrictionFunctor :
    Core (ComposableArrows C 2) ⥤ Core (TriangleBoundary C) :=
  (restrictionFunctor (C := C)).core

@[simp]
theorem coreRestrictionFunctor_map_app0
    {X Y : Core (ComposableArrows C 2)} (η : X ⟶ Y) :
    (((coreRestrictionFunctor (C := C)).map η).iso.hom.app0) =
      η.iso.hom.app 0 :=
  rfl

@[simp]
theorem coreRestrictionFunctor_map_app1
    {X Y : Core (ComposableArrows C 2)} (η : X ⟶ Y) :
    (((coreRestrictionFunctor (C := C)).map η).iso.hom.app1) =
      η.iso.hom.app 1 :=
  rfl

@[simp]
theorem coreRestrictionFunctor_map_app2
    {X Y : Core (ComposableArrows C 2)} (η : X ⟶ Y) :
    (((coreRestrictionFunctor (C := C)).map η).iso.hom.app2) =
      η.iso.hom.app 2 :=
  rfl

/-- Components of equality transport between core triangle boundaries. -/
theorem core_eqToHom_app0
    {X Y : Core (TriangleBoundary C)} (h : X = Y) :
    (eqToHom h).iso.hom.app0 =
      eqToHom (congrArg (fun Z => Z.of.vertex0) h) := by
  subst h
  rfl

/-- Components of equality transport between core triangle boundaries. -/
theorem core_eqToHom_app1
    {X Y : Core (TriangleBoundary C)} (h : X = Y) :
    (eqToHom h).iso.hom.app1 =
      eqToHom (congrArg (fun Z => Z.of.vertex1) h) := by
  subst h
  rfl

/-- Components of equality transport between core triangle boundaries. -/
theorem core_eqToHom_app2
    {X Y : Core (TriangleBoundary C)} (h : X = Y) :
    (eqToHom h).iso.hom.app2 =
      eqToHom (congrArg (fun Z => Z.of.vertex2) h) := by
  subst h
  rfl

private theorem coreObj_ext {A : Type*} {X Y : Core A}
    (h : X.of = Y.of) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- The degree-two boundary restriction is a strict isofibration.  An
isomorphism from a fillable boundary forces its target long edge to equal the
composite of the two target short edges; those target edges therefore build
an on-the-nose lifted two-simplex. -/
instance coreRestrictionFunctorIsIsofibration :
    (coreRestrictionFunctor (C := C)).IsIsofibration where
  exists_isoLift {X Y} e := by
    let α0 : X.of.obj' 0 ≅ Y.of.vertex0 := isoApp0 e.hom.iso
    let α1 : X.of.obj' 1 ≅ Y.of.vertex1 := isoApp1 e.hom.iso
    let α2 : X.of.obj' 2 ≅ Y.of.vertex2 := isoApp2 e.hom.iso
    have h01 : X.of.map' 0 1 ≫ α1.hom =
        α0.hom ≫ Y.of.edge01 :=
      by
        have hw := e.hom.iso.hom.naturality01
        change X.of.map' 0 1 ≫ e.hom.iso.hom.app1 =
          e.hom.iso.hom.app0 ≫ Y.of.edge01 at hw
        exact hw
    have h12 : X.of.map' 1 2 ≫ α2.hom =
        α1.hom ≫ Y.of.edge12 :=
      by
        have hw := e.hom.iso.hom.naturality12
        change X.of.map' 1 2 ≫ e.hom.iso.hom.app2 =
          e.hom.iso.hom.app1 ≫ Y.of.edge12 at hw
        exact hw
    have h02 : X.of.map' 0 2 ≫ α2.hom =
        α0.hom ≫ Y.of.edge02 :=
      by
        have hw := e.hom.iso.hom.naturality02
        change X.of.map' 0 2 ≫ e.hom.iso.hom.app2 =
          e.hom.iso.hom.app0 ≫ Y.of.edge02 at hw
        exact hw
    have hFill : Fillable Y.of :=
      fillable_of_iso_restriction X.of Y.of e.hom.iso
    let X' : Core (ComposableArrows C 2) :=
      ⟨ComposableArrows.mk₂ Y.of.edge01 Y.of.edge12⟩
    let η : X ≅ X' := Core.isoMk
      (ComposableArrows.isoMk₂ α0 α1 α2 h01 h12)
    have hOf : ((coreRestrictionFunctor (C := C)).obj X').of = Y.of := by
      exact ofEdges_comp_eq Y.of hFill
    have h : (coreRestrictionFunctor (C := C)).obj X' = Y :=
      coreObj_ext hOf
    exact ⟨{
      obj := X'
      obj_eq := h
      iso := η
      map_iso_hom := by
        apply Core.hom_ext
        apply hom_ext
        · rw [coreRestrictionFunctor_map_app0]
          dsimp [η, α0, isoApp0]
          change e.hom.iso.hom.app0 =
            (e.hom ≫ eqToHom h.symm).iso.hom.app0
          rw [CategoryTheory.coreCategory_comp_iso]
          change e.hom.iso.hom.app0 =
            e.hom.iso.hom.app0 ≫ (eqToHom h.symm).iso.hom.app0
          rw [core_eqToHom_app0]
          rw [show congrArg (fun Z : Core (TriangleBoundary C) =>
              Z.of.vertex0) h.symm = rfl from Subsingleton.elim _ _]
          exact (Category.comp_id _).symm
        · rw [coreRestrictionFunctor_map_app1]
          dsimp [η, α1, isoApp1]
          change e.hom.iso.hom.app1 =
            (e.hom ≫ eqToHom h.symm).iso.hom.app1
          rw [CategoryTheory.coreCategory_comp_iso]
          change e.hom.iso.hom.app1 =
            e.hom.iso.hom.app1 ≫ (eqToHom h.symm).iso.hom.app1
          rw [core_eqToHom_app1]
          rw [show congrArg (fun Z : Core (TriangleBoundary C) =>
              Z.of.vertex1) h.symm = rfl from Subsingleton.elim _ _]
          exact (Category.comp_id _).symm
        · rw [coreRestrictionFunctor_map_app2]
          dsimp [η, α2, isoApp2]
          change e.hom.iso.hom.app2 =
            (e.hom ≫ eqToHom h.symm).iso.hom.app2
          rw [CategoryTheory.coreCategory_comp_iso]
          change e.hom.iso.hom.app2 =
            e.hom.iso.hom.app2 ≫ (eqToHom h.symm).iso.hom.app2
          rw [core_eqToHom_app2]
          rw [show congrArg (fun Z : Core (TriangleBoundary C) =>
              Z.of.vertex2) h.symm = rfl from Subsingleton.elim _ _]
          exact (Category.comp_id _).symm }⟩

/-- The nerve of the degree-two boundary restriction is a Kan fibration. -/
theorem nerveMap_coreRestrictionFunctor_fibration
    (C : Type u) [Category.{v} C] :
    Fibration (CategoryTheory.nerveMap
      (coreRestrictionFunctor (C := C))) :=
  CategoryTheory.Functor.nerveMap_fibration
    (coreRestrictionFunctor (C := C))

end TriangleBoundary

end CategoryTheory
