import Ript.Semantics.Completeness
import Ript.Semantics.MonoidalCompleteness

/-!
# Monoidal interpretations across resource algebras

A single process language can be interpreted by models that measure different
resources.  `ResourceChangingMonoidalInterpretation signature C φ` maps the
`R`-valued declared costs of `signature` into the target model's `S`-valued
costs through an ordered additive homomorphism `φ : R →+o S`.

The bridge is computational: cost translation preserves the wire and
generator types, expressions translate by structural recursion, and
translation has an exact inverse on expressions.  The representation theorem
`equivMappedCostInterpretation` identifies the heterogeneous interface with
an ordinary interpretation of the cost-pushed signature.  Consequently the
existing monoidal soundness and free-model completeness layers apply without
duplicating their proof theory.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

namespace ResourceChangingInterpretation

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [Preorder S]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C S]
variable (φ : R →+o S)

/-- A common sequential syntax interpreted in a process category with a
different native resource algebra. -/
structure Interpretation where
  /-- Interpretation of object symbols. -/
  obj : signature.Obj → C
  /-- Interpretation of primitive processes. -/
  mapGen : {X Y : signature.Obj} → signature.Gen X Y → (obj X ⟶ obj Y)
  /-- Semantic generator cost is bounded by the translated declared cost. -/
  mapGen_cost : ∀ {X Y : signature.Obj} (g : signature.Gen X Y),
    processCost (R := S) (mapGen g) ≤ φ (signature.cost g)

/-- Regard a heterogeneous sequential interpretation as an ordinary
interpretation of the cost-pushed signature. -/
def toMappedCost
    (interpretation : Interpretation (signature := signature) (C := C) φ) :
    Ript.Semantics.Interpretation (signature.mapCost φ) C where
  obj := interpretation.obj
  mapGen := interpretation.mapGen
  mapGen_cost := interpretation.mapGen_cost

/-- Recover a heterogeneous sequential interpretation from an ordinary
interpretation of the cost-pushed signature. -/
def ofMappedCost
    (interpretation : Ript.Semantics.Interpretation (signature.mapCost φ) C) :
    Interpretation (signature := signature) (C := C) φ where
  obj := interpretation.obj
  mapGen := interpretation.mapGen
  mapGen_cost := interpretation.mapGen_cost

/-- **Sequential heterogeneous-interpretation representation theorem.** -/
def equivMappedCostInterpretation :
    Interpretation (signature := signature) (C := C) φ ≃
      Ript.Semantics.Interpretation (signature.mapCost φ) C where
  toFun := toMappedCost φ
  invFun := ofMappedCost φ
  left_inv interpretation := by cases interpretation; rfl
  right_inv interpretation := by cases interpretation; rfl

end ResourceChangingInterpretation

namespace ResourceChangingMonoidalInterpretation

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [Preorder S]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C]
variable [HasProcessCost C S]
variable (φ : R →+o S)

/-- A common `R`-costed syntax interpreted in an `S`-costed process model.
The resource map is explicit, so distinct models need not collapse their
native resource algebras to a shared scalar. -/
structure Interpretation where
  /-- Interpretation of primitive wires. -/
  wire : signature.Wire → C
  /-- Interpretation of primitive processes. -/
  mapGen : {X Y : signature.Obj} → signature.Gen X Y →
    (monoidalObjEval wire X ⟶ monoidalObjEval wire Y)
  /-- Target generator cost is bounded by the translated declared cost. -/
  mapGen_cost : ∀ {X Y : signature.Obj} (g : signature.Gen X Y),
    processCost (R := S) (mapGen g) ≤ φ (signature.cost g)

/-- Regard a heterogeneous interpretation as an ordinary interpretation after
pushing the syntax costs into the target resource algebra. -/
def toMappedCost
    (interpretation : Interpretation (signature := signature) (C := C) φ) :
    MonoidalInterpretation (signature.mapCost φ) C where
  wire := interpretation.wire
  mapGen := interpretation.mapGen
  mapGen_cost := interpretation.mapGen_cost

/-- Recover the heterogeneous interface from an ordinary interpretation of
the cost-pushed signature. -/
def ofMappedCost
    (interpretation : MonoidalInterpretation (signature.mapCost φ) C) :
    Interpretation (signature := signature) (C := C) φ where
  wire := interpretation.wire
  mapGen := interpretation.mapGen
  mapGen_cost := interpretation.mapGen_cost

/-- **Heterogeneous interpretation representation theorem.** Interpreting a
common syntax along `φ` is exactly the same data as first pushing its declared
costs along `φ` and then giving an ordinary monoidal interpretation. -/
def equivMappedCostInterpretation :
    Interpretation (signature := signature) (C := C) φ ≃
      MonoidalInterpretation (signature.mapCost φ) C where
  toFun := toMappedCost φ
  invFun := ofMappedCost φ
  left_inv interpretation := by cases interpretation; rfl
  right_inv interpretation := by cases interpretation; rfl

end ResourceChangingMonoidalInterpretation

end Ript.Semantics

namespace Ript.Syntax

universe u w

namespace Expr

variable {R S : Type w} [AddCommMonoid R] [Preorder R]
variable [AddCommMonoid S] [Preorder S]
variable {signature : Signature.{u, w} R}

/-- Translate a sequential expression to a new resource algebra while
preserving its complete process tree. -/
def mapCost (φ : R →+o S) {X Y : signature.Obj}
    (expression : Expr signature X Y) : Expr (signature.mapCost φ) X Y :=
  match expression with
  | .gen g => .gen g
  | .id X => .id (signature := signature.mapCost φ) X
  | .comp f g => .comp (mapCost φ f) (mapCost φ g)

/-- Forget a sequential cost translation. -/
def unmapCost (φ : R →+o S) {X Y : (signature.mapCost φ).Obj}
    (expression : Expr (signature.mapCost φ) X Y) : Expr signature X Y :=
  match expression with
  | .gen g => .gen g
  | .id X => .id (signature := signature) X
  | .comp f g => .comp (unmapCost φ f) (unmapCost φ g)

@[simp]
theorem unmapCost_mapCost (φ : R →+o S) {X Y : signature.Obj}
    (expression : Expr signature X Y) :
    unmapCost φ (mapCost φ expression) = expression := by
  induction expression <;> simp_all [mapCost, unmapCost]

@[simp]
theorem mapCost_unmapCost (φ : R →+o S)
    {X Y : (signature.mapCost φ).Obj}
    (expression : Expr (signature.mapCost φ) X Y) :
    mapCost φ (unmapCost φ expression) = expression := by
  induction expression <;> simp_all [mapCost, unmapCost]

/-- Sequential expressions before and after resource translation are
computably equivalent. -/
def mapCostEquiv (φ : R →+o S) (X Y : signature.Obj) :
    Expr signature X Y ≃ Expr (signature.mapCost φ) X Y where
  toFun := mapCost φ
  invFun := unmapCost φ
  left_inv := unmapCost_mapCost φ
  right_inv := mapCost_unmapCost φ

/-- Sequential syntax cost commutes exactly with resource translation. -/
@[simp]
theorem syntaxCost_mapCost (φ : R →+o S) {X Y : signature.Obj}
    (expression : Expr signature X Y) :
    (mapCost φ expression).syntaxCost = φ expression.syntaxCost := by
  induction expression <;> simp_all [mapCost, Expr.syntaxCost]
  all_goals rfl

end Expr

namespace Derives

variable {R S : Type w} [AddCommMonoid R] [Preorder R]
variable [AddCommMonoid S] [Preorder S]
variable {signature : Signature.{u, w} R}

/-- Resource translation preserves every formal sequential derivation. -/
theorem mapCost (φ : R →+o S) {X Y : signature.Obj}
    {f g : Expr signature X Y} (derivation : Derives f g) :
    Derives (Expr.mapCost φ f) (Expr.mapCost φ g) := by
  induction derivation with
  | refl f => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | comp_congr _ _ ih₁ ih₂ => exact .comp_congr ih₁ ih₂
  | id_comp f => exact .id_comp (Expr.mapCost φ f)
  | comp_id f => exact .comp_id (Expr.mapCost φ f)
  | assoc f g h =>
      simpa [Expr.mapCost] using
        (Derives.assoc (Expr.mapCost φ f) (Expr.mapCost φ g)
          (Expr.mapCost φ h))

/-- Forgetting a resource translation preserves every formal derivation. -/
theorem unmapCost (φ : R →+o S)
    {X Y : (signature.mapCost φ).Obj}
    {f g : Expr (signature.mapCost φ) X Y} (derivation : Derives f g) :
    Derives (Expr.unmapCost φ f) (Expr.unmapCost φ g) := by
  induction derivation with
  | refl f => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | comp_congr _ _ ih₁ ih₂ => exact .comp_congr ih₁ ih₂
  | id_comp f => exact .id_comp (Expr.unmapCost φ f)
  | comp_id f => exact .comp_id (Expr.unmapCost φ f)
  | assoc f g h =>
      simpa [Expr.unmapCost] using
        (Derives.assoc (Expr.unmapCost φ f) (Expr.unmapCost φ g)
          (Expr.unmapCost φ h))

/-- **Proof-theoretic conservativity of resource translation.** Two original
expressions are formally equal exactly when their cost-translated expressions
are formally equal. -/
theorem mapCost_iff (φ : R →+o S) {X Y : signature.Obj}
    {f g : Expr signature X Y} :
    Derives (Expr.mapCost φ f) (Expr.mapCost φ g) ↔ Derives f g := by
  constructor
  · intro derivation
    simpa using derivation.unmapCost φ
  · exact fun derivation ↦ derivation.mapCost φ

end Derives

namespace MonoidalExpr

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [Preorder S]
variable {signature : MonoidalSignature.{u, w} R}

/-- Translate an expression to a new resource algebra without changing any
wire, generator, or process constructor. -/
def mapCost (φ : R →+o S) {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    MonoidalExpr (signature.mapCost φ) X Y :=
  match expression with
  | .gen g => .gen g
  | .id X => .id (signature := signature.mapCost φ) X
  | .comp f g => .comp (mapCost φ f) (mapCost φ g)
  | .tensor f g => .tensor (mapCost φ f) (mapCost φ g)
  | .associator X Y Z =>
      .associator (signature := signature.mapCost φ) X Y Z
  | .associatorInv X Y Z =>
      .associatorInv (signature := signature.mapCost φ) X Y Z
  | .leftUnitor X => .leftUnitor (signature := signature.mapCost φ) X
  | .leftUnitorInv X => .leftUnitorInv (signature := signature.mapCost φ) X
  | .rightUnitor X => .rightUnitor (signature := signature.mapCost φ) X
  | .rightUnitorInv X => .rightUnitorInv (signature := signature.mapCost φ) X
  | .braid X Y => .braid (signature := signature.mapCost φ) X Y

/-- Forget a cost translation.  This is possible because `mapCost` changes
only the cost annotation, not the process language. -/
def unmapCost (φ : R →+o S) {X Y : (signature.mapCost φ).Obj}
    (expression : MonoidalExpr (signature.mapCost φ) X Y) :
    MonoidalExpr signature X Y :=
  match expression with
  | .gen g => .gen g
  | .id X => .id (signature := signature) X
  | .comp f g => .comp (unmapCost φ f) (unmapCost φ g)
  | .tensor f g => .tensor (unmapCost φ f) (unmapCost φ g)
  | .associator X Y Z => .associator (signature := signature) X Y Z
  | .associatorInv X Y Z => .associatorInv (signature := signature) X Y Z
  | .leftUnitor X => .leftUnitor (signature := signature) X
  | .leftUnitorInv X => .leftUnitorInv (signature := signature) X
  | .rightUnitor X => .rightUnitor (signature := signature) X
  | .rightUnitorInv X => .rightUnitorInv (signature := signature) X
  | .braid X Y => .braid (signature := signature) X Y

/-- Translating and then forgetting resource costs returns the exact original
expression. -/
@[simp]
theorem unmapCost_mapCost (φ : R →+o S) {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    unmapCost φ (mapCost φ expression) = expression := by
  induction expression <;> simp_all [mapCost, unmapCost]

/-- Forgetting and retranslating returns the exact cost-pushed expression. -/
@[simp]
theorem mapCost_unmapCost (φ : R →+o S)
    {X Y : (signature.mapCost φ).Obj}
    (expression : MonoidalExpr (signature.mapCost φ) X Y) :
    mapCost φ (unmapCost φ expression) = expression := by
  induction expression <;> simp_all [mapCost, unmapCost]

/-- Expression translation is a computable equivalence of the typed process
languages before and after resource change. -/
def mapCostEquiv (φ : R →+o S) (X Y : signature.Obj) :
    MonoidalExpr signature X Y ≃
      MonoidalExpr (signature.mapCost φ) X Y where
  toFun := mapCost φ
  invFun := unmapCost φ
  left_inv := unmapCost_mapCost φ
  right_inv := mapCost_unmapCost φ

/-- Computed syntax cost commutes exactly with ordered additive resource
translation. -/
@[simp]
theorem syntaxCost_mapCost (φ : R →+o S) {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    (mapCost φ expression).syntaxCost = φ expression.syntaxCost := by
  induction expression <;>
    simp_all [mapCost, MonoidalExpr.syntaxCost]
  all_goals rfl

end MonoidalExpr

namespace MonoidalDerives

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [Preorder S]
variable {signature : MonoidalSignature.{u, w} R}

set_option backward.isDefEq.respectTransparency false in
/-- Resource translation preserves every formal symmetric monoidal
derivation, including coherence and braiding laws. -/
theorem mapCost (φ : R →+o S) {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y} (derivation : MonoidalDerives f g) :
    MonoidalDerives (MonoidalExpr.mapCost φ f)
      (MonoidalExpr.mapCost φ g) := by
  induction derivation with
  | refl f => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | comp_congr _ _ ih₁ ih₂ => exact .comp_congr ih₁ ih₂
  | tensor_congr _ _ ih₁ ih₂ => exact .tensor_congr ih₁ ih₂
  | id_comp f => exact .id_comp (MonoidalExpr.mapCost φ f)
  | comp_id f => exact .comp_id (MonoidalExpr.mapCost φ f)
  | assoc f g h =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.assoc (MonoidalExpr.mapCost φ f)
          (MonoidalExpr.mapCost φ g) (MonoidalExpr.mapCost φ h))
  | tensor_id X Y =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.tensor_id (signature := signature.mapCost φ) X Y)
  | interchange f₁ f₂ g₁ g₂ =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.interchange (MonoidalExpr.mapCost φ f₁)
          (MonoidalExpr.mapCost φ f₂) (MonoidalExpr.mapCost φ g₁)
          (MonoidalExpr.mapCost φ g₂))
  | associator_hom_inv X Y Z =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.associator_hom_inv
          (signature := signature.mapCost φ) X Y Z)
  | associator_inv_hom X Y Z =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.associator_inv_hom
          (signature := signature.mapCost φ) X Y Z)
  | leftUnitor_hom_inv X =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.leftUnitor_hom_inv
          (signature := signature.mapCost φ) X)
  | leftUnitor_inv_hom X =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.leftUnitor_inv_hom
          (signature := signature.mapCost φ) X)
  | rightUnitor_hom_inv X =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.rightUnitor_hom_inv
          (signature := signature.mapCost φ) X)
  | rightUnitor_inv_hom X =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.rightUnitor_inv_hom
          (signature := signature.mapCost φ) X)
  | associator_naturality f₁ f₂ f₃ =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.associator_naturality
          (MonoidalExpr.mapCost φ f₁) (MonoidalExpr.mapCost φ f₂)
          (MonoidalExpr.mapCost φ f₃))
  | leftUnitor_naturality f =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.leftUnitor_naturality
          (MonoidalExpr.mapCost φ f))
  | rightUnitor_naturality f =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.rightUnitor_naturality
          (MonoidalExpr.mapCost φ f))
  | pentagon W X Y Z =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.pentagon (signature := signature.mapCost φ) W X Y Z)
  | triangle X Y =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.triangle (signature := signature.mapCost φ) X Y)
  | braid_symmetry X Y =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_symmetry
          (signature := signature.mapCost φ) X Y)
  | braid_naturality f g =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_naturality (MonoidalExpr.mapCost φ f)
          (MonoidalExpr.mapCost φ g))
  | braid_naturality_right X f =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_naturality_right X
          (signature := signature.mapCost φ) (MonoidalExpr.mapCost φ f))
  | braid_naturality_left f Z =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_naturality_left
          (MonoidalExpr.mapCost φ f) Z)
  | hexagon_forward X Y Z =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.hexagon_forward
          (signature := signature.mapCost φ) X Y Z)
  | hexagon_reverse X Y Z =>
      simpa [MonoidalExpr.mapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.hexagon_reverse
          (signature := signature.mapCost φ) X Y Z)

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting a resource translation also preserves every formal symmetric
monoidal derivation. -/
theorem unmapCost (φ : R →+o S)
    {X Y : (signature.mapCost φ).Obj}
    {f g : MonoidalExpr (signature.mapCost φ) X Y}
    (derivation : MonoidalDerives f g) :
    MonoidalDerives (MonoidalExpr.unmapCost φ f)
      (MonoidalExpr.unmapCost φ g) := by
  induction derivation with
  | refl f => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | comp_congr _ _ ih₁ ih₂ => exact .comp_congr ih₁ ih₂
  | tensor_congr _ _ ih₁ ih₂ => exact .tensor_congr ih₁ ih₂
  | id_comp f => exact .id_comp (MonoidalExpr.unmapCost φ f)
  | comp_id f => exact .comp_id (MonoidalExpr.unmapCost φ f)
  | assoc f g h =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.assoc (MonoidalExpr.unmapCost φ f)
          (MonoidalExpr.unmapCost φ g) (MonoidalExpr.unmapCost φ h))
  | tensor_id X Y =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.tensor_id (signature := signature) X Y)
  | interchange f₁ f₂ g₁ g₂ =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.interchange (MonoidalExpr.unmapCost φ f₁)
          (MonoidalExpr.unmapCost φ f₂) (MonoidalExpr.unmapCost φ g₁)
          (MonoidalExpr.unmapCost φ g₂))
  | associator_hom_inv X Y Z =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.associator_hom_inv (signature := signature) X Y Z)
  | associator_inv_hom X Y Z =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.associator_inv_hom (signature := signature) X Y Z)
  | leftUnitor_hom_inv X =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.leftUnitor_hom_inv (signature := signature) X)
  | leftUnitor_inv_hom X =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.leftUnitor_inv_hom (signature := signature) X)
  | rightUnitor_hom_inv X =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.rightUnitor_hom_inv (signature := signature) X)
  | rightUnitor_inv_hom X =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.rightUnitor_inv_hom (signature := signature) X)
  | associator_naturality f₁ f₂ f₃ =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.associator_naturality
          (MonoidalExpr.unmapCost φ f₁) (MonoidalExpr.unmapCost φ f₂)
          (MonoidalExpr.unmapCost φ f₃))
  | leftUnitor_naturality f =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.leftUnitor_naturality
          (MonoidalExpr.unmapCost φ f))
  | rightUnitor_naturality f =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.rightUnitor_naturality
          (MonoidalExpr.unmapCost φ f))
  | pentagon W X Y Z =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.pentagon (signature := signature) W X Y Z)
  | triangle X Y =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.triangle (signature := signature) X Y)
  | braid_symmetry X Y =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_symmetry (signature := signature) X Y)
  | braid_naturality f g =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_naturality (MonoidalExpr.unmapCost φ f)
          (MonoidalExpr.unmapCost φ g))
  | braid_naturality_right X f =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_naturality_right X
          (signature := signature) (MonoidalExpr.unmapCost φ f))
  | braid_naturality_left f Z =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.braid_naturality_left
          (MonoidalExpr.unmapCost φ f) Z)
  | hexagon_forward X Y Z =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.hexagon_forward (signature := signature) X Y Z)
  | hexagon_reverse X Y Z =>
      simpa [MonoidalExpr.unmapCost, MonoidalSignature.mapCost] using
        (MonoidalDerives.hexagon_reverse (signature := signature) X Y Z)

/-- **Monoidal proof-theoretic conservativity of resource translation.** -/
theorem mapCost_iff (φ : R →+o S) {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y} :
    MonoidalDerives (MonoidalExpr.mapCost φ f)
        (MonoidalExpr.mapCost φ g) ↔
      MonoidalDerives f g := by
  constructor
  · intro derivation
    simpa using derivation.unmapCost φ
  · exact fun derivation ↦ derivation.mapCost φ

end MonoidalDerives

end Ript.Syntax

namespace Ript.Semantics

open CategoryTheory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

namespace ResourceChangingInterpretation

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [PartialOrder S]
variable [ResourceAlgebra S]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C S]
variable {φ : R →+o S}

/-- Evaluate a common sequential expression in a category with a different
native resource algebra. -/
def eval (interpretation : Interpretation (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (expression : Expr signature X Y) :
    interpretation.obj X ⟶ interpretation.obj Y :=
  Ript.Semantics.eval (toMappedCost φ interpretation)
    (Expr.mapCost φ expression)

/-- Resource-changing sequential evaluation is bounded by the translated
computable syntax cost. -/
theorem eval_cost_le
    (interpretation : Interpretation (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (expression : Expr signature X Y) :
    processCost (R := S) (eval interpretation expression) ≤
      φ expression.syntaxCost := by
  change processCost (R := S)
      (Ript.Semantics.eval (toMappedCost φ interpretation)
        (Expr.mapCost φ expression)) ≤ _
  rw [← Expr.syntaxCost_mapCost φ expression]
  exact Ript.Semantics.eval_cost_le (toMappedCost φ interpretation)
    (Expr.mapCost φ expression)

omit [ResourceAlgebra S] in
/-- Every heterogeneous sequential interpretation respects the original
formal equational theory. -/
theorem soundness
    (interpretation : Interpretation (signature := signature) (C := C) φ)
    {X Y : signature.Obj} {f g : Expr signature X Y}
    (derivation : Derives f g) :
    eval interpretation f = eval interpretation g :=
  Ript.Semantics.soundness (toMappedCost φ interpretation)
    (derivation.mapCost φ)

end ResourceChangingInterpretation

namespace ResourceChangingInterpretation

variable {R S : Type w} [AddCommMonoid R] [Preorder R]
variable [AddCommMonoid S] [PartialOrder S]
variable {signature : Signature.{u, w} R}
variable (φ : R →+o S)

/-- Relative completeness of the sequential common language after resource
translation. -/
theorem mapped_soundness_iff_term_model {X Y : signature.Obj}
    {f g : Expr signature X Y} :
    Derives (Expr.mapCost φ f) (Expr.mapCost φ g) ↔
      Ript.Semantics.eval
          (TermModel.interpretation (signature.mapCost φ))
          (Expr.mapCost φ f) =
        Ript.Semantics.eval
          (TermModel.interpretation (signature.mapCost φ))
          (Expr.mapCost φ g) :=
  soundness_iff_term_model

/-- The translated sequential free model realizes exactly the translated
computed syntax cost. -/
theorem mapped_budget_complete_in_free_model {X Y : signature.Obj}
    (expression : Expr signature X Y) :
    processCost (R := S)
        (Ript.Semantics.eval
          (TermModel.interpretation (signature.mapCost φ))
          (Expr.mapCost φ expression)) =
      φ expression.syntaxCost := by
  calc
    processCost (R := S)
        (Ript.Semantics.eval
          (TermModel.interpretation (signature.mapCost φ))
          (Expr.mapCost φ expression)) =
        (Expr.mapCost φ expression).syntaxCost :=
      budget_complete_in_free_model
        (signature := signature.mapCost φ) (Expr.mapCost φ expression)
    _ = φ expression.syntaxCost := Expr.syntaxCost_mapCost φ expression

end ResourceChangingInterpretation

namespace ResourceChangingMonoidalInterpretation

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {S : Type w} [AddCommMonoid S] [PartialOrder S]
variable [ResourceAlgebra S]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C]
variable [SymmetricCategory C] [HasProcessCost C S]
variable [HasParallelProcessCost C S] [HasFreeStructuralCost C S]
variable {φ : R →+o S}

/-- Evaluate a common-syntax expression in a model with a different resource
algebra.  The executable process tree is preserved by `MonoidalExpr.mapCost`.
-/
def eval (interpretation : Interpretation (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    monoidalObjEval interpretation.wire X ⟶
      monoidalObjEval interpretation.wire Y :=
  monoidalEval (toMappedCost φ interpretation)
    (MonoidalExpr.mapCost φ expression)

/-- Resource-changing evaluation is bounded by the translated, computable
syntax cost. -/
theorem eval_cost_le
    (interpretation : Interpretation (signature := signature) (C := C) φ)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    processCost (R := S) (eval interpretation expression) ≤
      φ expression.syntaxCost := by
  change processCost (R := S)
      (monoidalEval (toMappedCost φ interpretation)
        (MonoidalExpr.mapCost φ expression)) ≤ _
  rw [← MonoidalExpr.syntaxCost_mapCost φ expression]
  exact monoidalEval_cost_le (toMappedCost φ interpretation)
    (MonoidalExpr.mapCost φ expression)

omit [ResourceAlgebra S] [HasParallelProcessCost C S]
  [HasFreeStructuralCost C S] in
/-- Every heterogeneous symmetric monoidal interpretation respects the
original formal equational theory before resource translation. -/
theorem soundness
    (interpretation : Interpretation (signature := signature) (C := C) φ)
    {X Y : signature.Obj} {f g : MonoidalExpr signature X Y}
    (derivation : MonoidalDerives f g) :
    eval interpretation f = eval interpretation g :=
  monoidal_soundness (toMappedCost φ interpretation)
    (derivation.mapCost φ)

end ResourceChangingMonoidalInterpretation

namespace ResourceChangingMonoidalInterpretation

variable {R S : Type w} [AddCommMonoid R] [Preorder R]
variable [AddCommMonoid S] [Preorder S]
variable {signature : MonoidalSignature.{u, w} R}
variable (φ : R →+o S)

/-- **Relative completeness after resource change.** Formal derivability in
the translated common language is exactly equality in its canonical free
symmetric monoidal term model. -/
theorem mapped_soundness_iff_term_model {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y} :
    MonoidalDerives (MonoidalExpr.mapCost φ f) (MonoidalExpr.mapCost φ g) ↔
      monoidalEval
          (MonoidalTermModel.interpretation (signature.mapCost φ))
          (MonoidalExpr.mapCost φ f) =
        monoidalEval
          (MonoidalTermModel.interpretation (signature.mapCost φ))
          (MonoidalExpr.mapCost φ g) :=
  monoidal_soundness_iff_term_model

/-- **Exact budget representation after resource change.** The free model of
the translated common language realizes exactly the translated computable
syntax cost, not merely an upper bound. -/
theorem mapped_budget_complete_in_free_model {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    processCost (R := S)
        (monoidalEval
          (MonoidalTermModel.interpretation (signature.mapCost φ))
          (MonoidalExpr.mapCost φ expression)) =
      φ expression.syntaxCost := by
  calc
    processCost (R := S)
        (monoidalEval
          (MonoidalTermModel.interpretation (signature.mapCost φ))
          (MonoidalExpr.mapCost φ expression)) =
        (MonoidalExpr.mapCost φ expression).syntaxCost :=
      monoidal_budget_complete_in_free_model
        (signature := signature.mapCost φ)
        (MonoidalExpr.mapCost φ expression)
    _ = φ expression.syntaxCost :=
      MonoidalExpr.syntaxCost_mapCost φ expression

end ResourceChangingMonoidalInterpretation

end Ript.Semantics
