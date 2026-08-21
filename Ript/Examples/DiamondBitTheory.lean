import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Semantics.ResourceChangingInterpretation

/-!
# A non-thin common process theory

The diamond theory has two parallel paths from input to output:

* a reversible path with two flips;
* an irreversible path that exposes and then erases information.

Four independent resource coordinates distinguish the primitive operations.
Unlike the earlier linear theory, normalization retains two genuinely
different canonical paths.  Semantic completeness therefore requires an
interpretation to separate their denotations.
-/

set_option autoImplicit false

namespace Ript.Examples.DiamondBitTheory

open CategoryTheory
open Ript.Core
open Ript.Semantics
open Ript.Syntax

universe u v

/-! ## Signature and resources -/

/-- One coordinate for each primitive edge of the diamond. -/
abbrev ResourceKind := Fin 4

namespace ResourceKind

/-- Resource coordinate of the first reversible edge. -/
def reversibleFirst : ResourceKind := 0

/-- Resource coordinate of the second reversible edge. -/
def reversibleSecond : ResourceKind := 1

/-- Resource coordinate of the exposure edge. -/
def exposure : ResourceKind := 2

/-- Resource coordinate of the erasure edge. -/
def erasure : ResourceKind := 3

end ResourceKind

/-- Four-coordinate resource algebra of the diamond theory. -/
abbrev Resource := ResourceKind → Nat

/-- Construct a diamond resource vector. -/
def Resource.of (reversibleFirst reversibleSecond exposure erasure : Nat) :
    Resource :=
  ![reversibleFirst, reversibleSecond, exposure, erasure]

/-- Four interfaces forming a directed diamond. -/
inductive Interface where
  | input
  | reversible
  | irreversible
  | output
  deriving DecidableEq, Repr

/-- Four primitive edges of the diamond. -/
inductive Generator : Interface → Interface → Type where
  | reversibleFirst : Generator .input .reversible
  | reversibleSecond : Generator .reversible .output
  | expose : Generator .input .irreversible
  | erase : Generator .irreversible .output

/-- Each generator occupies its own exact resource coordinate. -/
def signature : Signature Resource where
  Obj := Interface
  Gen := Generator
  cost
    | .reversibleFirst => Resource.of 1 0 0 0
    | .reversibleSecond => Resource.of 0 1 0 0
    | .expose => Resource.of 0 0 1 0
    | .erase => Resource.of 0 0 0 1

/-- Reversible input-to-output path. -/
def reversiblePath : Expr signature .input .output :=
  .comp (.gen .reversibleFirst) (.gen .reversibleSecond)

/-- Irreversible input-to-output path. -/
def erasurePath : Expr signature .input .output :=
  .comp (.gen .expose) (.gen .erase)

@[simp]
theorem reversiblePath_cost :
    reversiblePath.syntaxCost = Resource.of 1 1 0 0 := by
  funext kind
  fin_cases kind <;> rfl

@[simp]
theorem erasurePath_cost :
    erasurePath.syntaxCost = Resource.of 0 0 1 1 := by
  funext kind
  fin_cases kind <;> rfl

/-- The two paths cannot be formally equated because derivations preserve the
independent resource coordinates. -/
theorem reversiblePath_not_derives_erasurePath :
    ¬ Derives reversiblePath erasurePath := by
  intro derivation
  have hcost := derivation.syntaxCost_eq
  have hfirst := congrFun hcost ResourceKind.reversibleFirst
  norm_num [ResourceKind.reversibleFirst, Resource.of] at hfirst

/-! ## Canonical paths and normalization -/

/-- The ten canonical paths of the free diamond category. -/
inductive Canonical : Interface → Interface → Type where
  | inputId : Canonical .input .input
  | reversibleId : Canonical .reversible .reversible
  | irreversibleId : Canonical .irreversible .irreversible
  | outputId : Canonical .output .output
  | reversibleFirst : Canonical .input .reversible
  | reversibleSecond : Canonical .reversible .output
  | expose : Canonical .input .irreversible
  | erase : Canonical .irreversible .output
  | reversiblePath : Canonical .input .output
  | erasurePath : Canonical .input .output
  deriving DecidableEq

namespace Canonical

/-- Reify a canonical path as syntax. -/
def toExpr : {X Y : Interface} → Canonical X Y → Expr signature X Y
  | _, _, .inputId => .id (signature := signature) Interface.input
  | _, _, .reversibleId => .id (signature := signature) Interface.reversible
  | _, _, .irreversibleId => .id (signature := signature) Interface.irreversible
  | _, _, .outputId => .id (signature := signature) Interface.output
  | _, _, .reversibleFirst => .gen .reversibleFirst
  | _, _, .reversibleSecond => .gen .reversibleSecond
  | _, _, .expose => .gen .expose
  | _, _, .erase => .gen .erase
  | _, _, .reversiblePath => DiamondBitTheory.reversiblePath
  | _, _, .erasurePath => DiamondBitTheory.erasurePath

/-- Composition of canonical diamond paths. -/
def comp {X Y Z : Interface} :
    Canonical X Y → Canonical Y Z → Canonical X Z
  | .inputId, .inputId => .inputId
  | .inputId, .reversibleFirst => .reversibleFirst
  | .inputId, .expose => .expose
  | .inputId, .reversiblePath => .reversiblePath
  | .inputId, .erasurePath => .erasurePath
  | .reversibleId, .reversibleId => .reversibleId
  | .reversibleId, .reversibleSecond => .reversibleSecond
  | .irreversibleId, .irreversibleId => .irreversibleId
  | .irreversibleId, .erase => .erase
  | .outputId, .outputId => .outputId
  | .reversibleFirst, .reversibleId => .reversibleFirst
  | .reversibleFirst, .reversibleSecond => .reversiblePath
  | .expose, .irreversibleId => .expose
  | .expose, .erase => .erasurePath
  | .reversibleSecond, .outputId => .reversibleSecond
  | .erase, .outputId => .erase
  | .reversiblePath, .outputId => .reversiblePath
  | .erasurePath, .outputId => .erasurePath

/-- Syntactic composition derives to canonical composition. -/
theorem comp_derives {X Y Z : Interface}
    (left : Canonical X Y) (right : Canonical Y Z) :
    Derives (.comp left.toExpr right.toExpr) (left.comp right).toExpr := by
  cases left <;> cases right
  all_goals first
    | simpa [toExpr, comp] using
        (Derives.id_comp (Expr.id (signature := signature) Interface.input))
    | simpa [toExpr, comp] using
        (Derives.id_comp
          (Expr.gen (signature := signature) Generator.reversibleFirst))
    | simpa [toExpr, comp] using
        (Derives.id_comp (Expr.gen (signature := signature) Generator.expose))
    | simpa [toExpr, comp] using
        (Derives.id_comp DiamondBitTheory.reversiblePath)
    | simpa [toExpr, comp] using
        (Derives.id_comp DiamondBitTheory.erasurePath)
    | simpa [toExpr, comp] using
        (Derives.id_comp
          (Expr.id (signature := signature) Interface.reversible))
    | simpa [toExpr, comp] using
        (Derives.id_comp
          (Expr.gen (signature := signature) Generator.reversibleSecond))
    | simpa [toExpr, comp] using
        (Derives.id_comp
          (Expr.id (signature := signature) Interface.irreversible))
    | simpa [toExpr, comp] using
        (Derives.id_comp (Expr.gen (signature := signature) Generator.erase))
    | simpa [toExpr, comp] using
        (Derives.id_comp (Expr.id (signature := signature) Interface.output))
    | simpa [toExpr, comp] using
        (Derives.comp_id
          (Expr.gen (signature := signature) Generator.reversibleFirst))
    | exact .refl _
    | simpa [toExpr, comp] using
        (Derives.comp_id (Expr.gen (signature := signature) Generator.expose))
    | exact .refl _
    | simpa [toExpr, comp] using
        (Derives.comp_id
          (Expr.gen (signature := signature) Generator.reversibleSecond))
    | simpa [toExpr, comp] using
        (Derives.comp_id (Expr.gen (signature := signature) Generator.erase))
    | simpa [toExpr, comp] using
        (Derives.comp_id DiamondBitTheory.reversiblePath)
    | simpa [toExpr, comp] using
        (Derives.comp_id DiamondBitTheory.erasurePath)

end Canonical

/-- Compute a canonical representative while retaining the two parallel
input-to-output paths. -/
def normalize {X Y : Interface} : Expr signature X Y → Canonical X Y
  | .gen .reversibleFirst => .reversibleFirst
  | .gen .reversibleSecond => .reversibleSecond
  | .gen .expose => .expose
  | .gen .erase => .erase
  | .id X => match X with
    | Interface.input => .inputId
    | Interface.reversible => .reversibleId
    | Interface.irreversible => .irreversibleId
    | Interface.output => .outputId
  | .comp left right => (normalize left).comp (normalize right)

/-- Every expression derives to its computed canonical path. -/
theorem normalize_derives {X Y : Interface} (expression : Expr signature X Y) :
    Derives expression (normalize expression).toExpr :=
  match expression with
  | .gen .reversibleFirst => .refl _
  | .gen .reversibleSecond => .refl _
  | .gen .expose => .refl _
  | .gen .erase => .refl _
  | .id Interface.input => .refl _
  | .id Interface.reversible => .refl _
  | .id Interface.irreversible => .refl _
  | .id Interface.output => .refl _
  | .comp left right =>
      (Derives.comp_congr (normalize_derives left)
        (normalize_derives right)).trans
          (Canonical.comp_derives (normalize left) (normalize right))

/-- Derivability is exactly equality of computed canonical paths. -/
theorem derives_iff_normalize_eq {X Y : Interface}
    (left right : Expr signature X Y) :
    Derives left right ↔ normalize left = normalize right := by
  constructor
  · intro derivation
    have hcost := derivation.syntaxCost_eq
    have hleftCost := (normalize_derives left).syntaxCost_eq
    have hrightCost := (normalize_derives right).syntaxCost_eq
    have hcanonicalCost :
        (normalize left).toExpr.syntaxCost =
          (normalize right).toExpr.syntaxCost :=
      hleftCost.symm.trans (hcost.trans hrightCost)
    generalize hleft : normalize left = leftCanonical at *
    generalize hright : normalize right = rightCanonical at *
    cases leftCanonical <;> cases rightCanonical
    all_goals try rfl
    · exfalso
      have hcoordinate := congrFun hcanonicalCost
        ResourceKind.reversibleFirst
      change (1 : Nat) = 0 at hcoordinate
      exact Nat.one_ne_zero hcoordinate
    · exfalso
      have hcoordinate := congrFun hcanonicalCost
        ResourceKind.reversibleFirst
      change (0 : Nat) = 1 at hcoordinate
      exact Nat.zero_ne_one hcoordinate
  · intro equality
    have hright := normalize_derives right
    rw [← equality] at hright
    exact (normalize_derives left).trans hright.symm

/-! ## Exact image and conditional completeness -/

/-- Semantic morphisms represented by diamond expressions. -/
def InImage {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : Interface} (morphism : interpretation.obj X ⟶ interpretation.obj Y) :
    Prop :=
  ∃ expression : Expr signature X Y,
    ResourceChangingInterpretation.eval interpretation expression = morphism

/-- Exact image representation by canonical diamond paths. -/
theorem inImage_iff_exists_canonical
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    {X Y : Interface} (morphism : interpretation.obj X ⟶ interpretation.obj Y) :
    InImage interpretation morphism ↔
      ∃ canonical : Canonical X Y,
        morphism = ResourceChangingInterpretation.eval interpretation
          canonical.toExpr := by
  constructor
  · rintro ⟨expression, rfl⟩
    exact ⟨normalize expression,
      ResourceChangingInterpretation.soundness interpretation
        (normalize_derives expression)⟩
  · rintro ⟨canonical, equality⟩
    exact ⟨canonical.toExpr, equality.symm⟩

/-- The input-to-output image is exactly the union of the two competing path
denotations. -/
theorem inputOutput_inImage_iff
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (morphism : interpretation.obj .input ⟶ interpretation.obj .output) :
    InImage interpretation morphism ↔
      morphism = ResourceChangingInterpretation.eval interpretation
        reversiblePath ∨
      morphism = ResourceChangingInterpretation.eval interpretation
        erasurePath := by
  rw [inImage_iff_exists_canonical]
  constructor
  · rintro ⟨canonical, equality⟩
    cases canonical
    · exact Or.inl equality
    · exact Or.inr equality
  · rintro (equality | equality)
    · exact ⟨.reversiblePath, equality⟩
    · exact ⟨.erasurePath, equality⟩

/-- An interpretation separates the diamond when its parallel path
denotations are unequal. -/
def SeparatesPaths
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) : Prop :=
  ResourceChangingInterpretation.eval interpretation reversiblePath ≠
    ResourceChangingInterpretation.eval interpretation erasurePath

/-- Path separation makes canonical denotation injective. -/
theorem canonical_eq_of_eval_eq
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (separates : SeparatesPaths interpretation)
    {X Y : Interface} (left right : Canonical X Y)
    (equality : ResourceChangingInterpretation.eval interpretation left.toExpr =
      ResourceChangingInterpretation.eval interpretation right.toExpr) :
    left = right := by
  cases left <;> cases right
  all_goals first | rfl | exact False.elim (separates equality) |
    exact False.elim (separates equality.symm)

/-- Equality reflection for a diamond interpretation. -/
def SemanticallyComplete
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ) : Prop :=
  ∀ {X Y : Interface} (left right : Expr signature X Y),
    ResourceChangingInterpretation.eval interpretation left =
      ResourceChangingInterpretation.eval interpretation right →
    Derives left right

/-- **Non-thin semantic completeness criterion.** Every path-separating
interpretation reflects formal equality. -/
theorem semanticallyComplete_of_separates
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (separates : SeparatesPaths interpretation) :
    SemanticallyComplete interpretation := by
  intro X Y left right equality
  have leftSound := ResourceChangingInterpretation.soundness interpretation
    (normalize_derives left)
  have rightSound := ResourceChangingInterpretation.soundness interpretation
    (normalize_derives right)
  have canonicalEquality :
      ResourceChangingInterpretation.eval interpretation
          (normalize left).toExpr =
        ResourceChangingInterpretation.eval interpretation
          (normalize right).toExpr :=
    leftSound.symm.trans (equality.trans rightSound)
  have hcanonical := canonical_eq_of_eval_eq interpretation separates
    (normalize left) (normalize right) canonicalEquality
  exact (derives_iff_normalize_eq left right).2 hcanonical

end Ript.Examples.DiamondBitTheory
