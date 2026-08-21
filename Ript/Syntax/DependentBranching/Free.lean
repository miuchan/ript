import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Ript.Syntax.DependentBranching

/-!
# Free algebra and completeness for dependent branching

Dependent finite trees are the free algebra for the polynomial operations
specified by a dependent branching signature: one nullary leaf and, for every
generator `g`, one operation taking an `Outcome g`-indexed family of
continuations.

This file makes that statement categorical.  Branching algebras and their
homomorphisms form a category, the tree algebra is initial, and structural
fold is its unique outgoing morphism.  An explicit congruence derivation is
sound in every algebra and complete because the initial tree algebra reflects
equality.

Leaf substitution (`graft`) supplies sequential protocol composition.  It is
associative with `leaf` as unit, and its height and worst-case resource budget
are subadditive.  Both measures are themselves folds into canonical numeric
algebras.
-/

set_option autoImplicit false

namespace Ript.Syntax.DependentBranching.Free

open CategoryTheory Limits

open Ript.Syntax.DependentBranching

universe u

variable {signature : Signature.{u}}

/-- One algebra for the dependent branching operations of a signature. -/
structure Algebra (signature : Signature.{u}) where
  /-- Semantic carrier. -/
  Carrier : Type u
  /-- Interpretation of protocol termination. -/
  leaf : Carrier
  /-- Interpretation of a generator applied to all interpreted
  continuations. -/
  node : (generator : signature.Generator) →
    (signature.Outcome generator → Carrier) → Carrier

namespace Algebra

instance : CoeSort (Algebra signature) (Type u) :=
  ⟨Algebra.Carrier⟩

/-- Change only the interpretation of termination. -/
def withLeaf (algebra : Algebra signature) (replacement : algebra) :
    Algebra signature where
  Carrier := algebra
  leaf := replacement
  node := algebra.node

end Algebra

/-- Homomorphism of dependent branching algebras. -/
@[ext]
structure Hom (source target : Algebra signature) where
  /-- Carrier map. -/
  toFun : source → target
  /-- Preservation of termination. -/
  map_leaf : toFun source.leaf = target.leaf
  /-- Preservation of every dependent generator operation. -/
  map_node : ∀ generator continuations,
    toFun (source.node generator continuations) =
      target.node generator (fun outcome ↦ toFun (continuations outcome))

namespace Hom

instance {source target : Algebra signature} :
    CoeFun (Hom source target) (fun _ ↦ source → target) :=
  ⟨Hom.toFun⟩

/-- Identity algebra homomorphism. -/
def identity (algebra : Algebra signature) : Hom algebra algebra where
  toFun := id
  map_leaf := rfl
  map_node _ _ := rfl

/-- Composition of algebra homomorphisms. -/
def comp {first second third : Algebra signature}
    (left : Hom first second) (right : Hom second third) :
    Hom first third where
  toFun value := right (left value)
  map_leaf := by rw [left.map_leaf, right.map_leaf]
  map_node generator continuations := by
    rw [left.map_node, right.map_node]

end Hom

/-- Dependent branching algebras and homomorphisms form a category. -/
instance algebraCategory : Category.{u} (Algebra signature) where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp := by
    intro source target morphism
    apply Hom.ext
    rfl
  comp_id := by
    intro source target morphism
    apply Hom.ext
    rfl
  assoc := by
    intro first second third fourth one two three
    apply Hom.ext
    rfl

/-- Structural fold of a dependent tree into an arbitrary algebra. -/
def fold (algebra : Algebra signature) : Tree signature → algebra
  | .leaf => algebra.leaf
  | .node generator next =>
      algebra.node generator fun outcome ↦ fold algebra (next outcome)

@[simp]
theorem fold_leaf (algebra : Algebra signature) :
    fold algebra .leaf = algebra.leaf :=
  rfl

@[simp]
theorem fold_node (algebra : Algebra signature)
    (generator : signature.Generator)
    (next : signature.Outcome generator → Tree signature) :
    fold algebra (.node generator next) =
      algebra.node generator fun outcome ↦ fold algebra (next outcome) :=
  rfl

/-- The syntax tree itself is the canonical free branching algebra. -/
abbrev treeAlgebra (signature : Signature.{u}) : Algebra signature where
  Carrier := Tree signature
  leaf := .leaf
  node := .node

/-- Folding a tree back into the tree algebra is the identity. -/
@[simp]
theorem fold_treeAlgebra (tree : Tree signature) :
    fold (treeAlgebra signature) tree = tree := by
  induction tree with
  | leaf => rfl
  | node generator next induction =>
      simp only [fold_node]
      congr 1
      funext outcome
      exact induction outcome

/-- Every algebra receives its canonical fold homomorphism from syntax. -/
def foldHom (algebra : Algebra signature) :
    treeAlgebra signature ⟶ algebra where
  toFun := fold algebra
  map_leaf := rfl
  map_node _ _ := rfl

/-- Every homomorphism from the tree algebra acts by structural fold. -/
theorem hom_apply_eq_fold (algebra : Algebra signature)
    (morphism : treeAlgebra signature ⟶ algebra)
    (tree : Tree signature) :
    morphism.toFun tree = fold algebra tree := by
  induction tree with
  | leaf => exact morphism.map_leaf
  | node generator next induction =>
      rw [morphism.map_node, fold_node]
      congr 1
      funext outcome
      exact induction outcome

/-- Homomorphisms from the tree algebra are unique. -/
theorem hom_ext_from_tree (algebra : Algebra signature)
    (first second : treeAlgebra signature ⟶ algebra) : first = second := by
  apply Hom.ext
  funext tree
  rw [hom_apply_eq_fold algebra first, hom_apply_eq_fold algebra second]

/-- **Free branching initiality.**  The dependent tree algebra is an initial
object in the category of branching algebras. -/
def treeAlgebraIsInitial : IsInitial (treeAlgebra signature) :=
  IsInitial.ofUnique (h := fun algebra ↦
    { default := foldHom algebra
      uniq := fun morphism ↦ hom_ext_from_tree algebra morphism (foldHom algebra) })

/-- The type of strict branching interpretations from syntax is contractible. -/
def homEquivPUnit (algebra : Algebra signature) :
    (treeAlgebra signature ⟶ algebra) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := foldHom algebra
  left_inv morphism := hom_ext_from_tree algebra (foldHom algebra) morphism
  right_inv point := by cases point; rfl

/-! ## Explicit equational theory -/

/-- Congruence derivations for the free dependent branching theory. -/
inductive Derives : Tree signature → Tree signature → Prop where
  /-- Reflexivity. -/
  | refl (tree : Tree signature) : Derives tree tree
  /-- Symmetry. -/
  | symm {first second : Tree signature} :
      Derives first second → Derives second first
  /-- Transitivity. -/
  | trans {first second third : Tree signature} :
      Derives first second → Derives second third → Derives first third
  /-- Congruence for every dependent generator node. -/
  | node (generator : signature.Generator)
      {first second : signature.Outcome generator → Tree signature} :
      (∀ outcome, Derives (first outcome) (second outcome)) →
        Derives (.node generator first) (.node generator second)

namespace Derives

/-- **Soundness of free branching equations.**  Every derivation is respected
by every branching algebra. -/
theorem sound {first second : Tree signature}
    (derivation : Derives first second) (algebra : Algebra signature) :
    fold algebra first = fold algebra second := by
  induction derivation with
  | refl tree => rfl
  | symm _ induction => exact induction.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | node generator relation induction =>
      simp only [fold_node]
      congr 1
      funext outcome
      exact induction outcome

/-- Derivability in the equation-free branching theory is exactly structural
tree equality. -/
theorem iff_eq {first second : Tree signature} :
    Derives first second ↔ first = second := by
  constructor
  · intro derivation
    simpa using derivation.sound (treeAlgebra signature)
  · rintro rfl
    exact .refl first

/-- **Term-model completeness.**  Equality under every branching
interpretation implies a formal derivation. -/
theorem complete_via_treeAlgebra {first second : Tree signature}
    (semanticallyEqual : ∀ algebra : Algebra signature,
      fold algebra first = fold algebra second) :
    Derives first second := by
  apply iff_eq.mpr
  simpa using semanticallyEqual (treeAlgebra signature)

/-- **Absolute branching completeness.**  Formal derivability is equivalent
to equality in every algebraic interpretation. -/
theorem semanticCompleteness {first second : Tree signature} :
    Derives first second ↔
      ∀ algebra : Algebra signature,
        fold algebra first = fold algebra second := by
  constructor
  · intro derivation algebra
    exact derivation.sound algebra
  · exact complete_via_treeAlgebra

end Derives

/-! ## Sequential leaf substitution -/

/-- Replace every terminal leaf of `first` by the same continuation `second`. -/
def graft : Tree signature → Tree signature → Tree signature
  | .leaf, second => second
  | .node generator next, second =>
      .node generator fun outcome ↦ graft (next outcome) second

@[simp]
theorem leaf_graft (tree : Tree signature) : graft .leaf tree = tree :=
  rfl

@[simp]
theorem graft_leaf (tree : Tree signature) : graft tree .leaf = tree := by
  induction tree with
  | leaf => rfl
  | node generator next induction =>
      simp only [graft]
      congr 1
      funext outcome
      exact induction outcome

/-- Leaf substitution is associative. -/
theorem graft_assoc (first second third : Tree signature) :
    graft (graft first second) third = graft first (graft second third) := by
  induction first with
  | leaf => rfl
  | node generator next induction =>
      simp only [graft]
      congr 1
      funext outcome
      exact induction outcome

/-- Dependent trees form a monoid under sequential leaf substitution. -/
instance treeMonoid : Monoid (Tree signature) where
  one := .leaf
  mul := graft
  one_mul := leaf_graft
  mul_one := graft_leaf
  mul_assoc := graft_assoc

/-- Folding a graft is folding the first tree with the folded continuation as
its leaf value. -/
theorem fold_graft (algebra : Algebra signature)
    (first second : Tree signature) :
    fold algebra (graft first second) =
      fold (algebra.withLeaf (fold algebra second)) first := by
  induction first with
  | leaf => rfl
  | node generator next induction =>
      simp only [graft, fold_node, Algebra.withLeaf]
      congr 1
      funext outcome
      exact induction outcome

/-- Numeric algebra whose fold computes maximum branch depth. -/
def heightAlgebra (signature : Signature.{u}) : Algebra signature where
  Carrier := ULift.{u} Nat
  leaf := ULift.up 0
  node _ continuations :=
    ULift.up (1 + Finset.univ.sup fun outcome ↦ (continuations outcome).down)

/-- Tree height is exactly its algebraic fold. -/
theorem fold_height (tree : Tree signature) :
    (fold (heightAlgebra signature) tree).down = tree.height := by
  induction tree with
  | leaf => rfl
  | node generator next induction =>
      change 1 + Finset.univ.sup
          (fun outcome ↦ (fold (heightAlgebra signature) (next outcome)).down) =
        1 + Finset.univ.sup fun outcome ↦ (next outcome).height
      congr 1
      apply Finset.sup_congr rfl
      intro outcome _
      exact induction outcome

/-- Numeric algebra whose fold computes worst-case resource cost. -/
def budgetAlgebra (signature : Signature.{u}) : Algebra signature where
  Carrier := ULift.{u} Nat
  leaf := ULift.up 0
  node generator continuations :=
    ULift.up (signature.cost generator +
      Finset.univ.sup fun outcome ↦ (continuations outcome).down)

/-- Worst-case resource budget is exactly its algebraic fold. -/
theorem fold_budget (tree : Tree signature) :
    (fold (budgetAlgebra signature) tree).down = tree.budget := by
  induction tree with
  | leaf => rfl
  | node generator next induction =>
      change signature.cost generator + Finset.univ.sup
          (fun outcome ↦ (fold (budgetAlgebra signature) (next outcome)).down) =
        signature.cost generator +
          Finset.univ.sup fun outcome ↦ (next outcome).budget
      congr 1
      apply Finset.sup_congr rfl
      intro outcome _
      exact induction outcome

/-- Maximum depth is subadditive under sequential grafting. -/
theorem height_graft_le (first second : Tree signature) :
    (graft first second).height ≤ first.height + second.height := by
  induction first with
  | leaf => simp
  | node generator next induction =>
      simp only [graft, Tree.height]
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      apply Finset.sup_le
      intro outcome _
      exact (induction outcome).trans
        (Nat.add_le_add_right
          (Finset.le_sup (f := fun result ↦ (next result).height)
            (Finset.mem_univ outcome)) second.height)

/-- Worst-case resource budget is subadditive under sequential grafting. -/
theorem budget_graft_le (first second : Tree signature) :
    (graft first second).budget ≤ first.budget + second.budget := by
  induction first with
  | leaf => simp
  | node generator next induction =>
      simp only [graft, Tree.budget]
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      apply Finset.sup_le
      intro outcome _
      exact (induction outcome).trans
        (Nat.add_le_add_right
          (Finset.le_sup (f := fun result ↦ (next result).budget)
            (Finset.mem_univ outcome)) second.budget)

end Ript.Syntax.DependentBranching.Free
