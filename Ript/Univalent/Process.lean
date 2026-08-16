import Ript.Univalent.Soundness

/-!
# Deeply embedded processes over the internal universe

The Stage-11 universe is not only a syntax of interface identities.  This file
adds typed process expressions, their set-level interpretation, transport
along internal structural equivalences, an explicit equational derivation
system, and a kernel-checked soundness theorem.

Transport is conjugation by the interpreted source and target equivalences.  A
separate theorem identifies this operation with the structure-identity
transport supplied by internal univalence.
-/

set_option autoImplicit false

namespace Ript.Univalent

universe u

/-- A typed signature of primitive processes over interface codes. -/
structure ProcessSignature (Atom : Type u) where
  /-- Primitive processes indexed by their input and output interfaces. -/
  Generator : Code Atom → Code Atom → Type u

/-- Deeply embedded typed process expressions with explicit reindexing along
internal structural equivalences. -/
inductive ProcessExpr {Atom : Type u} (signature : ProcessSignature Atom) :
    Code Atom → Code Atom → Type u where
  /-- A primitive process from the signature. -/
  | generator {A B : Code Atom} (generator : signature.Generator A B) :
      ProcessExpr signature A B
  /-- Identity process. -/
  | id (A : Code Atom) : ProcessExpr signature A A
  /-- Serial composition, written in execution order. -/
  | comp {A B C : Code Atom} (first : ProcessExpr signature A B)
      (second : ProcessExpr signature B C) : ProcessExpr signature A C
  /-- Parallel composition. -/
  | tensor {A B C D : Code Atom} (left : ProcessExpr signature A B)
      (right : ProcessExpr signature C D) :
      ProcessExpr signature (.tensor A C) (.tensor B D)
  /-- Reindex a process by structural equivalences of its source and target. -/
  | reindex {A A' B B' : Code Atom} (source : EquivExpr A A')
      (target : EquivExpr B B') (process : ProcessExpr signature A B) :
      ProcessExpr signature A' B'

/-- Interpretation of the primitive processes of a signature in a universe
model's deterministic process spaces. -/
structure ProcessInterpretation {Atom : Type u} (signature : ProcessSignature Atom)
    (model : UniverseModel Atom) where
  /-- Interpret every primitive generator as a typed function. -/
  generator : ∀ {A B : Code Atom}, signature.Generator A B →
    model.FunctionProcess A B

namespace ProcessExpr

variable {Atom : Type u} {signature : ProcessSignature Atom}
variable {model : UniverseModel Atom}
variable {A B C D : Code Atom}

/-- Evaluate a deeply embedded process as a deterministic function between
the externally interpreted endpoint types. -/
def eval (interpretation : ProcessInterpretation signature model)
    {A B : Code Atom} (process : ProcessExpr signature A B) :
    model.FunctionProcess A B :=
  match process with
  | .generator primitive => interpretation.generator primitive
  | .id _ => fun input => input
  | .comp first second => fun input =>
      eval interpretation second (eval interpretation first input)
  | .tensor left right => fun input =>
      (eval interpretation left input.1, eval interpretation right input.2)
  | .reindex source target process => fun input =>
      target.denote model.atomSemantics
        (eval interpretation process ((source.denote model.atomSemantics).symm input))

variable (interpretation : ProcessInterpretation signature model)

@[simp]
theorem eval_generator {generator : signature.Generator A B} :
    eval interpretation (.generator generator) = interpretation.generator generator :=
  rfl

@[simp]
theorem eval_id (A : Code Atom) :
    eval interpretation (.id A) = fun input => input :=
  rfl

@[simp]
theorem eval_comp (first : ProcessExpr signature A B)
    (second : ProcessExpr signature B C) :
    eval interpretation (.comp first second) =
      fun input => eval interpretation second (eval interpretation first input) :=
  rfl

@[simp]
theorem eval_tensor (left : ProcessExpr signature A B)
    (right : ProcessExpr signature C D) :
    eval interpretation (.tensor left right) = fun input =>
      (eval interpretation left input.1, eval interpretation right input.2) :=
  rfl

/-- Evaluation of process reindexing is exactly transport along the internal
identities obtained by univalence. -/
theorem eval_reindex_eq_structureIdentity {A' B' : Code Atom}
    (source : EquivExpr A A') (target : EquivExpr B B')
    (process : ProcessExpr signature A B) :
    eval interpretation (.reindex source target process) =
      UniverseModel.functionProcessStructureIdentity model
        (UniverseModel.equivToId model
          (UniverseModel.InternalEquiv.mk model source))
        (UniverseModel.equivToId model
          (UniverseModel.InternalEquiv.mk model target))
        (eval interpretation process) :=
  rfl

end ProcessExpr

/-- Explicit equational derivations for the deep process syntax. -/
inductive ProcessDerives {Atom : Type u} {signature : ProcessSignature Atom} :
    {A B : Code Atom} → ProcessExpr signature A B → ProcessExpr signature A B → Prop where
  /-- Reflexivity. -/
  | refl {A B : Code Atom} (process : ProcessExpr signature A B) :
      ProcessDerives process process
  /-- Symmetry. -/
  | symm {A B : Code Atom} {first second : ProcessExpr signature A B}
      (derivation : ProcessDerives first second) : ProcessDerives second first
  /-- Transitivity. -/
  | trans {A B : Code Atom} {first second third : ProcessExpr signature A B}
      (firstDerivation : ProcessDerives first second)
      (secondDerivation : ProcessDerives second third) :
      ProcessDerives first third
  /-- Congruence for serial composition. -/
  | comp_congr {A B C : Code Atom}
      {first first' : ProcessExpr signature A B}
      {second second' : ProcessExpr signature B C}
      (hFirst : ProcessDerives first first')
      (hSecond : ProcessDerives second second') :
      ProcessDerives (.comp first second) (.comp first' second')
  /-- Congruence for parallel composition. -/
  | tensor_congr {A B C D : Code Atom}
      {left left' : ProcessExpr signature A B}
      {right right' : ProcessExpr signature C D}
      (hLeft : ProcessDerives left left')
      (hRight : ProcessDerives right right') :
      ProcessDerives (.tensor left right) (.tensor left' right')
  /-- Congruence for equivalence reindexing. -/
  | reindex_congr {A A' B B' : Code Atom}
      (source : EquivExpr A A') (target : EquivExpr B B')
      {first second : ProcessExpr signature A B}
      (derivation : ProcessDerives first second) :
      ProcessDerives (.reindex source target first) (.reindex source target second)
  /-- Left identity law. -/
  | id_comp {A B : Code Atom} (process : ProcessExpr signature A B) :
      ProcessDerives (.comp (.id A) process) process
  /-- Right identity law. -/
  | comp_id {A B : Code Atom} (process : ProcessExpr signature A B) :
      ProcessDerives (.comp process (.id B)) process
  /-- Associativity of serial composition. -/
  | assoc {A B C D : Code Atom} (first : ProcessExpr signature A B)
      (second : ProcessExpr signature B C) (third : ProcessExpr signature C D) :
      ProcessDerives (.comp (.comp first second) third)
        (.comp first (.comp second third))
  /-- Tensor preserves identity. -/
  | tensor_id (A B : Code Atom) :
      ProcessDerives (.tensor (.id A) (.id B)) (.id (.tensor A B))
  /-- Interchange between tensor and serial composition. -/
  | interchange {A B C D E F : Code Atom}
      (firstLeft : ProcessExpr signature A B)
      (secondLeft : ProcessExpr signature B C)
      (firstRight : ProcessExpr signature D E)
      (secondRight : ProcessExpr signature E F) :
      ProcessDerives
        (.tensor (.comp firstLeft secondLeft) (.comp firstRight secondRight))
        (.comp (.tensor firstLeft firstRight) (.tensor secondLeft secondRight))
  /-- Reindexing by reflexive equivalences changes no semantics. -/
  | reindex_refl {A B : Code Atom} (process : ProcessExpr signature A B) :
      ProcessDerives (.reindex (.refl A) (.refl B) process) process
  /-- Successive reindexing composes the endpoint equivalences. -/
  | reindex_trans {A A' A'' B B' B'' : Code Atom}
      (source₁ : EquivExpr A A') (source₂ : EquivExpr A' A'')
      (target₁ : EquivExpr B B') (target₂ : EquivExpr B' B'')
      (process : ProcessExpr signature A B) :
      ProcessDerives
        (.reindex source₂ target₂ (.reindex source₁ target₁ process))
        (.reindex (.trans source₁ source₂) (.trans target₁ target₂) process)

namespace ProcessDerives

variable {Atom : Type u} {signature : ProcessSignature Atom}
variable {model : UniverseModel Atom}
variable (interpretation : ProcessInterpretation signature model)
variable {A B : Code Atom} {first second : ProcessExpr signature A B}

/-- Every derivable equation of deep process expressions is valid in every
deterministic universe interpretation. -/
theorem soundness (derivation : ProcessDerives first second) :
    ProcessExpr.eval interpretation first = ProcessExpr.eval interpretation second := by
  induction derivation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | comp_congr _ _ firstHypothesis secondHypothesis =>
      funext input
      simp only [ProcessExpr.eval]
      rw [firstHypothesis, secondHypothesis]
  | tensor_congr _ _ leftHypothesis rightHypothesis =>
      funext input
      simp only [ProcessExpr.eval]
      rw [leftHypothesis, rightHypothesis]
  | reindex_congr _ _ _ inductionHypothesis =>
      funext input
      simp only [ProcessExpr.eval]
      rw [inductionHypothesis]
  | id_comp => rfl
  | comp_id => rfl
  | assoc => rfl
  | tensor_id => rfl
  | interchange => rfl
  | reindex_refl => rfl
  | reindex_trans => rfl

end ProcessDerives

end Ript.Univalent
