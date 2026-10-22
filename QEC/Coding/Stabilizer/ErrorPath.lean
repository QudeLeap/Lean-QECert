import QEC.Coding.Stabilizer.LocalHamiltonian
import QEC.Coding.Stabilizer.Distance

/-!
# Single-qubit Pauli error paths

This module defines finite Pauli walks by their actual increments. Every
increment has weight at most one, while the initial state, intermediate states,
and endpoint are computed from binary Pauli multiplication.

The logical-endpoint predicate reuses the existing source-valid stabilizer
normalizer semantics. Energy, decoding, and thermal dynamics are deliberately
outside this interface.
-/

noncomputable section

namespace QEC
namespace Coding

open PauliSymplectic

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/--
A finite Pauli error path, represented by the actual sequence of increments.

An increment may be the identity, so the bound is "at most one qubit" rather
than "exactly one qubit", matching the source definition of a Pauli walk.
-/
structure PauliErrorPath where
  increments : List (Binary ι)
  step_weight_le_one : ∀ step ∈ increments, weight step ≤ 1

namespace PauliErrorPath

/-- Accumulate a list of Pauli increments from the identity. -/
def accumulate (steps : List (Binary ι)) : Binary ι :=
  steps.foldl binaryMul binaryOne

/-- The identity path with no increments. -/
def empty : PauliErrorPath (ι := ι) where
  increments := []
  step_weight_le_one := by simp

/-- A one-step path from an increment of weight at most one. -/
def singleton (step : Binary ι) (hstep : weight step ≤ 1) :
    PauliErrorPath (ι := ι) where
  increments := [step]
  step_weight_le_one := by
    simpa using hstep

/-- The accumulated endpoint of a Pauli error path. -/
def endpoint (γ : PauliErrorPath (ι := ι)) : Binary ι :=
  accumulate γ.increments

/-- The state after the first `n` increments. -/
def stateAt (γ : PauliErrorPath (ι := ι)) (n : Nat) : Binary ι :=
  accumulate (γ.increments.take n)

/--
All accumulated path states, including the identity before the first increment
and the endpoint after the final increment.
-/
def states (γ : PauliErrorPath (ι := ι)) : List (Binary ι) :=
  γ.increments.scanl binaryMul binaryOne

/-- Restrict a path to the prefix consisting of its first `n` increments. -/
def take (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    PauliErrorPath (ι := ι) where
  increments := γ.increments.take n
  step_weight_le_one := by
    intro step hstep
    exact γ.step_weight_le_one step (List.mem_of_mem_take hstep)

/-- Concatenate the actual increment lists of two paths. -/
def append (γ δ : PauliErrorPath (ι := ι)) : PauliErrorPath (ι := ι) where
  increments := γ.increments ++ δ.increments
  step_weight_le_one := by
    intro step hstep
    rcases List.mem_append.mp hstep with hγ | hδ
    · exact γ.step_weight_le_one step hγ
    · exact δ.step_weight_le_one step hδ

omit [DecidableEq ι] in
@[simp]
theorem accumulate_nil :
    accumulate ([] : List (Binary ι)) = binaryOne :=
  rfl

omit [DecidableEq ι] in
@[simp]
theorem accumulate_singleton (step : Binary ι) :
    accumulate [step] = step := by
  simp [accumulate]

omit [DecidableEq ι] in
/-- Starting a fold at `start` left-multiplies the identity-based accumulation. -/
theorem foldl_binaryMul_eq_binaryMul_accumulate
    (steps : List (Binary ι)) (start : Binary ι) :
    steps.foldl binaryMul start = binaryMul start (accumulate steps) := by
  unfold accumulate
  induction steps generalizing start with
  | nil =>
      simp
  | cons step rest ih =>
      simp only [List.foldl_cons]
      rw [ih (binaryMul start step), ih (binaryMul binaryOne step)]
      simp [binaryMul_assoc]

omit [DecidableEq ι] in
/-- Accumulation respects list concatenation. -/
theorem accumulate_append (left right : List (Binary ι)) :
    accumulate (left ++ right) =
      binaryMul (accumulate left) (accumulate right) := by
  rw [accumulate, List.foldl_append]
  exact foldl_binaryMul_eq_binaryMul_accumulate right (accumulate left)

@[simp]
theorem endpoint_empty :
    (empty (ι := ι)).endpoint = binaryOne :=
  rfl

@[simp]
theorem endpoint_singleton (step : Binary ι) (hstep : weight step ≤ 1) :
    (singleton step hstep).endpoint = step :=
  accumulate_singleton step

@[simp]
theorem stateAt_zero (γ : PauliErrorPath (ι := ι)) :
    γ.stateAt 0 = binaryOne := by
  simp [stateAt]

@[simp]
theorem stateAt_length (γ : PauliErrorPath (ι := ι)) :
    γ.stateAt γ.increments.length = γ.endpoint := by
  simp [stateAt, endpoint]

@[simp]
theorem states_length (γ : PauliErrorPath (ι := ι)) :
    γ.states.length = γ.increments.length + 1 := by
  simp [states]

@[simp]
theorem states_head_eq_some (γ : PauliErrorPath (ι := ι)) :
    γ.states.head? = some binaryOne := by
  simp [states]

@[simp]
theorem states_getLast_eq_some (γ : PauliErrorPath (ι := ι)) :
    γ.states.getLast? = some γ.endpoint := by
  exact List.getLast?_scanl

/-- Every indexed accumulated state is the product of the corresponding prefix. -/
theorem states_getElem (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.states.length) :
    γ.states[n] = γ.stateAt n := by
  simp [states, stateAt, accumulate]

/-- Each available increment satisfies the single-qubit weight bound. -/
theorem getElem_weight_le_one (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.increments.length) :
    weight γ.increments[n] ≤ 1 :=
  γ.step_weight_le_one γ.increments[n] (List.getElem_mem hn)

/-- Consecutive accumulated states differ by the stored increment. -/
theorem stateAt_succ (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.increments.length) :
    γ.stateAt (n + 1) =
      binaryMul (γ.stateAt n) γ.increments[n] := by
  rw [stateAt, List.take_succ_eq_append_getElem hn, accumulate_append]
  simp [stateAt]

@[simp]
theorem take_increments (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    (γ.take n).increments = γ.increments.take n :=
  rfl

@[simp]
theorem endpoint_take (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    (γ.take n).endpoint = γ.stateAt n :=
  rfl

@[simp]
theorem append_increments (γ δ : PauliErrorPath (ι := ι)) :
    (γ.append δ).increments = γ.increments ++ δ.increments :=
  rfl

/-- The endpoint of concatenated increments is the product of the endpoints. -/
theorem endpoint_append (γ δ : PauliErrorPath (ι := ι)) :
    (γ.append δ).endpoint = binaryMul γ.endpoint δ.endpoint :=
  accumulate_append γ.increments δ.increments

/--
The endpoint is a nontrivial Pauli logical exactly when it normalizes the
existing stabilizer but is not in its generated group up to sign.
-/
def HasLogicalEndpoint
    (γ : PauliErrorPath (ι := ι)) (Q : StabilizerCode.SourceValidBinary ι) :
    Prop :=
  Q.1.InBinaryNormalizer γ.endpoint ∧
    ¬ Q.1.InGeneratedGroupUpToSign γ.endpoint

/-- The path predicate is exactly the existing M3 nondetectability sector. -/
theorem hasLogicalEndpoint_iff_not_detectableOn
    (γ : PauliErrorPath (ι := ι)) (Q : StabilizerCode.SourceValidBinary ι) :
    γ.HasLogicalEndpoint Q ↔
      ¬ Semantics.DetectableOn Q.1.code (toQubitOperator γ.endpoint) := by
  exact
    (StabilizerCode.not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
      Q γ.endpoint).symm

end PauliErrorPath

namespace StabilizerCode.LocalStabilizerHamiltonian

variable {κ : Type v} [Fintype κ]

/--
A convenience specialization of the generic path predicate to the existing
source-valid code carried by a selected local stabilizer Hamiltonian.
-/
def HasLogicalEndpoint
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) : Prop :=
  γ.HasLogicalEndpoint H.code

end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC
