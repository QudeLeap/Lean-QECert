import QEC.Coding.Stabilizer.Distance

/-!
# Semantic degeneracy of a binary stabilizer code

This module defines degeneracy independently through a nonzero scalar action
below a finite semantic distance, then characterizes it by low-weight
nonidentity membership in the generated stabilizer up to binary sign.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode

universe u

open PauliSymplectic

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/--
A source-valid binary stabilizer code is semantically degenerate at a finite
distance when a nonidentity Pauli below that distance acts by a nonzero scalar
on all code-carrier matrix elements.
-/
def SemanticallyDegenerateAtDistance
    (Q : SourceValidBinary ι) (d : Nat) : Prop :=
  SemanticStabilizerDistance Q d ∧
  ∃ E : Binary ι, ∃ c : Complex,
    ¬ BinaryUpToSign E (binaryOne (ι := ι)) ∧
    weight E < d ∧ c ≠ 0 ∧
    Semantics.DetectableOnWithScalar Q.1.code (toQubitOperator E) c

/--
Generated-stabilizer membership up to binary sign is exactly nonzero scalar
action on the source-valid code.
-/
theorem inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar
    (Q : SourceValidBinary ι) (E : Binary ι) :
    Q.1.InGeneratedGroupUpToSign E ↔
      ∃ c : Complex, c ≠ 0 ∧
        Semantics.DetectableOnWithScalar Q.1.code (toQubitOperator E) c := by
  constructor
  · intro hGenerated
    obtain ⟨p, hScalar⟩ :=
      scalar_action_on_code_of_inGeneratedGroupUpToSign Q E hGenerated
    refine ⟨binaryPhaseScalar p, ?_, ?_⟩
    · by_cases hp : p = 0
      · simp [hp]
      · simp [binaryPhaseScalar, hp]
    · intro ψ hψ φ hφ
      rw [hScalar φ hφ]
      simp
  · rintro ⟨c, hc, hScalar⟩
    have hDetectable :
        Semantics.DetectableOn Q.1.code (toQubitOperator E) :=
      ⟨c, hScalar⟩
    rcases
        (detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer
          Q E).1 hDetectable with hGenerated | hOutsideNormalizer
    · exact hGenerated
    · obtain ⟨ψ, hψ, hψne⟩ := exists_nonzero_mem_code Q
      have hProduct : c * inner Complex ψ ψ = 0 := by
        rw [← hScalar ψ hψ ψ hψ]
        exact matrixElement_eq_zero_of_not_inBinaryNormalizer
          Q E hOutsideNormalizer ψ hψ ψ hψ
      have hInnerZero : inner Complex ψ ψ = 0 :=
        (mul_eq_zero.mp hProduct).resolve_left hc
      exact False.elim (hψne (inner_self_eq_zero.mp hInnerZero))

/--
Semantic degeneracy below a finite distance is equivalent to a low-weight
nonidentity generated stabilizer representative. This realizes
[Gott97, Ch. 3, stabilizer distance and degeneracy paragraph].
-/
theorem semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign
    (Q : SourceValidBinary ι) (d : Nat) :
    SemanticallyDegenerateAtDistance Q d ↔
      SemanticStabilizerDistance Q d ∧
      ∃ E : Binary ι,
        Q.1.InGeneratedGroupUpToSign E ∧
        ¬ BinaryUpToSign E (binaryOne (ι := ι)) ∧
        weight E < d := by
  constructor
  · rintro ⟨hd, E, c, hNonidentity, hWeight, hc, hScalar⟩
    refine ⟨hd, E, ?_, hNonidentity, hWeight⟩
    exact
      (inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar Q E).2
        ⟨c, hc, hScalar⟩
  · rintro ⟨hd, E, hGenerated, hNonidentity, hWeight⟩
    obtain ⟨c, hc, hScalar⟩ :=
      (inGeneratedGroupUpToSign_iff_exists_nonzero_detectableOnWithScalar Q E).1
        hGenerated
    exact ⟨hd, E, c, hNonidentity, hWeight, hc, hScalar⟩

/--
Under a finite semantic distance witness, nondegeneracy is exactly the lower
weight bound on every nonidentity generated stabilizer representative.
-/
theorem not_semanticallyDegenerateAtDistance_iff_generated_weight_ge
    (Q : SourceValidBinary ι) (d : Nat)
    (hd : SemanticStabilizerDistance Q d) :
    ¬ SemanticallyDegenerateAtDistance Q d ↔
      ∀ E, Q.1.InGeneratedGroupUpToSign E →
        ¬ BinaryUpToSign E (binaryOne (ι := ι)) →
        d ≤ weight E := by
  constructor
  · intro hNondegenerate E hGenerated hNonidentity
    apply Nat.le_of_not_gt
    intro hWeight
    apply hNondegenerate
    exact
      (semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign Q d).2
        ⟨hd, E, hGenerated, hNonidentity, hWeight⟩
  · intro hWeight hDegenerate
    obtain ⟨_, E, hGenerated, hNonidentity, hLowWeight⟩ :=
      (semanticallyDegenerateAtDistance_iff_exists_generatedGroupUpToSign Q d).1
        hDegenerate
    exact (Nat.not_lt_of_ge (hWeight E hGenerated hNonidentity)) hLowWeight

end StabilizerCode
end Coding
end QEC
