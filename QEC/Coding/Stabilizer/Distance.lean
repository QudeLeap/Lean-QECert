import QEC.Coding.Stabilizer.Detectability

/-!
# Semantic distance of a binary stabilizer code

This module defines finite semantic Pauli distance directly through failure of
the scalar matrix-element condition, then characterizes it by the least weight
in the binary normalizer outside the generated stabilizer up to sign.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode

universe u

open PauliSymplectic

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/--
A finite semantic Pauli distance is attained by a nondetectable binary Pauli
and is a lower bound for every nondetectable binary Pauli.
-/
def SemanticStabilizerDistance (Q : SourceValidBinary ι) (d : Nat) : Prop :=
  ∃ E : Binary ι,
    ¬ Semantics.DetectableOn Q.1.code (toQubitOperator E) ∧
    weight E = d ∧
    ∀ F : Binary ι,
      ¬ Semantics.DetectableOn Q.1.code (toQubitOperator F) →
      d ≤ weight F

/--
Negating the source-valid stabilizer detectability characterization identifies
semantic nondetectability with the binary normalizer logical sector.
-/
theorem not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
    (Q : SourceValidBinary ι) (E : Binary ι) :
    ¬ Semantics.DetectableOn Q.1.code (toQubitOperator E) ↔
      Q.1.InBinaryNormalizer E ∧ ¬ Q.1.InGeneratedGroupUpToSign E := by
  rw [detectableOn_toQubitOperator_iff_inGeneratedGroupUpToSign_or_not_inBinaryNormalizer]
  tauto

/--
For a source-valid binary stabilizer code, finite semantic Pauli distance is
exactly the attained least weight in the binary normalizer outside the
generated stabilizer up to sign. This realizes the distance characterization
of [Gott97, Ch. 2, distance paragraph; Ch. 3, stabilizer distance paragraph].
-/
theorem semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
    (Q : SourceValidBinary ι) (d : Nat) :
    SemanticStabilizerDistance Q d ↔
      ∃ E : Binary ι,
        Q.1.InBinaryNormalizer E ∧
        ¬ Q.1.InGeneratedGroupUpToSign E ∧
        weight E = d ∧
        ∀ F : Binary ι,
          Q.1.InBinaryNormalizer F →
          ¬ Q.1.InGeneratedGroupUpToSign F →
          d ≤ weight F := by
  constructor
  · rintro ⟨E, hNondetectable, hWeight, hLeast⟩
    have hLogical :=
      (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
        Q E).1 hNondetectable
    refine ⟨E, hLogical.1, hLogical.2, hWeight, ?_⟩
    intro F hNormalizer hOutsideGenerated
    exact hLeast F
      ((not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
        Q F).2 ⟨hNormalizer, hOutsideGenerated⟩)
  · rintro ⟨E, hNormalizer, hOutsideGenerated, hWeight, hLeast⟩
    refine ⟨E, ?_, hWeight, ?_⟩
    · exact
        (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
          Q E).2 ⟨hNormalizer, hOutsideGenerated⟩
    · intro F hNondetectable
      have hLogical :=
        (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
          Q F).1 hNondetectable
      exact hLeast F hLogical.1 hLogical.2

/--
A finite semantic stabilizer distance exists exactly when the binary normalizer
logical sector is nonempty. The forward implication uses the attained semantic
witness; the reverse implication minimizes weight over the finite binary Pauli
space.
-/
theorem exists_semanticStabilizerDistance_iff_exists_logicalPauli
    (Q : SourceValidBinary ι) :
    (∃ d, SemanticStabilizerDistance Q d) ↔
      ∃ E, Q.1.InBinaryNormalizer E ∧
        ¬ Q.1.InGeneratedGroupUpToSign E := by
  constructor
  · rintro ⟨d, E, hNondetectable, _hWeight, _hLeast⟩
    exact ⟨E,
      (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
        Q E).1 hNondetectable⟩
  · rintro ⟨E, hNormalizer, hOutsideGenerated⟩
    classical
    let logicalPaulis : Finset (Binary ι) :=
      Finset.univ.filter fun P =>
        Q.1.InBinaryNormalizer P ∧ ¬ Q.1.InGeneratedGroupUpToSign P
    have hNonempty : logicalPaulis.Nonempty := by
      exact ⟨E, by simp [logicalPaulis, hNormalizer, hOutsideGenerated]⟩
    obtain ⟨P, hP, hMinimum⟩ :=
      Finset.exists_min_image logicalPaulis (fun A : Binary ι => weight A) hNonempty
    have hPNormalizer : Q.1.InBinaryNormalizer P :=
      (Finset.mem_filter.mp hP).2.1
    have hPOutsideGenerated : ¬ Q.1.InGeneratedGroupUpToSign P :=
      (Finset.mem_filter.mp hP).2.2
    refine ⟨weight P,
      (semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff Q (weight P)).2
        ⟨P, hPNormalizer, hPOutsideGenerated, rfl, ?_⟩⟩
    intro F hFNormalizer hFOutsideGenerated
    exact hMinimum F (by simp [logicalPaulis, hFNormalizer, hFOutsideGenerated])

end StabilizerCode
end Coding
end QEC
