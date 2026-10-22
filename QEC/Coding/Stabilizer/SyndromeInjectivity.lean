import QEC.Coding.Stabilizer.Correctability
import QEC.Coding.Stabilizer.Degeneracy

/-!
# Nondegenerate correctable-error syndrome injectivity

This module combines finite-Kraus correctability, generator-indexed syndrome
laws, and semantic nondegeneracy to distinguish bounded active Pauli errors up
to the stored binary sign.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode

open PauliSymplectic

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private theorem inBinaryNormalizer_of_inStabilizerNormalizer_of_generated_eq
    {κ : Type v} [Fintype κ]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    {E : Binary ι} (hE : InStabilizerNormalizer generators E) :
    Q.1.InBinaryNormalizer E := by
  intro S hS
  apply hE S
  have : S ∈ ({P | GeneratedStabilizer generators P} : Set (Binary ι)) := by
    rw [hgenerated]
    exact hS
  exact this

omit [DecidableEq ι] in
private theorem binaryUpToSign_relative_one_iff (E F : Binary ι) :
    BinaryUpToSign (binaryMul (binaryDagger E) F) binaryOne ↔
      BinaryUpToSign E F := by
  have hneg (P : SymplecticVector (ZMod 2) ι) : -P = P := by
    apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
    rw [map_neg]
    change (-P.xPart, -P.zPart) = (P.xPart, P.zPart)
    apply Prod.ext
    · funext i
      exact ZMod.neg_eq_self_mod_two _
    · funext i
      exact ZMod.neg_eq_self_mod_two _
  constructor
  · intro hRelative
    change E.vector + F.vector = 0 at hRelative
    change E.vector = F.vector
    calc
      E.vector = -F.vector := (add_eq_zero_iff_eq_neg.mp hRelative)
      _ = F.vector := hneg F.vector
  · intro hEF
    change E.vector + F.vector = 0
    rw [hEF]
    rw [add_eq_zero_iff_eq_neg]
    exact (hneg F.vector).symm

/--
For a source-valid binary stabilizer code with finite semantic distance, a
complete correctable finite binary-Pauli Kraus family supported in a radius
strictly below half the distance has generator-indexed syndromes that are
injective up to stored binary sign on its nonzero-amplitude support.

This realizes the bounded nondegenerate syndrome distinction of
[Gott97, Ch. 2, distance paragraph; Ch. 3, stabilizer error-set criterion,
stabilizer distance and degeneracy paragraph, and error syndrome].
-/
theorem stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
    {κ : Type v} [Fintype κ] {α : Type w} [Fintype α]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    (d t : Nat) (hd : SemanticStabilizerDistance Q d)
    (hNondegenerate : ¬ SemanticallyDegenerateAtDistance Q d)
    (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete)
    (hcorrectable : ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.FiniteKrausCorrectable α
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
          Q.1.code (binaryPauliKrausFamily E amp) recovery)
    (hweight : ∀ i, amp i ≠ 0 → weight (E i) ≤ t)
    (hradius : 2 * t < d) :
    ∀ i j, amp i ≠ 0 → amp j ≠ 0 →
      stabilizerSyndrome generators (E i) = stabilizerSyndrome generators (E j) →
      BinaryUpToSign (E i) (E j) := by
  intro i j hi hj hsyndrome
  let relative := binaryMul (binaryDagger (E i)) (E j)
  have hpairs :=
    (exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
      Q E amp hcomplete).1 hcorrectable
  have hrelativeGenerated : Q.1.InGeneratedGroupUpToSign relative := by
    rcases hpairs i j hi hj with hGenerated | hOutsideNormalizer
    · exact hGenerated
    · have hproperties :=
        stabilizerSyndrome_map_properties generators relative (E i) (E j)
      have hproductZero :
          stabilizerSyndrome generators (binaryMul (E i) (E j)) = 0 :=
        hproperties.2.1.mp hsyndrome
      have hrelativeZero : stabilizerSyndrome generators relative = 0 := by
        calc
          stabilizerSyndrome generators relative =
              stabilizerSyndrome generators (binaryMul (E i) (E j)) :=
            hproperties.2.2.symm
          _ = 0 := hproductZero
      have hgeneratorNormalizer : InStabilizerNormalizer generators relative :=
        hproperties.1.mp hrelativeZero
      have hcodeNormalizer : Q.1.InBinaryNormalizer relative :=
        inBinaryNormalizer_of_inStabilizerNormalizer_of_generated_eq
          Q generators hgenerated hgeneratorNormalizer
      exact False.elim (hOutsideNormalizer hcodeNormalizer)
  have hrelativeWeight : weight relative ≤ weight (E i) + weight (E j) := by
    simpa [relative] using weight_binaryMul_le (binaryDagger (E i)) (E j)
  have hrelativeLt : weight relative < d := by
    have hiWeight := hweight i hi
    have hjWeight := hweight j hj
    omega
  by_cases hidentity : BinaryUpToSign relative binaryOne
  · exact (binaryUpToSign_relative_one_iff (E i) (E j)).1 hidentity
  · have hlower : d ≤ weight relative :=
      (not_semanticallyDegenerateAtDistance_iff_generated_weight_ge Q d hd).1
        hNondegenerate relative hrelativeGenerated hidentity
    omega

/--
If the active Pauli representatives contain no duplicates modulo stored sign,
the syndrome map is literally injective on active family indices.
-/
theorem stabilizerSyndrome_injective_on_active_of_correctable_nondegenerate
    {κ : Type v} [Fintype κ] {α : Type w} [Fintype α]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    (d t : Nat) (hd : SemanticStabilizerDistance Q d)
    (hNondegenerate : ¬ SemanticallyDegenerateAtDistance Q d)
    (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete)
    (hcorrectable : ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.FiniteKrausCorrectable α
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
          Q.1.code (binaryPauliKrausFamily E amp) recovery)
    (hweight : ∀ i, amp i ≠ 0 → weight (E i) ≤ t)
    (hradius : 2 * t < d)
    (hNoDuplicates : ∀ i j, amp i ≠ 0 → amp j ≠ 0 →
      BinaryUpToSign (E i) (E j) → i = j) :
    Function.Injective (fun i : {i // amp i ≠ 0} =>
      stabilizerSyndrome generators (E i.1)) := by
  intro i j hsyndrome
  apply Subtype.ext
  apply hNoDuplicates i.1 j.1 i.2 j.2
  exact stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
    Q generators hgenerated d t hd hNondegenerate E amp hcomplete hcorrectable
      hweight hradius i.1 j.1 i.2 j.2 hsyndrome

end StabilizerCode
end Coding
end QEC
