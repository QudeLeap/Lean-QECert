import QEC.Coding.CSS.ParityChecks
import QEC.Coding.Stabilizer.Distance

/-!
# Semantic distance of binary CSS stabilizers

This module relates the independently semantic stabilizer distance to attained
relative logical distances for the CSS code constructed from parity checks. It
also derives the ordinary classical-distance formula under a strict structural
purity condition on the generated stabilizer group.
-/

noncomputable section

namespace QEC
namespace Coding

open Classical

universe u v

namespace PauliSymplectic

variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]

/-- The attained least weight in the X-logical sector `ker P \ im Q^T`. -/
def CSSXLogicalMinimumDistance
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (d : Nat) : Prop :=
  RelativeMinimumDistance (parityCheckKernelCode P) (parityCheckRowCode Q) d

/-- The attained least weight in the Z-logical sector `ker Q \ im P^T`. -/
def CSSZLogicalMinimumDistance
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (d : Nat) : Prop :=
  RelativeMinimumDistance (parityCheckKernelCode Q) (parityCheckRowCode P) d

/--
Normalizer membership for the parity-check CSS code is exactly componentwise
membership in `ker P` and `ker Q`, preserving the P/Z and Q/X orientation.
-/
theorem inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InBinaryNormalizer E ↔
      E.vector.xPart ∈ (parityCheckKernelCode P).carrier ∧
      E.vector.zPart ∈ (parityCheckKernelCode Q).carrier := by
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  constructor
  · intro hnormalizer
    constructor
    · rw [← parityCheckRowCode_dual_eq_kernelCode P]
      refine ((parityCheckRowCode P).mem_dual E.vector.xPart).2 ?_
      intro z hz
      have hcheck : cssZCheck z ∈ C.stabilizers := by
        exact Or.inr ⟨z, hz, rfl⟩
      have hgenerated := mem_generatedGroup_of_mem_stabilizers C hcheck
      have hcommutes := hnormalizer (cssZCheck z) hgenerated
      simpa [Commutes, symplecticForm, wordPairing_apply, dotProduct] using hcommutes
    · rw [← parityCheckRowCode_dual_eq_kernelCode Q]
      refine ((parityCheckRowCode Q).mem_dual E.vector.zPart).2 ?_
      intro x hx
      have hcheck : cssXCheck x ∈ C.stabilizers := by
        exact Or.inl ⟨x, hx, rfl⟩
      have hgenerated := mem_generatedGroup_of_mem_stabilizers C hcheck
      have hcommutes := hnormalizer (cssXCheck x) hgenerated
      simpa [Commutes, symplecticForm, wordPairing_apply, dotProduct,
        Finset.sum_neg_distrib] using hcommutes
  · rintro ⟨hxKernel, hzKernel⟩ S hS
    have hxDual : E.vector.xPart ∈ (parityCheckRowCode P).dual.carrier := by
      simpa [parityCheckRowCode_dual_eq_kernelCode P] using hxKernel
    have hzDual : E.vector.zPart ∈ (parityCheckRowCode Q).dual.carrier := by
      simpa [parityCheckRowCode_dual_eq_kernelCode Q] using hzKernel
    have hdual : (parityCheckRowCode P).carrier ≤
        (parityCheckRowCode Q).dual.carrier :=
      (parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).1 horth
    have hcomponents :
        S.vector.xPart ∈ (parityCheckRowCode Q).carrier ∧
        S.vector.zPart ∈ (parityCheckRowCode P).carrier := by
      have hfull :=
        binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
          (parityCheckRowCode Q) (parityCheckRowCode P) hdual
          (P := S) (by
            exact hS)
      exact ⟨hfull.2.1, hfull.2.2⟩
    have hxPair : wordPairing E.vector.xPart S.vector.zPart = 0 :=
      ((parityCheckRowCode P).mem_dual E.vector.xPart).1 hxDual
        S.vector.zPart hcomponents.2
    have hzPair : wordPairing E.vector.zPart S.vector.xPart = 0 :=
      ((parityCheckRowCode Q).mem_dual E.vector.zPart).1 hzDual
        S.vector.xPart hcomponents.1
    simpa [Commutes, symplecticForm, wordPairing_apply, dotProduct] using
      sub_eq_zero.mpr (by
        rw [show (∑ i, E.vector.xPart i * S.vector.zPart i) = 0 by
          simpa [wordPairing_apply, dotProduct] using hxPair]
        rw [show (∑ i, E.vector.zPart i * S.vector.xPart i) = 0 by
          simpa [wordPairing_apply, dotProduct, mul_comm] using hzPair])

/--
Generated-group membership up to the stored sign is exactly componentwise
membership in the Q-row/X and P-row/Z codes.
-/
theorem inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InGeneratedGroupUpToSign E ↔
      E.vector.xPart ∈ (parityCheckRowCode Q).carrier ∧
      E.vector.zPart ∈ (parityCheckRowCode P).carrier := by
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  let hdual : (parityCheckRowCode P).carrier ≤
      (parityCheckRowCode Q).dual.carrier :=
    (parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).1 horth
  constructor
  · rintro ⟨S, hS, hvector⟩
    have hcomponents :=
      binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
        (parityCheckRowCode Q) (parityCheckRowCode P) hdual
        (P := S) (by
          exact hS)
    change E.vector = S.vector at hvector
    rw [hvector]
    exact ⟨hcomponents.2.1, hcomponents.2.2⟩
  · rintro ⟨hx, hz⟩
    have hxGenerated :
        GeneratedStabilizer (binaryCSSParityCheckGenerators P Q)
          (cssXCheck E.vector.xPart) :=
      binaryCSSParityCheckGenerators_generate_cssXCheck P Q hx
    have hzGenerated :
        GeneratedStabilizer (binaryCSSParityCheckGenerators P Q)
          (cssZCheck E.vector.zPart) :=
      binaryCSSParityCheckGenerators_generate_cssZCheck P Q hz
    refine ⟨binaryMul (cssXCheck E.vector.xPart) (cssZCheck E.vector.zPart), ?_, ?_⟩
    · rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
      exact GeneratedStabilizer.mul hxGenerated hzGenerated
    · simp [BinaryUpToSign, binaryMul]

/--
Strict purity at a threshold: every nonidentity binary Pauli represented in the
actual generated stabilizer up to sign has weight strictly above the threshold.
-/
def StrictGeneratedGroupPurity
    (C : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (threshold : Nat) : Prop :=
  ∀ E : Binary ι,
    C.InGeneratedGroupUpToSign E →
    ¬ BinaryUpToSign E binaryOne →
    threshold < weight E

end PauliSymplectic

namespace StabilizerCode

open PauliSymplectic

variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]

/--
The semantic distance of a source-valid parity-check CSS code is the minimum
of its two attained relative logical-sector distances.
-/
theorem binaryCSSStabilizerDistance_eq_min_logicalDistances
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {dX dZ : Nat}
    (hX : CSSXLogicalMinimumDistance P Q dX)
    (hZ : CSSZLogicalMinimumDistance P Q dZ) :
    SemanticStabilizerDistance
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) (min dX dZ) := by
  rw [semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff]
  rcases hX with ⟨x, hxKernel, hxOutside, hxWeight, hxLeast⟩
  rcases hZ with ⟨z, hzKernel, hzOutside, hzWeight, hzLeast⟩
  rcases le_total dX dZ with hXZ | hZX
  · refine ⟨cssXCheck x, ?_, ?_, ?_, ?_⟩
    · exact
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssXCheck x)).2
          ⟨hxKernel, (parityCheckKernelCode Q).carrier.zero_mem⟩
    · intro hgenerated
      have hcomponents :=
        (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssXCheck x)).1 hgenerated
      exact hxOutside hcomponents.1
    · simpa [Nat.min_eq_left hXZ] using
        (weight_cssXCheck_eq_hammingWeight x).trans hxWeight
    · intro F hnormalizer houtside
      have hnormalizerComponents :=
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth F).1 hnormalizer
      have houtsideComponents :
          F.vector.xPart ∉ (parityCheckRowCode Q).carrier ∨
          F.vector.zPart ∉ (parityCheckRowCode P).carrier := by
        by_contra hnot
        push Not at hnot
        exact houtside
          ((inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth F).2 hnot)
      rw [Nat.min_eq_left hXZ]
      rcases houtsideComponents with hxF | hzF
      · exact (hxLeast F.vector.xPart hnormalizerComponents.1 hxF).trans
          (hammingWeight_xPart_le_weight F)
      · exact hXZ.trans ((hzLeast F.vector.zPart hnormalizerComponents.2 hzF).trans
          (hammingWeight_zPart_le_weight F))
  · refine ⟨cssZCheck z, ?_, ?_, ?_, ?_⟩
    · exact
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssZCheck z)).2
          ⟨(parityCheckKernelCode P).carrier.zero_mem, hzKernel⟩
    · intro hgenerated
      have hcomponents :=
        (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssZCheck z)).1 hgenerated
      exact hzOutside hcomponents.2
    · simpa [Nat.min_eq_right hZX] using
        (weight_cssZCheck_eq_hammingWeight z).trans hzWeight
    · intro F hnormalizer houtside
      have hnormalizerComponents :=
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth F).1 hnormalizer
      have houtsideComponents :
          F.vector.xPart ∉ (parityCheckRowCode Q).carrier ∨
          F.vector.zPart ∉ (parityCheckRowCode P).carrier := by
        by_contra hnot
        push Not at hnot
        exact houtside
          ((inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth F).2 hnot)
      rw [Nat.min_eq_right hZX]
      rcases houtsideComponents with hxF | hzF
      · exact hZX.trans ((hxLeast F.vector.xPart hnormalizerComponents.1 hxF).trans
          (hammingWeight_xPart_le_weight F))
      · exact (hzLeast F.vector.zPart hnormalizerComponents.2 hzF).trans
          (hammingWeight_zPart_le_weight F)

/--
Under strict generated-group purity at the ordinary threshold, the semantic
CSS distance is the minimum of the two ordinary nonzero kernel-code distances.
-/
theorem binaryCSSStabilizerDistance_eq_min_classicalDistances_of_strictPurity
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {dP dQ : Nat}
    (hP : MinimumDistance (parityCheckKernelCode P) dP)
    (hQ : MinimumDistance (parityCheckKernelCode Q) dQ)
    (hPurity : StrictGeneratedGroupPurity
      (binaryCSSStabilizerCodeOfParityChecks P Q horth) (min dP dQ)) :
    SemanticStabilizerDistance
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) (min dP dQ) := by
  rw [semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff]
  rcases hP with ⟨x, hxKernel, hxNonzero, hxWeight, hxLeast⟩
  rcases hQ with ⟨z, hzKernel, hzNonzero, hzWeight, hzLeast⟩
  rcases le_total dP dQ with hPQ | hQP
  · refine ⟨cssXCheck x, ?_, ?_, ?_, ?_⟩
    · exact
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssXCheck x)).2
          ⟨hxKernel, (parityCheckKernelCode Q).carrier.zero_mem⟩
    · intro hgenerated
      have hnonidentity : ¬ BinaryUpToSign (cssXCheck x) binaryOne := by
        intro hidentity
        change (cssXCheck x).vector = binaryOne.vector at hidentity
        exact hxNonzero (by
          simpa [binaryOne] using congrArg SymplecticVector.xPart hidentity)
      have hpure := hPurity (cssXCheck x) hgenerated hnonidentity
      have hpure' : min dP dQ < HammingWeight x := by
        simpa using hpure
      have : dP < dP := by
        rw [hxWeight, Nat.min_eq_left hPQ] at hpure'
        exact hpure'
      exact (Nat.lt_irrefl dP) this
    · simpa [Nat.min_eq_left hPQ] using
        (weight_cssXCheck_eq_hammingWeight x).trans hxWeight
    · intro F hnormalizer houtside
      have hnormalizerComponents :=
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth F).1 hnormalizer
      have houtsideComponents :
          F.vector.xPart ∉ (parityCheckRowCode Q).carrier ∨
          F.vector.zPart ∉ (parityCheckRowCode P).carrier := by
        by_contra hnot
        push Not at hnot
        exact houtside
          ((inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth F).2 hnot)
      rw [Nat.min_eq_left hPQ]
      rcases houtsideComponents with hxOutside | hzOutside
      · have hxFNonzero : F.vector.xPart ≠ 0 := by
          intro hxZero
          apply hxOutside
          rw [hxZero]
          exact (parityCheckRowCode Q).carrier.zero_mem
        exact (hxLeast F.vector.xPart hnormalizerComponents.1 hxFNonzero).trans
          (hammingWeight_xPart_le_weight F)
      · have hzFNonzero : F.vector.zPart ≠ 0 := by
          intro hzZero
          apply hzOutside
          rw [hzZero]
          exact (parityCheckRowCode P).carrier.zero_mem
        exact hPQ.trans ((hzLeast F.vector.zPart hnormalizerComponents.2 hzFNonzero).trans
          (hammingWeight_zPart_le_weight F))
  · refine ⟨cssZCheck z, ?_, ?_, ?_, ?_⟩
    · exact
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssZCheck z)).2
          ⟨(parityCheckKernelCode P).carrier.zero_mem, hzKernel⟩
    · intro hgenerated
      have hnonidentity : ¬ BinaryUpToSign (cssZCheck z) binaryOne := by
        intro hidentity
        change (cssZCheck z).vector = binaryOne.vector at hidentity
        exact hzNonzero (by
          simpa [binaryOne] using congrArg SymplecticVector.zPart hidentity)
      have hpure := hPurity (cssZCheck z) hgenerated hnonidentity
      have hpure' : min dP dQ < HammingWeight z := by
        simpa using hpure
      have : dQ < dQ := by
        rw [hzWeight, Nat.min_eq_right hQP] at hpure'
        exact hpure'
      exact (Nat.lt_irrefl dQ) this
    · simpa [Nat.min_eq_right hQP] using
        (weight_cssZCheck_eq_hammingWeight z).trans hzWeight
    · intro F hnormalizer houtside
      have hnormalizerComponents :=
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth F).1 hnormalizer
      have houtsideComponents :
          F.vector.xPart ∉ (parityCheckRowCode Q).carrier ∨
          F.vector.zPart ∉ (parityCheckRowCode P).carrier := by
        by_contra hnot
        push Not at hnot
        exact houtside
          ((inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth F).2 hnot)
      rw [Nat.min_eq_right hQP]
      rcases houtsideComponents with hxOutside | hzOutside
      · have hxFNonzero : F.vector.xPart ≠ 0 := by
          intro hxZero
          apply hxOutside
          rw [hxZero]
          exact (parityCheckRowCode Q).carrier.zero_mem
        exact hQP.trans ((hxLeast F.vector.xPart hnormalizerComponents.1 hxFNonzero).trans
          (hammingWeight_xPart_le_weight F))
      · have hzFNonzero : F.vector.zPart ≠ 0 := by
          intro hzZero
          apply hzOutside
          rw [hzZero]
          exact (parityCheckRowCode P).carrier.zero_mem
        exact (hzLeast F.vector.zPart hnormalizerComponents.2 hzFNonzero).trans
          (hammingWeight_zPart_le_weight F)

end StabilizerCode
end Coding
end QEC
