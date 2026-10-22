import QEC.Coding.CSS.Syndrome
import QEC.Coding.Stabilizer.Correctability

/-!
# Componentwise correctability of binary CSS codes

This module derives finite-Kraus correctability of the exact parity-check CSS
code from bounded injectivity of the two classical syndrome maps.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PauliSymplectic

universe u v

variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]

omit [DecidableEq iota] in
private theorem binaryUpToSign_of_equal_binaryCSSSyndrome_of_componentwiseBounds
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {tX tZ : Nat}
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    {E F : Binary iota}
    (hE : HammingWeight E.vector.xPart ≤ tX ∧ HammingWeight E.vector.zPart ≤ tZ)
    (hF : HammingWeight F.vector.xPart ≤ tX ∧ HammingWeight F.vector.zPart ≤ tZ)
    (hsyndrome : stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E =
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) F) :
    BinaryUpToSign E F := by
  rw [binaryCSSSyndrome_eq_classicalSyndromes P Q horth E,
    binaryCSSSyndrome_eq_classicalSyndromes P Q horth F] at hsyndrome
  have hxSyndrome : P E.vector.xPart = P F.vector.xPart := by
    funext p
    exact congrFun hsyndrome (Sum.inl p)
  have hzSyndrome : Q E.vector.zPart = Q F.vector.zPart := by
    funext q
    exact congrFun hsyndrome (Sum.inr q)
  have hx : E.vector.xPart = F.vector.xPart :=
    hP E.vector.xPart F.vector.xPart hE.1 hF.1 hxSyndrome
  have hz : E.vector.zPart = F.vector.zPart :=
    hQ E.vector.zPart F.vector.zPart hE.2 hF.2 hzSyndrome
  change E.vector = F.vector
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := iota)).injective
  exact Prod.ext hx hz

private theorem relative_inGeneratedGroupUpToSign_of_binaryUpToSign
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {E F : Binary iota} (hEF : BinaryUpToSign E F) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InGeneratedGroupUpToSign
      (binaryMul (binaryDagger E) F) := by
  refine ⟨binaryOne, ?_, ?_⟩
  · rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
    exact GeneratedStabilizer.one
  · change (binaryMul (binaryDagger E) F).vector = (binaryOne (ι := iota)).vector
    calc
      (binaryMul (binaryDagger E) F).vector =
          (binaryMul (binaryDagger E) E).vector := by
            rcases E with ⟨ephase, evector⟩
            rcases F with ⟨fphase, fvector⟩
            change evector = fvector at hEF
            subst fvector
            rfl
      _ = (binaryOne (ι := iota)).vector := by
        rw [binaryMul_binaryDagger_left]

private theorem relative_not_inBinaryNormalizer_of_binaryCSSSyndrome_ne
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {E F : Binary iota}
    (hsyndrome : stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E ≠
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) F) :
    ¬ (binaryCSSStabilizerCodeOfParityChecks P Q horth).InBinaryNormalizer
      (binaryMul (binaryDagger E) F) := by
  let generators := binaryCSSParityCheckGenerators P Q
  let R := binaryMul (binaryDagger E) F
  have hmaps := stabilizerSyndrome_map_properties generators R E F
  have hrelativeSyndrome : stabilizerSyndrome generators R ≠ 0 := by
    intro hzero
    apply hsyndrome
    apply hmaps.2.1.2
    rw [hmaps.2.2]
    exact hzero
  have hnotGeneratorNormalizer : ¬ InStabilizerNormalizer generators R := by
    intro hnormalizer
    exact hrelativeSyndrome (hmaps.1.2 hnormalizer)
  intro hnormalizer
  apply hnotGeneratorNormalizer
  intro S hS
  apply hnormalizer S
  rw [← binaryCSSParityCheckGenerators_generate_generatedGroup P Q horth]
  exact hS

/--
Separate bounded injectivity of the P-row/Z-check and Q-row/X-check classical
syndrome maps gives the active-support stabilizer pair-product dichotomy for
the exact source-valid parity-check CSS stabilizer.

This is an internal API lemma: it neither assumes nor concludes
Knill-Laflamme, completeness, recovery, or correctability.
-/
theorem binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ) :
    ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth).1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (E a)) (E b)) ∨
        ¬ (binaryCSSSourceValidStabilizerOfParityChecks P Q horth).1.InBinaryNormalizer
          (binaryMul (binaryDagger (E a)) (E b)) := by
  intro a b ha hb
  by_cases hsyndrome :
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (E a) =
        stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (E b)
  · apply Or.inl
    exact relative_inGeneratedGroupUpToSign_of_binaryUpToSign P Q horth
      (binaryUpToSign_of_equal_binaryCSSSyndrome_of_componentwiseBounds
        P Q horth hP hQ (hbound a ha) (hbound b hb) hsyndrome)
  · exact Or.inr
      (relative_not_inBinaryNormalizer_of_binaryCSSSyndrome_ne P Q horth hsyndrome)

omit [DecidableEq iota] in
/--
A nonzero equal-X/Z support word inside both injectivity balls has nonzero
classical syndromes in both sectors, and its CSS syndrome is their tagged pair.
This is the conditional Y-support corollary of [Gott97, Ch. 3, CSS Y-error
two-component scope].
-/
theorem binaryCSSSyndrome_equalXZ_components_ne_zero_of_componentwiseSyndromeInjective
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {tX tZ : Nat}
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (phase : ZMod 2) (y : Word (ZMod 2) iota)
    (hy : y ≠ 0) (hyX : HammingWeight y ≤ tX) (hyZ : HammingWeight y ≤ tZ) :
    P y ≠ 0 ∧ Q y ≠ 0 ∧
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
          ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota) =
        Sum.elim (P y) (Q y) ∧
      (fun p => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota)
        (Sum.inl p)) ≠ 0 ∧
      (fun q => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota)
        (Sum.inr q)) ≠ 0 := by
  have hPy : P y ≠ 0 := by
    intro hzero
    apply hy
    apply hP y 0 hyX (by simp)
    simpa using hzero
  have hQy : Q y ≠ 0 := by
    intro hzero
    apply hy
    apply hQ y 0 hyZ (by simp)
    simpa using hzero
  refine ⟨hPy, hQy, binaryCSSSyndrome_equalXZ P Q horth phase y, ?_, ?_⟩
  · exact (binaryCSSSyndrome_equalXZ_inl_ne_zero_iff P Q horth phase y).2 hPy
  · exact (binaryCSSSyndrome_equalXZ_inr_ne_zero_iff P Q horth phase y).2 hQy

/--
Bounded injectivity of the two classical CSS syndrome maps gives the
same-space Knill-Laflamme criterion for every finite binary-Pauli family whose
active X and Z components obey the corresponding separate bounds.

The conclusion is the exact matrix-element criterion on the actual common
+1 fixed parity-check CSS carrier; it requires neither completeness nor a
recovery channel.
-/
theorem binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ) :
    (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion
      (binaryCSSStabilizerCodeOfParityChecks P Q horth).code := by
  apply
    (StabilizerCode.binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) E amp).2
  exact
    binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
      P Q horth tX tZ hP hQ E amp hbound

/--
Bounded injectivity of the two classical CSS syndrome maps corrects every
complete finite binary-Pauli Kraus family whose active X and Z components obey
the corresponding separate bounds. One M2 recovery witnesses both raw
finite-Kraus correctability and bundled-channel semantic correctability for the
same common-fixed parity-check CSS code and the same family.
-/
theorem binaryCSSParityChecks_exists_finiteKrausCorrectable_and_correctable_toQuantumChannel_of_componentwiseSyndromeInjective
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota),
      Semantics.FiniteKrausCorrectable alpha
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        (binaryPauliKrausFamily E amp) recovery ∧
      Semantics.Correctable
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        ((binaryPauliKrausFamily E amp).toQuantumChannel hcomplete) recovery := by
  obtain ⟨recovery, hcorrectable⟩ :=
    Semantics.FiniteKrausFamily.exists_recovery_of_sameSpaceKnillLaflammeCriterion
      (binaryPauliKrausFamily E amp)
      (binaryCSSStabilizerCodeOfParityChecks P Q horth).code hcomplete
      (binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
        P Q horth tX tZ hP hQ E amp hbound)
  refine ⟨recovery, hcorrectable, ?_⟩
  exact
    ((binaryPauliKrausFamily E amp).correctedBy_iff_correctable_toQuantumChannel
      hcomplete (binaryCSSStabilizerCodeOfParityChecks P Q horth).code recovery).1 hcorrectable.2

/--
Bounded injectivity of the two classical CSS syndrome maps corrects every
complete finite binary-Pauli Kraus family whose active X and Z components obey
the corresponding separate bounds. The conclusion is an actual CPTP recovery
for the exact common-fixed parity-check CSS code. This realizes the derived
semantic bridge from [Gott97, Ch. 3, CSS componentwise X/Z/Y correction scope]
through the support-sensitive stabilizer criterion and Knill-Laflamme recovery.
-/
theorem binaryCSSParityChecks_exists_finiteKrausCorrectable_of_componentwiseSyndromeInjective
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota),
      Semantics.FiniteKrausCorrectable alpha
        (Semantics.Qubit.QubitRegister iota) (Semantics.Qubit.QubitRegister iota)
        (binaryCSSStabilizerCodeOfParityChecks P Q horth).code
        (binaryPauliKrausFamily E amp) recovery := by
  apply
    (StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) E amp hcomplete).2
  exact
    binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
      P Q horth tX tZ hP hQ E amp hbound

end PauliSymplectic
end Coding
end QEC
