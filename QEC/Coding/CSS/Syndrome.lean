import QEC.Coding.CSS.ParityChecks

/-!
# Binary CSS quantum/classical syndrome bridge

This module identifies the finite syndrome of the oriented parity-check CSS
generators with the two classical parity-check syndromes. Rows of `P` remain
Z checks, rows of `Q` remain X checks, and syndrome bits use the ordered
symplectic pairing of the error with the generator.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PauliSymplectic

universe v

variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]

/--
The syndrome of the oriented binary CSS generator family is the tagged pair of
classical `P` and `Q` syndromes. The orthogonality assumption keeps the theorem
in the source-valid CSS setting, while the equality itself is algebraic.
-/
theorem binaryCSSSyndrome_eq_classicalSyndromes
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E =
      Sum.elim (P E.vector.xPart) (Q E.vector.zPart) := by
  classical
  funext j
  cases j with
  | inl p =>
      calc
        stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E (Sum.inl p) =
            wordPairing E.vector.xPart (parityCheckRow P p) := by
              simp [stabilizerSyndrome, stabilizerSyndromeBit,
                binaryCSSParityCheckGenerators, symplecticForm,
                wordPairing_apply, dotProduct]
        _ = wordPairing (parityCheckRow P p) E.vector.xPart := by
              simp [wordPairing_apply, dotProduct_comm]
        _ = wordPairing (Pi.single p 1) (P E.vector.xPart) :=
              wordPairing_wordLinearMapTranspose P (Pi.single p 1) E.vector.xPart
        _ = P E.vector.xPart p := by simp [wordPairing_apply]
        _ = Sum.elim (P E.vector.xPart) (Q E.vector.zPart) (Sum.inl p) := rfl
  | inr q =>
      calc
        stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E (Sum.inr q) =
            -wordPairing E.vector.zPart (parityCheckRow Q q) := by
              simp [stabilizerSyndrome, stabilizerSyndromeBit,
                binaryCSSParityCheckGenerators, symplecticForm,
                wordPairing_apply, dotProduct]
        _ = -wordPairing (parityCheckRow Q q) E.vector.zPart := by
              simp [wordPairing_apply, dotProduct_comm]
        _ = -wordPairing (Pi.single q 1) (Q E.vector.zPart) := by
              exact congrArg Neg.neg
                (wordPairing_wordLinearMapTranspose Q (Pi.single q 1) E.vector.zPart)
        _ = -(Q E.vector.zPart q) := by simp [wordPairing_apply]
        _ = Q E.vector.zPart q := ZMod.neg_eq_self_mod_two _
        _ = Sum.elim (P E.vector.xPart) (Q E.vector.zPart) (Sum.inr q) := rfl

/-- A pure-X error has classical `P` syndrome and zero `Q` syndrome. -/
theorem binaryCSSSyndrome_pureX
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (x : Word (ZMod 2) ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (cssXCheck x) =
      Sum.elim (P x) (0 : Word (ZMod 2) κQ) := by
  simpa using binaryCSSSyndrome_eq_classicalSyndromes P Q horth (cssXCheck x)

/-- A pure-Z error has zero `P` syndrome and classical `Q` syndrome. -/
theorem binaryCSSSyndrome_pureZ
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (z : Word (ZMod 2) ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) (cssZCheck z) =
      Sum.elim (0 : Word (ZMod 2) κP) (Q z) := by
  simpa using binaryCSSSyndrome_eq_classicalSyndromes P Q horth (cssZCheck z)

/--
Equal X/Z coordinates, the binary support representation of Y up to phase,
have the two classical syndromes `(P y, Q y)` for every binary phase.
-/
theorem binaryCSSSyndrome_equalXZ
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι) =
      Sum.elim (P y) (Q y) := by
  simpa using binaryCSSSyndrome_eq_classicalSyndromes P Q horth
    ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι)

/-- The P-row component of an equal-X/Z syndrome is nonzero exactly when `P y` is. -/
theorem binaryCSSSyndrome_equalXZ_inl_ne_zero_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    (fun p => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
      ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι)
      (Sum.inl p)) ≠ 0 ↔ P y ≠ 0 := by
  rw [binaryCSSSyndrome_equalXZ P Q horth phase y]
  rfl

/-- The Q-row component of an equal-X/Z syndrome is nonzero exactly when `Q y` is. -/
theorem binaryCSSSyndrome_equalXZ_inr_ne_zero_iff
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (phase : ZMod 2) (y : Word (ZMod 2) ι) :
    (fun q => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
      ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary ι)
      (Sum.inr q)) ≠ 0 ↔ Q y ≠ 0 := by
  rw [binaryCSSSyndrome_equalXZ P Q horth phase y]
  rfl

end PauliSymplectic
end Coding
end QEC
