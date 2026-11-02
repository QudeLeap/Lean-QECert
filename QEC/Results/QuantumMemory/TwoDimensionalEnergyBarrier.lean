import QEC.Coding.Stabilizer.TwoDimensional.StripLogicalPath

/-!
# Bravyi--Terhal two-dimensional constant energy barrier

This module assembles the source-audited BT09 Theorem 2 route.  Large lattices
use alternating-strip cleaning followed by the explicit row-major path.
The finitely many lattice sizes below the strip threshold use the same exact
row-major path with a full-lattice participation count.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian

open PauliSymplectic
open scoped Classical

universe u

variable {κ : Type u} [Fintype κ]

/--
BT09 Theorem 2, in the selected-generator and single-qubit-walk conventions.

The disjunction is exactly the audited open/periodic boundary split.  The
explicit bound depends only on the common range upper bound and the recorded
qubit-participation bound, never on `L`.
-/
theorem bt09_two_dimensional_constant_energy_barrier
    {L r : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hr : 2 ≤ r)
    (hBoundary :
      (StripGeometry.HasOpenIntervalGeneratorSupport H r ∧
        StripGeometry.HasOpenRowIntervalGeneratorSupport H r) ∨
      (StripGeometry.HasPeriodicIntervalGeneratorSupport H r ∧
        StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r))
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    H.logicalEnergyBarrier ≤
      8 * r ^ 4 * H.participationBound := by
  by_cases hLarge : 2 * (r - 1) ^ 2 ≤ L
  · have hrOne : 1 ≤ r := by omega
    have hrrOne : 1 ≤ r * r := by
      simpa using Nat.mul_le_mul hrOne hrOne
    have hrrLePow : r * r ≤ r ^ 4 := by
      calc
        r * r = (r * r) * 1 := by simp
        _ ≤ (r * r) * (r * r) :=
          Nat.mul_le_mul_left (r * r) hrrOne
        _ = r ^ 4 := by ring
    rcases hBoundary with hOpen | hPeriodic
    · obtain ⟨start, width, hwidth, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩ :=
        H.exists_bt09_open_strip_logical_of_two_le_range
          hr hLarge hOpen.1 P hPNormalizer hPNontrivial
      have hwidthLe : width ≤ r := by
        rcases hwidth with rfl | rfl <;> omega
      obtain ⟨γ, _hEndpoint, hLogical, hHeight⟩ :=
        H.exists_open_rowMajor_logical_path
          hL hwidthLe hOpen.2 Q hQNormalizer hQNontrivial hQSupport
      exact
        (H.logicalEnergyBarrier_le_pathHeight γ hLogical).trans
          (hHeight.trans (by
            apply Nat.mul_le_mul_right H.participationBound
            calc
              2 * r * r = 2 * (r * r) := by ring
              _ ≤ 2 * r ^ 4 := Nat.mul_le_mul_left 2 hrrLePow
              _ ≤ 8 * r ^ 4 := by omega))
    · obtain ⟨start, width, hwidth, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩ :=
        H.exists_bt09_periodic_strip_logical_of_two_le_range
          hr hLarge hPeriodic.1 P hPNormalizer hPNontrivial
      have hwidthLe : width ≤ r := by
        rcases hwidth with rfl | rfl <;> omega
      obtain ⟨γ, _hEndpoint, hLogical, hHeight⟩ :=
        H.exists_periodic_rowMajor_logical_path
          hL hwidthLe hPeriodic.2 Q hQNormalizer hQNontrivial hQSupport
      exact
        (H.logicalEnergyBarrier_le_pathHeight γ hLogical).trans
          (hHeight.trans (by
            apply Nat.mul_le_mul_right H.participationBound
            calc
              4 * r * r = 4 * (r * r) := by ring
              _ ≤ 4 * r ^ 4 := Nat.mul_le_mul_left 4 hrrLePow
              _ ≤ 8 * r ^ 4 := by omega))
  · let γ := StripGeometry.rowMajorExactPath P
    have hLogical : H.HasLogicalEndpoint γ := by
      change
        H.code.1.InBinaryNormalizer γ.endpoint ∧
          ¬ H.code.1.InGeneratedGroupUpToSign γ.endpoint
      rw [show γ.endpoint = P by
        exact StripGeometry.rowMajorExactPath_endpoint P]
      exact ⟨hPNormalizer, hPNontrivial⟩
    have hNaive :
        H.pathHeight γ ≤
          2 * (L * L) * H.participationBound :=
      H.pathHeight_rowMajorExactPath_le_full_lattice P
    have hLBound : L ≤ 2 * r * r := by
      push Not at hLarge
      have hsub : r - 1 ≤ r := Nat.sub_le r 1
      have hsq : (r - 1) * (r - 1) ≤ r * r :=
        Nat.mul_le_mul hsub hsub
      calc
        L ≤ 2 * (r - 1) ^ 2 := hLarge.le
        _ ≤ 2 * (r * r) := by
          exact Nat.mul_le_mul_left 2 (by simpa [pow_two] using hsq)
        _ = 2 * r * r := by ring
    have hSquare : L * L ≤ (2 * r * r) * (2 * r * r) :=
      Nat.mul_le_mul hLBound hLBound
    have hCoefficient : 2 * (L * L) ≤ 8 * r ^ 4 := by
      calc
        2 * (L * L) ≤ 2 * ((2 * r * r) * (2 * r * r)) :=
          Nat.mul_le_mul_left 2 hSquare
        _ = 8 * r ^ 4 := by ring
    exact
      (H.logicalEnergyBarrier_le_pathHeight γ hLogical).trans
        (hNaive.trans (by
          exact Nat.mul_le_mul_right H.participationBound hCoefficient))

end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC
