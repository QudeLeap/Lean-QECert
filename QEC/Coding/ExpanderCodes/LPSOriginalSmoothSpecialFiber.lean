import QEC.Coding.ExpanderCodes.LPSOriginalReducedSpecialFiber
import QEC.Coding.ExpanderCodes.LPSOriginalSpecialFibreFlat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# LPSOriginalSmoothSpecialFiber

The literal original special fibre has a dense, nonempty smooth open over
its perfect prime field whenever p does not divide the positive level N.
The open is the actual smooth locus of the SAME original fibre projection;
its finite presentation and nonempty whole fibre are already proved. The
new whole-fibre reducedness supplies density. Restriction to this open is
proved smooth, without assuming any good-model or smoothness conclusion.

This internal arithmetic prerequisite supports the original LPS route behind
pinned PK22 ex:Xpq, main.tex:484-486, and the exact th:qLDPC statement at
main.tex:231-238. The source locator is route context, not a claim that these
scheme-theoretic deductions are separately stated there. Global smooth/good
reduction of the complete fibres, Hecke/Frobenius/Weil identities, the LPS
spectral bound and the exact arbitrary-finite-field quantum family remain
unproved. This module establishes only the stated internal arithmetic result.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory

def lpsOriginalSpecialFibreSmoothLocus
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalSpecialFibre p N hN).Opens :=
  letI := lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation p N hN
  (lpsOriginalSpecialFibreToPrimeField p N hN).smoothLocus

lemma lpsOriginalSpecialFibreSmoothLocus_dense
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    Dense (lpsOriginalSpecialFibreSmoothLocus p N hN :
      Set (lpsOriginalSpecialFibre p N hN)) := by
  let := lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation p N hN
  let := lpsOriginalSpecialFibre_reduced N hN p hpN
  exact Scheme.Hom.dense_smoothLocus_of_perfectField
    (lpsOriginalSpecialFibreToPrimeField p N hN)

lemma lpsOriginalSpecialFibre_exists_smoothPoint
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    ∃ x : lpsOriginalSpecialFibre p N hN,
      x ∈ lpsOriginalSpecialFibreSmoothLocus p N hN := by
  let := lpsOriginalSpecialFibre_nonempty p N hN
  exact (lpsOriginalSpecialFibreSmoothLocus_dense p N hN hpN).nonempty

def lpsOriginalSpecialFibreSmoothOpenToPrimeField
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalSpecialFibreSmoothLocus p N hN).toScheme ⟶ Spec (.of (ZMod p)) :=
  (lpsOriginalSpecialFibreSmoothLocus p N hN).ι ≫
    lpsOriginalSpecialFibreToPrimeField p N hN

lemma lpsOriginalSpecialFibreSmoothOpenToPrimeField_smooth
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    Smooth (lpsOriginalSpecialFibreSmoothOpenToPrimeField p N hN) := by
  let := lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation p N hN
  let U := lpsOriginalSpecialFibreSmoothLocus p N hN
  change Smooth (U.ι ≫ lpsOriginalSpecialFibreToPrimeField p N hN)
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact U.ι_preimage_self

lemma lpsOriginalSpecialFibreSmoothOpen_nonempty
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    Nonempty (lpsOriginalSpecialFibreSmoothLocus p N hN).toScheme := by
  obtain ⟨x, hx⟩ := lpsOriginalSpecialFibre_exists_smoothPoint p N hN hpN
  exact ⟨⟨x, hx⟩⟩

end
end QEC.Coding.TannerLiftedProduct
