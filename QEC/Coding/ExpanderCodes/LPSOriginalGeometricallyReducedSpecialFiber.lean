import QEC.Coding.AlgebraicGeometry.Schemes.PrimeReducedBaseChange
import QEC.Coding.ExpanderCodes.LPSOriginalReducedSpecialFiber

/-!
# Geometrically reduced original special fibre

For every prime p not dividing the positive level N, the SAME original
special-fibre projection is geometrically reduced. Apply prime-field scalar
extension to its already proved ordinary reducedness. The literal pullback
along every morphism Spec K to Spec F_p is therefore reduced.

This internal arithmetic deduction supports the original LPS route in
pinned PK22 main.tex ex:Xpq:484–486 and th:qLDPC:231–238. Whole-fibre normality
and smoothness, global good reduction, Hecke/Weil/LPS spectral bounds and the
full explicit quantum family remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

lemma lpsOriginalSpecialFibreToPrimeField_geometricallyReduced
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) :
    GeometricallyReduced (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  let := lpsOriginalSpecialFibre_reduced N hN p hpN
  exact QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange.primeFieldMorphism_geometricallyReduced
    p (lpsOriginalSpecialFibre p N hN) (lpsOriginalSpecialFibreToPrimeField p N hN)

lemma lpsOriginalSpecialFibre_fieldPullback_reduced
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N)
    (hpN : ¬ p ∣ N) (K : Type) [Field K]
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalSpecialFibreToPrimeField p N hN) g) := by
  let := lpsOriginalSpecialFibreToPrimeField_geometricallyReduced p N hN hpN
  exact GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)

end
end QEC.Coding.TannerLiftedProduct
