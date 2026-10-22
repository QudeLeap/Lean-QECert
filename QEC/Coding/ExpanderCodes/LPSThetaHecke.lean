import QEC.Coding.ExpanderCodes.LPSHeckeCoefficients
import QEC.Coding.ExpanderCodes.LPSThetaCuspidalRemainder

/-!
# Original LPS theta coefficients through the actual Hecke action

Instantiate the genuine prime-away-level operator on the existing original theta
cusp remainder at Gamma0((4*q)^2), using the proved original residue-prime
coprimality. Its prime-power first coefficient is exactly the original cusp
coefficient. The centered trace retains the original PSL cardinality and signed
2*(-p)^n term. No eigenvalue/coefficient bound or public PK22 theorem is proved;
parent #449 and pk-good-qldpc remain open and unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The actual prime-power operator applied to the original LPS theta cusp remainder. -/
noncomputable def lpsThetaHeckePrimePower (p : ℕ) (a : LPSResiduePrime p) (r : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 := by
  letI : Fact p.Prime := ⟨a.degreePrime⟩
  have hNp : p.Coprime ((4*a.q)^2) := by
    convert a.coprime_thetaLevel using 1
    ring
  exact lpsHeckePrimePowerLinearMap ((4*a.q)^2) p hNp r
    (lpsThetaCuspidalRemainder a.q a.modFour)

/-- The original theta prime-power coefficient is recovered by the true operator first coefficient. -/
lemma coeff_one_lpsThetaHeckePrimePower (p : ℕ) (a : LPSResiduePrime p) (r : ℕ) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsThetaHeckePrimePower p a r))=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder a.q a.modFour)) := by
  let : Fact p.Prime := ⟨a.degreePrime⟩
  unfold lpsThetaHeckePrimePower
  exact coeff_one_lpsHeckePrimePowerLinearMap _ p _ r _

/-- The original centered trace is exactly the true Hecke-action coefficient with the original cardinality and signed term. -/
lemma lpsCenteredThetaResidual_even_eq_hecke_coefficient (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
          (lpsThetaHeckePrimePower p a (2*n)))).re+2*(-(p:ℝ))^n := by
  rw [coeff_one_lpsThetaHeckePrimePower]
  exact lpsCenteredThetaResidual_even_eq_cuspidal_coefficient p a n


end QEC.Coding.TannerLiftedProduct
