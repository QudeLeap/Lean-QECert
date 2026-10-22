import QEC.Coding.ExpanderCodes.LPSCongruenceFiniteDimension
import QEC.Coding.ExpanderCodes.LPSThetaHecke

/-!
# Congruence Sturm and genuine finite-dimensional Hecke spaces

Internal proof closure for the original PK22 theta route. Fourier width, actual
coset norm and level-one Sturm give a finite coefficient injection at Gamma0(N).
The finite basis and matrices describe the already proved weight-two operators.
The arithmetic spectral bound and public theorem pk-good-qldpc remain unproved;
parent #449 remains open. No spectral or finite-dimensional conclusion is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

/-- The original LPS theta remainder lies in a proved finite-dimensional weight-two cusp space. -/
lemma lpsThetaCuspFiniteDimensional (p : ℕ) (a : LPSResiduePrime p) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) :
      Subgroup (GL (Fin 2) ℝ)) 2) := by
  have hn : NeZero ((4*a.q)^2) := ⟨pow_ne_zero _ (mul_ne_zero (by norm_num) a.prime.ne_zero)⟩
  exact lpsGamma0CuspFiniteDimensional ((4*a.q)^2) 2

end QEC.Coding.TannerLiftedProduct
