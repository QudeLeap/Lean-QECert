import QEC.Coding.ExpanderCodes.JacobiFourSquareIdentity

/-!
# Exact LPS quaternion-shell count

This module applies the proved Jacobi four-square identity to the existing
coefficient/shell equivalence.  It removes the last arithmetic hypothesis
from the normalized LPS generator count.
-/

namespace QEC.Coding.TannerLiftedProduct

/-- A prime congruent to one modulo four has exactly `8 (p + 1)` ordered,
signed integral four-square representations. -/
theorem card_lpsQuaternionFullShell_eq_prime
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsQuaternionFullShell p).card = 8 * (p + 1) :=
  card_lpsQuaternionFullShell_eq_prime_of_theta_identity hp hp4
    integerThetaSeries_pow_four_eq_jacobiFourSquareSeries

/-- The normalized integral quaternion shell used by the LPS construction
has exactly `p + 1` elements. -/
theorem card_lpsQuaternionShell_eq_prime_add_one
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsQuaternionShell p).card = p + 1 :=
  card_lpsQuaternionShell_eq_prime_add_one_of_theta_identity hp hp4
    integerThetaSeries_pow_four_eq_jacobiFourSquareSeries

end QEC.Coding.TannerLiftedProduct
