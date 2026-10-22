import Mathlib.Algebra.Polynomial.Reverse

/-!
# Bounded inner polynomial reflection

Reflect every inner coefficient at one common degree while preserving the outer root variable. The actual reciprocal evaluation identity and leading coefficient prove root transport and monicity; these are used by the original E4 denominator equation.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]

/-- Reflect every inner coefficient at one fixed degree, keeping the outer polynomial variable. -/
def reflectCoefficients (m : ℕ) (Φ : Polynomial (Polynomial k)) :
    Polynomial (Polynomial k) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Φ.toFinsupp.coeff.mapRange (Polynomial.reflect m) Polynomial.reflect_zero))

/-- The constructed reflection has exactly the reflected inner coefficient at every outer index. -/
lemma reflectCoefficients_coeff (m : ℕ) (Φ : Polynomial (Polynomial k)) (i : ℕ) :
    (reflectCoefficients m Φ).coeff i = (Φ.coeff i).reflect m := by
  rfl

/-- Inner reflection cannot increase the degree in the unchanged outer variable. -/
lemma reflectCoefficients_degree (m r : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : Φ.natDegree ≤ r) : (reflectCoefficients m Φ).natDegree ≤ r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [reflectCoefficients_coeff, Polynomial.natDegree_le_iff_coeff_eq_zero.mp hΦ i hi,
    Polynomial.reflect_zero]

/-- At reciprocal nonzero coordinates, the reflected coefficient evaluation recovers the original polynomial after multiplying by the common power. -/
lemma reflectCoefficients_map (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z : k) (hz : z ≠ 0) :
    (reflectCoefficients m Φ).map (Polynomial.evalRingHom z⁻¹) * Polynomial.C (z^m) =
      Φ.map (Polynomial.evalRingHom z) := by
  let : Invertible z := invertibleOfNonzero hz
  ext i
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, reflectCoefficients_coeff,
    Polynomial.coeff_map]
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval₂_id, invOf_eq_inv] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id k) z m (Φ.coeff i) (hΦ i)

/-- The genuine reciprocal reflection identity transports an actual scalar root. -/
lemma reflectCoefficients_root (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z t : k) (hz : z ≠ 0)
    (ht : Φ.eval₂ (Polynomial.evalRingHom z) t = 0) :
    (reflectCoefficients m Φ).eval₂ (Polynomial.evalRingHom z⁻¹) t = 0 := by
  have he := congrArg (fun Q : Polynomial k => Q.eval t)
    (reflectCoefficients_map m Φ hΦ z hz)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    Polynomial.eval_map, ht] at he
  exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hz)

/-- The reflected top coefficient of a common-power leading term is one, so the outer polynomial is monic. -/
lemma reflectCoefficients_monic (m r : ℕ) (Φ : Polynomial (Polynomial k))
    (hdegree : Φ.natDegree ≤ r)
    (htop : Φ.coeff r = Polynomial.X^m) :
    (reflectCoefficients m Φ).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one r
  · exact reflectCoefficients_degree m r Φ hdegree
  · rw [reflectCoefficients_coeff, htop, Polynomial.reflect_monomial]
    simp


/-- The common-power reflection identity also holds after an actual coefficient field map. -/
lemma reflectCoefficients_map_field {L : Type*} [Field L]
    (φ : k →+* L) (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z : L) (hz : z ≠ 0) :
    (reflectCoefficients m Φ).map (Polynomial.eval₂RingHom φ z⁻¹) * Polynomial.C (z^m) =
      Φ.map (Polynomial.eval₂RingHom φ z) := by
  let : Invertible z := invertibleOfNonzero hz
  ext i
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, reflectCoefficients_coeff,
    Polynomial.coeff_map]
  simpa only [Polynomial.coe_eval₂RingHom, invOf_eq_inv] using
    Polynomial.eval₂_reflect_mul_pow φ z m (Φ.coeff i) (hΦ i)

/-- The actual field-mapped reflection identity transports a root through the reciprocal base coordinate. -/
lemma reflectCoefficients_root_field {L : Type*} [Field L]
    (φ : k →+* L) (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z t : L) (hz : z ≠ 0)
    (ht : Φ.eval₂ (Polynomial.eval₂RingHom φ z) t = 0) :
    (reflectCoefficients m Φ).eval₂ (Polynomial.eval₂RingHom φ z⁻¹) t = 0 := by
  have he := congrArg (fun Q : Polynomial L => Q.eval t)
    (reflectCoefficients_map_field φ m Φ hΦ z hz)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    Polynomial.eval_map, ht] at he
  exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hz)

end
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
