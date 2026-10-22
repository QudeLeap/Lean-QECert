import QEC.Coding.ExpanderCodes.LPSOriginalFunctionField
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Actual holomorphic fraction roots

Homogenization extends literal point equations off denominator zeros to an actual fraction-field root. The proved holomorphic integral domain cancels the denominator as a function; raw division identities at its zeros are not assumed.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Evaluate genuine holomorphic functions at one actual upper-half-plane point as a ring map. -/
def lpsOriginalHolomorphicPointEvaluation (τ : ℍ) :
    LPSOriginalHolomorphicRing →+* ℂ where
  toFun f := f.val τ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Actual point equations away from denominator zeros yield a fraction-field root by homogenization and domain cancellation. -/
lemma lpsOriginalHolomorphicFraction_root_of_pointEquations
    (p : Polynomial LPSOriginalHolomorphicRing) (r : ℕ) (hp : p.natDegree ≤ r)
    (A B : LPSOriginalHolomorphicRing) (hB : B ≠ 0)
    (hpoint : ∀ τ : ℍ, B.val τ ≠ 0 →
      p.eval₂ (lpsOriginalHolomorphicPointEvaluation τ)
        (A.val τ / B.val τ) = 0) :
    p.eval₂ (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
      ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField A) /
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField B)) = 0 := by
  classical
  let H := MvPolynomial.eval ![A, B] (p.homogenize r)
  have hHpoint (τ : ℍ) (hb : B.val τ ≠ 0) : H.val τ = 0 := by
    let e := lpsOriginalHolomorphicPointEvaluation τ
    have he : e H = MvPolynomial.eval ![e A, e B] ((p.map e).homogenize r) := by
      dsimp only [H]
      rw [MvPolynomial.map_eval, ← Polynomial.homogenize_map]
      have hv : (e ∘ ![A, B]) = ![e A, e B] := by
        funext i
        fin_cases i <;> rfl
      rw [hv]
    rw [Polynomial.eval_homogenize ((Polynomial.natDegree_map_le).trans hp)
      ![e A, e B] hb, Polynomial.eval_map] at he
    change H.val τ = p.eval₂ (lpsOriginalHolomorphicPointEvaluation τ)
      (A.val τ / B.val τ) * B.val τ^r at he
    rw [hpoint τ hb, zero_mul] at he
    exact he
  have hmul : H * B = 0 := by
    apply Subtype.ext
    funext τ
    change H.val τ * B.val τ = 0
    by_cases hb : B.val τ = 0
    · rw [hb, mul_zero]
    · rw [hHpoint τ hb, zero_mul]
  have hH : H = 0 := (mul_eq_zero.mp hmul).resolve_right hB
  let e := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hb : e B ≠ 0 := fun hz => hB
    ((IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
      (hz.trans (map_zero e).symm))
  have he : e H = MvPolynomial.eval ![e A, e B] ((p.map e).homogenize r) := by
    dsimp only [H]
    rw [MvPolynomial.map_eval, ← Polynomial.homogenize_map]
    have hv : (e ∘ ![A, B]) = ![e A, e B] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
  rw [hH, map_zero, Polynomial.eval_homogenize
    ((Polynomial.natDegree_map_le).trans hp) ![e A, e B] hb,
    Polynomial.eval_map] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (pow_ne_zero r hb)

end
end QEC.Coding.TannerLiftedProduct
