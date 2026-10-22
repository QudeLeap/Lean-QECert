import QEC.Coding.ExpanderCodes.LPSCongruenceFiniteDimension
import QEC.Coding.ExpanderCodes.LPSHeckeCoefficients
import QEC.Coding.ExpanderCodes.LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap

/-!
# LPSCuspIntegralHecke

The actual all-integer Fourier coefficient cusp lattice is finite over Z by genuine congruence Sturm. The original Hecke operator preserves it and has a derived monic integer annihilator. Inclusion intertwines actual powers and polynomial action.
No lattice, finite generation, stability, annihilator or integrality conclusion is assumed.
The arithmetic magnitude estimate and public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

/-- All-n actual cusp Fourier coefficient, restricted to integer scalars. -/
def lpsCuspCoefficient (N n : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℤ] ℂ :=
  ((lpsModularForm_coefficientLinearMap N n).comp CuspForm.toModularFormₗ).restrictScalars ℤ

/-- The concrete original cusp lattice with integer coefficients at every exponent. -/
def lpsIntegralCuspLattice (N : ℕ) :
    Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) where
  carrier f := ∀ n, ∃ z : ℤ, lpsCuspCoefficient N n f = (z : ℂ)
  zero_mem' := by intro n; exact ⟨0, by simp⟩
  add_mem' hf hg := by
    intro n
    obtain ⟨a, ha⟩ := hf n
    obtain ⟨b, hb⟩ := hg n
    exact ⟨a+b, by rw [map_add, ha, hb, Int.cast_add]⟩
  smul_mem' z f hf := by
    intro n
    obtain ⟨a, ha⟩ := hf n
    refine ⟨z*a, ?_⟩
    rw [map_smul, ha, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Int.cast_mul]

/-- Actual integer coordinates selected from each true Fourier coefficient. -/
def lpsIntegralCuspCoordinates (N : ℕ) :
    lpsIntegralCuspLattice N →ₗ[ℤ] (Fin (lpsGamma0CoefficientCount N 2) → ℤ) where
  toFun f i := (f.property i.val).choose
  map_add' f g := by
    funext i
    apply Int.cast_injective (α := ℂ)
    simp only [Pi.add_apply]
    rw [Int.cast_add, ← (f.property i.val).choose_spec, ← (g.property i.val).choose_spec,
      ← ((f+g).property i.val).choose_spec]
    exact map_add (lpsCuspCoefficient N i.val) f.val g.val
  map_smul' z f := by
    funext i
    apply Int.cast_injective (α := ℂ)
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [← (f.property i.val).choose_spec, ← ((z • f).property i.val).choose_spec]
    change lpsCuspCoefficient N i.val (z • f.val) =
      ((RingHom.id ℤ) z : ℂ) * lpsCuspCoefficient N i.val f.val
    simpa only [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, RingHom.id_apply] using
      map_smul (lpsCuspCoefficient N i.val) z f.val

/-- The actual selected integer coordinate is exactly the original Fourier coefficient. -/
lemma lpsIntegralCuspCoordinates_cast (N : ℕ) (f : lpsIntegralCuspLattice N)
    (i : Fin (lpsGamma0CoefficientCount N 2)) :
    (lpsIntegralCuspCoordinates N f i : ℂ) = lpsCuspCoefficient N i.val f :=
  (f.property i.val).choose_spec.symm

/-- Genuine congruence Sturm makes the integer coordinate map injective. -/
lemma lpsIntegralCuspCoordinates_injective (N : ℕ) [NeZero N] :
    Function.Injective (lpsIntegralCuspCoordinates N) := by
  intro f g h
  apply Subtype.ext
  apply CuspForm.toModularFormₗ_injective
  apply lpsGamma0FiniteCoefficients_injective N 2
  ext i
  change lpsCuspCoefficient N i.val f = lpsCuspCoefficient N i.val g
  rw [← lpsIntegralCuspCoordinates_cast N f i, ← lpsIntegralCuspCoordinates_cast N g i]
  exact congrArg (fun v => (v i : ℂ)) h

/-- This original all-integer cusp lattice is finite over Z, with no supplied lattice hypothesis. -/
lemma lpsIntegralCuspLattice_finite (N : ℕ) [NeZero N] :
    Module.Finite ℤ (lpsIntegralCuspLattice N) :=
  Module.Finite.of_injective (lpsIntegralCuspCoordinates N) (lpsIntegralCuspCoordinates_injective N)

/-- The true original Hecke coefficient formula preserves actual integrality. -/
lemma lpsCuspHecke_preservesIntegralLattice (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : f ∈ lpsIntegralCuspLattice N) :
    lpsCuspHeckeLinearMap N p hNp f ∈ lpsIntegralCuspLattice N := by
  intro n
  obtain ⟨x, hx⟩ := hf (p*n)
  change PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f) = (x : ℂ) at hx
  change ∃ z : ℤ, PowerSeries.coeff n
    (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f)) = (z : ℂ)
  rw [coeff_qExpansion_lpsCuspHecke, lpsModularDilationCoefficient]
  by_cases hd : p ∣ n
  · obtain ⟨y, hy⟩ := hf (n/p)
    change PowerSeries.coeff (n/p) (UpperHalfPlane.qExpansion 1 f) = (y : ℂ) at hy
    refine ⟨x+(p : ℤ)*y, ?_⟩
    simp only [if_pos hd, hx, hy, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  · exact ⟨x, by simp [hd, hx]⟩

/-- The actual Hecke endomorphism of the concrete original integral cusp lattice. -/
def lpsIntegralCuspHecke (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) :
    Module.End ℤ (lpsIntegralCuspLattice N) where
  toFun f := ⟨lpsCuspHeckeLinearMap N p hNp f,
    lpsCuspHecke_preservesIntegralLattice N p hNp f f.property⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' z f := by
    apply Subtype.ext
    exact map_smul ((lpsCuspHeckeLinearMap N p hNp).restrictScalars ℤ) z f.val

/-- A derived monic integer polynomial annihilates the actual restricted original Hecke operator. -/
lemma lpsIntegralCuspHecke_exists_monic_annihilator (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃ P : ℤ[X], P.Monic ∧ aeval (lpsIntegralCuspHecke N p hNp) P = 0 := by
  let := lpsIntegralCuspLattice_finite N
  exact LinearMap.exists_monic_and_aeval_eq_zero ℤ (lpsIntegralCuspHecke N p hNp)

/-- Inclusion intertwines every power of the actual restricted and original Hecke operators. -/
lemma lpsIntegralCuspHecke_pow_coe (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) (f : lpsIntegralCuspLattice N) :
    (((lpsIntegralCuspHecke N p hNp)^r) f :
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) =
      ((lpsCuspHeckeLinearMap N p hNp)^r) f.val := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change lpsCuspHeckeLinearMap N p hNp
      (((lpsIntegralCuspHecke N p hNp)^r) f :
        CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) = _
    rw [ih]

/-- Inclusion transports every integer polynomial action to the original complex operator. -/
lemma lpsIntegralCuspHecke_polynomial_coe (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (P : ℤ[X]) (f : lpsIntegralCuspLattice N) :
    ((aeval (lpsIntegralCuspHecke N p hNp) P) f :
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) =
      (aeval (lpsCuspHeckeLinearMap N p hNp) (P.map (Int.castRingHom ℂ))) f.val := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hP, hQ]
  | monomial r z =>
    simp only [Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, Submodule.coe_smul,
      ← Int.cast_smul_eq_zsmul ℂ, lpsIntegralCuspHecke_pow_coe]
    rfl

end
end QEC.Coding.TannerLiftedProduct
