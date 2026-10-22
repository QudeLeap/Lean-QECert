import QEC.Coding.AlgebraicGeometry.Towers.ClosureCanonicalDifferential
import QEC.Coding.AlgebraicGeometry.Towers.ClosureFullConstants
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Theorem

/-!
# The intrinsic genus of the actual source normal closure

The genus is the existing Riemann--Roch invariant of the constructed field.
Its value is derived from the actual canonical divisor and fibre degrees.
-/

namespace QEC.Coding.AlgebraicGeometry

theorem canonicalDivisor_degree_of_constantAlgebra_eq
    (k F : Type*) [Field k] [Finite k] [Field F]
    [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [κ : Algebra k F] [IsScalarTower k (RatFunc k) F]
    [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    {D : Divisor (GlobalPlace k F)}
    (hD : FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F) D) :
    Divisor.degree (GlobalPlace.residueDegree (κ := κ)) D =
      2 * (GlobalPlace.functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 2 := by
  subst κ
  exact CanonicalDivisor.degree_eq_two_mul_genus_sub_two k F hD

namespace F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

def sourceClosureGenus (m : ℕ) : ℕ :=
  GlobalPlace.functionFieldGenus F256 (SourceGaloisClosureField m)

theorem sourceClosureCanonicalDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (sourceClosureCanonicalDivisor m) =
      2 * (sourceClosureGenus m : ℤ) - 2 := by
  exact canonicalDivisor_degree_of_constantAlgebra_eq F256 (SourceGaloisClosureField m)
    (sourceClosureDirectConstant_eq m).symm
    (sourceClosureCanonicalDivisor_isCanonical m)

/-- Integer form of the source genus formula, derived from intrinsic
canonical degree and the actual two fibre degrees. -/
theorem sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees (m : ℕ) :
    (sourceClosureGenus m : ℤ) = 1 + (sourceGaloisWRelativeDegree m : ℤ) -
      Divisor.degree GlobalPlace.residueDegree (sourceGaloisWZeroFibreDivisor m) -
      Divisor.degree GlobalPlace.residueDegree (sourceGaloisWInfinityFibreDivisor m) := by
  have hzsmul (a : ℤ) (D : Divisor (GlobalPlace F256 (SourceGaloisClosureField m))) :
      Divisor.degree GlobalPlace.residueDegree (a • D) =
        a * Divisor.degree GlobalPlace.residueDegree D := by
    have h := (Divisor.degreeHom GlobalPlace.residueDegree).map_zsmul a D
    simp only [zsmul_eq_mul] at h
    exact h
  have h := sourceClosureCanonicalDivisor_degree m
  rw [sourceClosureCanonicalDivisor_eq, Divisor.degree_sub, Divisor.degree_add,
    hzsmul, hzsmul, sourceGaloisClosureSelectedDivisor_degree] at h
  have hA := sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree m
  have hB := sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree m
  have hN : (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) =
      sourceGaloisClosureSelectedLength m := by
    exact_mod_cast sourceGaloisWRelativeDegree_mul_fifteen m
  nlinarith

/-- The paper's rational genus formula for the constructed normal closure,
with n the cardinality of its actual selected rational-place enumeration. -/
theorem sourceClosureGenus_eq_source_formula (m : ℕ) :
    (sourceClosureGenus m : ℚ) = 1 + (sourceGaloisClosureSelectedLength m : ℚ) / 15 *
      (1 - 1 / (sourceGaloisWZeroRamificationIndex m : ℚ) -
        1 / (sourceGaloisWInfinityRamificationIndex m : ℚ)) := by
  have hg : (sourceClosureGenus m : ℚ) = 1 + (sourceGaloisWRelativeDegree m : ℚ) -
      (Divisor.degree GlobalPlace.residueDegree (sourceGaloisWZeroFibreDivisor m) : ℚ) -
      (Divisor.degree GlobalPlace.residueDegree (sourceGaloisWInfinityFibreDivisor m) : ℚ) := by
    exact_mod_cast sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees m
  have hα : (sourceGaloisWZeroRamificationIndex m : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sourceGaloisWZeroRamificationIndex_pos m))
  have hβ : (sourceGaloisWInfinityRamificationIndex m : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sourceGaloisWInfinityRamificationIndex_pos m))
  have hA : (sourceGaloisWZeroRamificationIndex m : ℚ) *
      (Divisor.degree GlobalPlace.residueDegree (sourceGaloisWZeroFibreDivisor m) : ℚ) =
        sourceGaloisWRelativeDegree m := by
    exact_mod_cast sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree m
  have hB : (sourceGaloisWInfinityRamificationIndex m : ℚ) *
      (Divisor.degree GlobalPlace.residueDegree (sourceGaloisWInfinityFibreDivisor m) : ℚ) =
        sourceGaloisWRelativeDegree m := by
    exact_mod_cast sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree m
  have hAdiv : (Divisor.degree GlobalPlace.residueDegree (sourceGaloisWZeroFibreDivisor m) : ℚ) =
      (sourceGaloisWRelativeDegree m : ℚ) / sourceGaloisWZeroRamificationIndex m := by
    apply (eq_div_iff hα).mpr
    simpa only [mul_comm] using hA
  have hBdiv : (Divisor.degree GlobalPlace.residueDegree (sourceGaloisWInfinityFibreDivisor m) : ℚ) =
      (sourceGaloisWRelativeDegree m : ℚ) / sourceGaloisWInfinityRamificationIndex m := by
    apply (eq_div_iff hβ).mpr
    simpa only [mul_comm] using hB
  have hN : (sourceGaloisClosureSelectedLength m : ℚ) / 15 = sourceGaloisWRelativeDegree m := by
    apply (div_eq_iff (by norm_num : (15 : ℚ) ≠ 0)).mpr
    have h : (15 : ℚ) * (sourceGaloisWRelativeDegree m : ℚ) =
        sourceGaloisClosureSelectedLength m := by
      exact_mod_cast sourceGaloisWRelativeDegree_mul_fifteen m
    simpa only [mul_comm] using h.symm
  rw [hg, hAdiv, hBdiv, hN]
  ring

end

end F256GarciaStichtenoth

end QEC.Coding.AlgebraicGeometry
