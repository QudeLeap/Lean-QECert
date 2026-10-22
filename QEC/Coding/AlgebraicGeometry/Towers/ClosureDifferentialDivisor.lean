import QEC.Coding.AlgebraicGeometry.Towers.ClosureFibreDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Towers.ClosureRegularDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Differentials.CanonicalDifferential

/-!
# The actual divisor of dz on the source normal closure

The two genuine w-fibres and their complement exhaust all places by the
already proved principal divisor of w. The local differential computations
therefore give an equality of intrinsic differential divisors.
-/

open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem sourceClosureWFibreDivisors_disjoint (m : ℕ) :
    Disjoint (sourceGaloisWZeroFibreDivisor m).support
      (sourceGaloisWInfinityFibreDivisor m).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hA hB
  have hA' : Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m) := by
    rw [← sourceGaloisWZeroFibreDivisor_support]
    exact hA
  have hB' : Q ∈ Set.range (sourceGaloisWInfinityPlaceOfPrime m) := by
    rw [← sourceGaloisWInfinityFibreDivisor_support]
    exact hB
  obtain ⟨P, rfl⟩ := hA'
  obtain ⟨S, hS⟩ := hB'
  have h := congrArg (fun R : GlobalPlace F256 (SourceGaloisClosureField m) =>
    R.order (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m)) hS
  rw [sourceGaloisWInfinityPlaceOfPrime_order_generator,
    sourceGaloisWZeroPlaceOfPrime_order_generator] at h
  have hα : (0 : ℤ) < sourceGaloisWZeroRamificationIndex m := by
    exact_mod_cast sourceGaloisWZeroRamificationIndex_pos m
  have hβ : (0 : ℤ) < sourceGaloisWInfinityRamificationIndex m := by
    exact_mod_cast sourceGaloisWInfinityRamificationIndex_pos m
  omega

/-- This is the divisor of the actual nonzero dz, not a divisor defined to
have the desired source coefficients. -/
theorem sourceClosure_dz_divisor (m : ℕ) :
    differentialDivisor (k := F256) (F := SourceGaloisClosureField m)
      functionFieldDifferentialGenerator functionFieldDifferentialGenerator_ne_zero =
      (16 * (sourceGaloisWZeroRamificationIndex m : ℤ) - 2) • sourceGaloisWZeroFibreDivisor m +
        (-14 * (sourceGaloisWInfinityRamificationIndex m : ℤ) - 2) •
          sourceGaloisWInfinityFibreDivisor m := by
  classical
  ext Q
  rw [differentialDivisor_apply]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : Q ∈ (sourceGaloisWZeroFibreDivisor m).support
  · have hB : sourceGaloisWInfinityFibreDivisor m Q = 0 := by
      by_contra hn
      exact Finset.disjoint_left.mp (sourceClosureWFibreDivisors_disjoint m)
        hA (Finsupp.mem_support_iff.mpr hn)
    have hA' : Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m) := by
      rw [← sourceGaloisWZeroFibreDivisor_support]
      exact hA
    obtain ⟨P, rfl⟩ := hA'
    rw [sourceClosureWZero_dz_order, sourceGaloisWZeroFibreDivisor_apply, hB]
    ring
  · have hAzero : sourceGaloisWZeroFibreDivisor m Q = 0 := by
      by_contra hn
      exact hA (Finsupp.mem_support_iff.mpr hn)
    by_cases hB : Q ∈ (sourceGaloisWInfinityFibreDivisor m).support
    · have hB' : Q ∈ Set.range (sourceGaloisWInfinityPlaceOfPrime m) := by
        rw [← sourceGaloisWInfinityFibreDivisor_support]
        exact hB
      obtain ⟨P, rfl⟩ := hB'
      rw [sourceClosureWInfinity_dz_order, sourceGaloisWInfinityFibreDivisor_apply, hAzero]
      ring
    · have hBzero : sourceGaloisWInfinityFibreDivisor m Q = 0 := by
        by_contra hn
        exact hB (Finsupp.mem_support_iff.mpr hn)
      have hw := congrArg (fun D : Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) => D Q)
        (sourceGaloisWClosureGenerator_principalDivisor m)
      simp only [GlobalPlace.principalDivisor_apply, Units.val_mk0,
        Finsupp.sub_apply, Finsupp.smul_apply, hAzero, hBzero, smul_zero, sub_self] at hw
      rw [sourceClosure_dz_order_of_generator_order_zero m Q hw, hAzero, hBzero]
      ring

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
