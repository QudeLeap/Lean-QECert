import QEC.Coding.AlgebraicGeometry.Towers.ClosureCanonicalDifferential

/-!
# Separation of the selected rational points from both w-fibres

At a selected point, z-1 is a simple parameter and its derivative is one,
so dz has order zero. This differs from its proved order at either w-fibre.
-/

open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem sourceClosure_selected_dz_order (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    differentialOrder (sourceGaloisClosureSelectedRationalPlace m j).place
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  let P := (sourceGaloisClosureSelectedRationalPlace m j).place
  have hf := sourceGaloisClosureSelectedRationalPlace_order_vanishingFunction m j
  obtain ⟨_, h⟩ := differentialGenerator_order_of_order_one_or_neg_one P
    (sourceGaloisClosureSelectedVanishingFunction m)
    (sourceGaloisClosureSelectedVanishingFunction_ne_zero m) (.inl hf)
  rw [h, sourceClosure_selectedVanishing_derivative, hf]
  simp [GlobalPlace.order]

theorem sourceClosureWZeroFibre_disjoint_selected (m : ℕ) :
    Disjoint (sourceGaloisWZeroFibreDivisor m).support
      (sourceGaloisClosureSelectedDivisor m).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hA hD
  have hA' : Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m) := by
    rw [← sourceGaloisWZeroFibreDivisor_support]
    exact hA
  have hD' : Q ∈ Set.range (fun j : Fin (sourceGaloisClosureSelectedLength m) =>
      (sourceGaloisClosureSelectedRationalPlace m j).place) := by
    rw [← sourceGaloisClosureSelectedDivisor_support]
    exact hD
  obtain ⟨P, rfl⟩ := hA'
  obtain ⟨j, hj⟩ := hD'
  dsimp only at hj
  have h := sourceClosure_selected_dz_order m j
  rw [hj, sourceClosureWZero_dz_order] at h
  have hp : (0 : ℤ) < sourceGaloisWZeroRamificationIndex m := by
    exact_mod_cast sourceGaloisWZeroRamificationIndex_pos m
  omega

theorem sourceClosureWInfinityFibre_disjoint_selected (m : ℕ) :
    Disjoint (sourceGaloisWInfinityFibreDivisor m).support
      (sourceGaloisClosureSelectedDivisor m).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hB hD
  have hB' : Q ∈ Set.range (sourceGaloisWInfinityPlaceOfPrime m) := by
    rw [← sourceGaloisWInfinityFibreDivisor_support]
    exact hB
  have hD' : Q ∈ Set.range (fun j : Fin (sourceGaloisClosureSelectedLength m) =>
      (sourceGaloisClosureSelectedRationalPlace m j).place) := by
    rw [← sourceGaloisClosureSelectedDivisor_support]
    exact hD
  obtain ⟨P, rfl⟩ := hB'
  obtain ⟨j, hj⟩ := hD'
  dsimp only at hj
  have h := sourceClosure_selected_dz_order m j
  rw [hj, sourceClosureWInfinity_dz_order] at h
  have hp : (0 : ℤ) < sourceGaloisWInfinityRamificationIndex m := by
    exact_mod_cast sourceGaloisWInfinityRamificationIndex_pos m
  omega

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
