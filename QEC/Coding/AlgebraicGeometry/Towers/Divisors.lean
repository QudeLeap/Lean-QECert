import QEC.Coding.AlgebraicGeometry.Towers.Enumeration

/-!
# Selected divisors in the F256 Garcia--Stichtenoth tower

The retained original GS95-family tail uses recursive field `Field (i + 2)`,
not `SourceField` or its normal closure. This module forms the reduced divisor on
the previously constructed finite enumeration of split rational places.  Its
coefficients, support, positivity, and weighted degree are derived from that
enumeration; no divisor is supplied as parameter data.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

open scoped BigOperators

noncomputable section

/-- The actual reduced divisor on the selected split places of this
original-family tail. -/
noncomputable def selectedDivisor (i : ℕ) :
    Divisor (GlobalPlace F256 (Field (i + 2))) := by
  classical
  exact ∑ j : Fin (selectedLength i),
    Finsupp.single (selectedPlace i j) (1 : ℤ)

/-- Every enumerated selected place has coefficient one. -/
theorem selectedDivisor_apply_selected (i : ℕ)
    (j : Fin (selectedLength i)) :
    selectedDivisor i (selectedPlace i j) = 1 := by
  classical
  unfold selectedDivisor
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    have hplace : selectedPlace i j' ≠ selectedPlace i j := by
      intro h
      exact hj' (selectedPlace_injective i h)
    simp [hplace]
  · simp

/-- A place outside the selected finite set has coefficient zero. -/
theorem selectedDivisor_apply_eq_zero_of_not_mem (i : ℕ)
    (P : GlobalPlace F256 (Field (i + 2))) (hP : P ∉ selectedPlaces i) :
    selectedDivisor i P = 0 := by
  classical
  unfold selectedDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hplace : selectedPlace i j ≠ P := by
    intro h
    apply hP
    rw [selectedPlaces]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩
  simp [hplace]

/-- The selected-place divisor is coefficientwise nonnegative. -/
theorem selectedDivisor_nonnegative (i : ℕ) : 0 ≤ selectedDivisor i := by
  intro P
  classical
  unfold selectedDivisor
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun j _ => by
    by_cases hplace : selectedPlace i j = P <;> simp [hplace]

/-- The support of the selected-place divisor is exactly the selected finite
set. -/
theorem selectedDivisor_support (i : ℕ) :
    (selectedDivisor i).support = selectedPlaces i := by
  classical
  ext P
  rw [Divisor.mem_support_iff]
  constructor
  · intro hcoefficient
    by_contra hP
    exact hcoefficient (selectedDivisor_apply_eq_zero_of_not_mem i P hP)
  · intro hP
    rw [selectedPlaces, Finset.mem_image] at hP
    obtain ⟨j, _, rfl⟩ := hP
    rw [selectedDivisor_apply_selected]
    norm_num

private theorem divisor_degree_single (i : ℕ) (degreeOf :
    GlobalPlace F256 (Field (i + 2)) → ℕ)
    (P : GlobalPlace F256 (Field (i + 2))) (coefficient : ℤ) :
    Divisor.degree degreeOf (Finsupp.single P coefficient) =
      coefficient * (degreeOf P : ℤ) := by
  simp [Divisor.degree, Divisor.degreeHom]

/-- The weighted degree of the selected-place divisor is the exact selected
length because every selected place is rational. -/
theorem selectedDivisor_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (selectedDivisor i) =
      selectedLength i := by
  classical
  unfold selectedDivisor
  change
    Divisor.degreeHom GlobalPlace.residueDegree
        (∑ j : Fin (selectedLength i),
          Finsupp.single (selectedPlace i j) (1 : ℤ)) =
      selectedLength i
  rw [map_sum]
  calc
    (∑ j : Fin (selectedLength i),
        Divisor.degreeHom GlobalPlace.residueDegree
          (Finsupp.single (selectedPlace i j) (1 : ℤ))) =
        ∑ _j : Fin (selectedLength i), (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro j _
      change
        Divisor.degree GlobalPlace.residueDegree
            (Finsupp.single (selectedPlace i j) (1 : ℤ)) = 1
      rw [divisor_degree_single, selectedPlace_residueDegree]
      simp
    _ = selectedLength i := by simp

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
