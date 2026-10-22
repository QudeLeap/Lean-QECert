import QEC.Coding.AlgebraicGeometry.RiemannRoch.PlaceIncrement

/-!
# Divisors of finite injective place families

This module packages the elementary divisor bookkeeping for an actual finite
family of global places.  It records coefficients, support, nonnegativity,
and weighted degree; it makes no tower-specific ramification claim.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators

noncomputable section

namespace GlobalPlace

variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-- The reduced divisor formed from a finite family of actual global places. -/
noncomputable def finitePlaceDivisor [Fintype ι]
    (P : ι → GlobalPlace k F) : Divisor (GlobalPlace k F) :=
  ∑ i : ι, placeDivisor (P i)

/-- An injectively enumerated place has coefficient one in its finite-family
divisor. -/
@[simp]
theorem finitePlaceDivisor_apply [Fintype ι]
    (P : ι → GlobalPlace k F) (hP : Function.Injective P) (i : ι) :
    finitePlaceDivisor P (P i) = 1 := by
  classical
  unfold finitePlaceDivisor
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact placeDivisor_apply (P i)
  · intro j _ hji
    exact placeDivisor_apply_of_ne (P j) (P i) (fun h => hji (hP h))
  · simp

/-- A place outside the finite image has coefficient zero. -/
theorem finitePlaceDivisor_apply_eq_zero_of_not_mem [Fintype ι]
    (P : ι → GlobalPlace k F) (Q : GlobalPlace k F)
    (hQ : Q ∉ Set.range P) : finitePlaceDivisor P Q = 0 := by
  classical
  unfold finitePlaceDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply placeDivisor_apply_of_ne
  intro hPi
  exact hQ ⟨i, hPi⟩

/-- A finite-family place divisor is coefficientwise nonnegative. -/
theorem finitePlaceDivisor_nonnegative [Fintype ι]
    (P : ι → GlobalPlace k F) : 0 ≤ finitePlaceDivisor P := by
  intro Q
  classical
  unfold finitePlaceDivisor
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i _ => by
    by_cases hPi : P i = Q <;> simp [placeDivisor, hPi]

/-- The support of an injective finite-family divisor is exactly the image of
the enumerating family. -/
theorem finitePlaceDivisor_support [Fintype ι]
    (P : ι → GlobalPlace k F) (hP : Function.Injective P) :
    ↑(finitePlaceDivisor P).support = Set.range P := by
  classical
  ext Q
  rw [Finset.mem_coe, Divisor.mem_support_iff]
  constructor
  · intro hQ
    by_contra hmem
    exact hQ (finitePlaceDivisor_apply_eq_zero_of_not_mem P Q hmem)
  · intro hQ
    obtain ⟨i, rfl⟩ := hQ
    rw [finitePlaceDivisor_apply P hP]
    norm_num

/-- The weighted degree of a finite-family divisor is the sum of the actual
residue degrees of its places. -/
theorem finitePlaceDivisor_degree [Fintype ι]
    (P : ι → GlobalPlace k F) :
    Divisor.degree (residueDegree (k := k) (F := F))
        (finitePlaceDivisor P) =
      ∑ i : ι, (residueDegree (k := k) (F := F) (P i) : ℤ) := by
  classical
  unfold finitePlaceDivisor
  change
    Divisor.degreeHom (residueDegree (k := k) (F := F))
        (∑ i : ι, placeDivisor (P i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact placeDivisor_degree (P i)

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
