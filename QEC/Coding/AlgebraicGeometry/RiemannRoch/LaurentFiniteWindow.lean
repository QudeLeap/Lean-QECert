import Mathlib

namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

open scoped Polynomial Pointwise

variable (k : Type*) [Field k]

noncomputable def directCoordinate : k[X] →ₐ[k] LaurentPolynomial k :=
  Polynomial.toLaurentAlg

noncomputable def inverseCoordinate : k[X] →ₐ[k] LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toAlgHom.comp Polynomial.toLaurentAlg

theorem directCoordinate_apply (p : k[X]) :
    directCoordinate k p = p.toLaurent :=
  rfl

theorem inverseCoordinate_apply (p : k[X]) :
    inverseCoordinate k p = LaurentPolynomial.invert p.toLaurent :=
  rfl

theorem directCoordinate_X :
    directCoordinate k Polynomial.X = LaurentPolynomial.T (R := k) 1 := by
  simp [directCoordinate]

theorem inverseCoordinate_X :
    inverseCoordinate k Polynomial.X = LaurentPolynomial.T (R := k) (-1) := by
  simp [inverseCoordinate]

theorem direct_inverse_X_pow (m n : ℕ) :
    directCoordinate k (Polynomial.X ^ m) * inverseCoordinate k (Polynomial.X ^ n) =
      LaurentPolynomial.T (R := k) ((m : ℤ) - n) := by
  calc
    directCoordinate k (Polynomial.X ^ m) * inverseCoordinate k (Polynomial.X ^ n) =
        LaurentPolynomial.T (R := k) (m : ℤ) * LaurentPolynomial.T (R := k) (-(n : ℤ)) := by
      simp only [directCoordinate_apply, inverseCoordinate_apply,
        Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_T]
    _ = LaurentPolynomial.T (R := k) ((m : ℤ) + -(n : ℤ)) :=
      (LaurentPolynomial.T_add (R := k) (m : ℤ) (-(n : ℤ))).symm
    _ = LaurentPolynomial.T (R := k) ((m : ℤ) - n) := by
      rw [sub_eq_add_neg]

def laurentWindow (lower upper : ℤ) : Submodule k (LaurentPolynomial k) where
  carrier := {f | f.coeff.support ⊆ Finset.Icc lower upper}
  zero_mem' := by
    change (∅ : Finset ℤ) ⊆ Finset.Icc lower upper
    exact Finset.empty_subset _
  add_mem' := by
    intro f g hf hg
    exact Finsupp.support_add.trans (Finset.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    exact Finsupp.support_smul.trans hf

noncomputable def laurentWindowFamily (lower upper : ℤ) : Finset (LaurentPolynomial k) :=
  by
    classical
    exact (Finset.Icc lower upper).image (fun n : ℤ => LaurentPolynomial.T (R := k) n)

theorem T_mem_laurentWindow {lower upper n : ℤ} (hn : n ∈ Finset.Icc lower upper) :
    LaurentPolynomial.T (R := k) n ∈ laurentWindow k lower upper := by
  have hsupport : (LaurentPolynomial.T (R := k) n).coeff.support ⊆ ({n} : Finset ℤ) := by
    exact Finsupp.support_single_subset
  exact hsupport.trans <| by
    intro m hm
    have hmn : m = n := Finset.mem_singleton.mp hm
    simpa [hmn] using hn

theorem laurent_sum_C_mul_T_eq (f : LaurentPolynomial k) :
    f.coeff.support.sum (fun n : ℤ =>
      LaurentPolynomial.C (R := k) (f.coeff n) * LaurentPolynomial.T (R := k) n) = f := by
  simpa only [← LaurentPolynomial.single_eq_C_mul_T, Finsupp.sum] using
    AddMonoidAlgebra.sum_coeff_single f

theorem laurentWindow_eq_span (lower upper : ℤ) :
    laurentWindow k lower upper =
      Submodule.span k (laurentWindowFamily k lower upper : Set (LaurentPolynomial k)) := by
  classical
  apply le_antisymm
  · intro f hf
    change f.coeff.support ⊆ Finset.Icc lower upper at hf
    rw [← laurent_sum_C_mul_T_eq k f]
    exact Submodule.sum_mem _ fun n hn => by
      rw [← LaurentPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ <| Submodule.subset_span <|
        Finset.mem_image.mpr ⟨n, hf hn, rfl⟩
  · refine Submodule.span_le.mpr ?_
    intro f hf
    change f ∈ laurentWindowFamily k lower upper at hf
    rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
    exact T_mem_laurentWindow k hn

theorem laurentWindow_finiteDimensional (lower upper : ℤ) :
    FiniteDimensional k (laurentWindow k lower upper) := by
  rw [laurentWindow_eq_span]
  exact FiniteDimensional.span_of_finite k (Finset.finite_toSet _)

theorem direct_support_subset_interval (p : k[X]) :
    (directCoordinate k p).coeff.support ⊆ Finset.Icc (0 : ℤ) (p.natDegree : ℤ) := by
  rw [directCoordinate_apply, LaurentPolynomial.support_coeff_toLaurent]
  rintro n hn
  rcases Finset.mem_map.mp hn with ⟨m, hm, rfl⟩
  refine Finset.mem_Icc.mpr ⟨Int.natCast_nonneg _, ?_⟩
  exact Int.ofNat_le.mpr (Polynomial.le_natDegree_of_mem_supp m hm)

theorem inverse_support_subset_interval (q : k[X]) :
    (inverseCoordinate k q).coeff.support ⊆ Finset.Icc (-(q.natDegree : ℤ)) 0 := by
  intro n hn
  have hneg : -n ∈ (directCoordinate k q).coeff.support := by
    rw [Finsupp.mem_support_iff] at hn ⊢
    simpa [directCoordinate_apply, inverseCoordinate_apply] using hn
  have hbounds := direct_support_subset_interval k q hneg
  rw [Finset.mem_Icc] at hbounds ⊢
  omega

theorem direct_mul_inverse_support_subset (p q : k[X]) :
    (directCoordinate k p * inverseCoordinate k q).coeff.support ⊆
      Finset.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by
  intro n hn
  obtain ⟨i, hi, j, hj, hij⟩ :
      ∃ i ∈ (directCoordinate k p).coeff.support, ∃ j ∈ (inverseCoordinate k q).coeff.support, i + j = n :=
    Finset.mem_add.mp <| AddMonoidAlgebra.support_coeff_mul_subset _ _ hn
  have hibounds := direct_support_subset_interval k p hi
  have hjbounds := inverse_support_subset_interval k q hj
  rw [Finset.mem_Icc] at hibounds hjbounds ⊢
  omega

theorem direct_mul_inverse_mem_laurentWindow (p q : k[X]) :
    directCoordinate k p * inverseCoordinate k q ∈
      laurentWindow k (-(q.natDegree : ℤ)) (p.natDegree : ℤ) := by
  change (directCoordinate k p * inverseCoordinate k q).coeff.support ⊆
    Finset.Icc (-(q.natDegree : ℤ)) (p.natDegree : ℤ)
  exact direct_mul_inverse_support_subset k p q

def directScaledLocus (a : k[X]) : Set (LaurentPolynomial k) :=
  {z | ∃ p : k[X], directCoordinate k a * z = directCoordinate k p}

def inverseScaledLocus (b : k[X]) : Set (LaurentPolynomial k) :=
  {z | ∃ q : k[X], inverseCoordinate k b * z = inverseCoordinate k q}

theorem opposite_scaled_intersection_mem_laurentWindow
    {a b : k[X]} {z : LaurentPolynomial k}
    (hzDirect : z ∈ directScaledLocus k a)
    (hzInverse : z ∈ inverseScaledLocus k b) :
    inverseCoordinate k b * (directCoordinate k a * z) ∈
      laurentWindow k (-(b.natDegree : ℤ)) (a.natDegree : ℤ) := by
  change ∃ p : k[X], directCoordinate k a * z = directCoordinate k p at hzDirect
  change ∃ q : k[X], inverseCoordinate k b * z = inverseCoordinate k q at hzInverse
  rcases hzDirect with ⟨p, hp⟩
  rcases hzInverse with ⟨q, hq⟩
  change (inverseCoordinate k b * (directCoordinate k a * z)).coeff.support ⊆
    Finset.Icc (-(b.natDegree : ℤ)) (a.natDegree : ℤ)
  intro n hn
  have hleft : n ∈ Finset.Icc (-(b.natDegree : ℤ)) (p.natDegree : ℤ) := by
    apply direct_mul_inverse_support_subset k p b
    simpa [hp, mul_comm] using hn
  have hscaled : inverseCoordinate k b * (directCoordinate k a * z) =
      directCoordinate k a * inverseCoordinate k q := by
    calc
      inverseCoordinate k b * (directCoordinate k a * z) =
          (inverseCoordinate k b * directCoordinate k a) * z := (mul_assoc _ _ _).symm
      _ = (directCoordinate k a * inverseCoordinate k b) * z := by
        rw [mul_comm (inverseCoordinate k b) (directCoordinate k a)]
      _ = directCoordinate k a * (inverseCoordinate k b * z) := mul_assoc _ _ _
      _ = directCoordinate k a * inverseCoordinate k q := by rw [hq]
  have hright : n ∈ Finset.Icc (-(q.natDegree : ℤ)) (a.natDegree : ℤ) := by
    apply direct_mul_inverse_support_subset k a q
    simpa [hscaled] using hn
  rw [Finset.mem_Icc] at hleft hright ⊢
  exact ⟨hleft.1, hright.2⟩

end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
