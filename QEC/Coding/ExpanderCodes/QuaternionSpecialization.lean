import QEC.Coding.ExpanderCodes.FiniteFieldSquareParameters
import QEC.Coding.ExpanderCodes.QuaternionMatrix

/-!
# Quaternion specializations inside PSL₂

The finite-field square-ratio construction and quadratic constant splitting
put both actual arithmetic generators in the canonical PSL₂ image. Their
specialization point has the full prescribed minimal-polynomial degree.
This is an existence theorem for algebraic specializations, not a proof of
generation of PSL₂ or of the Ramanujan property.
-/

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

variable {K : Type*} [Field K]

/-- The two independently computed norms are squares for these actual roots. -/
theorem base_prime_matrix_mem_psl_of_squares (r y s i : K)
    (hR : r ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1) :
    projectiveMatrixEquiv r y hR hOne hTwo (projectiveBase (r ^ 2) y hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquiv r y hR hOne hTwo
          (projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by
  constructor
  · exact (projectiveBase_matrix_mem_psl_iff r y hR hY hOne hTwo).mpr ⟨s, hRatio⟩
  · apply (projectivePrime_matrix_mem_psl_iff r y hR hY hOne hTwo).mpr
    refine ⟨i * r * s, ?_⟩
    rw [mul_pow, mul_pow, hI, hRatio]
    ring

theorem base_prime_matrix_mem_psl_of_root (epsilon r y s i : K)
    (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1) :
    projectiveMatrixEquivOfRoot epsilon r y hRoot hR hOne hTwo
          (projectiveBase epsilon y hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquivOfRoot epsilon r y hRoot hR hOne hTwo
          (projectivePrime epsilon y hEpsilon hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by
  subst epsilon
  exact base_prime_matrix_mem_psl_of_squares r y s i hR hY hOne hTwo hRatio hI

/-- Every sufficiently large even extension admits a full-degree
specialization whose two actual projective generators belong to PSL₂. -/
theorem exists_even_psl_specialization (p n : ℕ) [Fact p.Prime]
    (hOdd : 3 ≤ p) (hDegree : 1 < n) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) :
    ∃ (y r : GaloisField p (2 * n)) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
      (hR : r ≠ 0)
      (hRoot : r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
      (hTwo : (2 : GaloisField p (2 * n)) ≠ 0),
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n ∧
      projectiveMatrixEquivOfRoot
          (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y hRoot hR hOne hTwo
          (projectiveBase (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
            y hY hOne) ∈ ProjectiveDeterminant.specialProjectiveSubgroup ∧
      projectiveMatrixEquivOfRoot
          (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y hRoot hR hOne hTwo
          (projectivePrime (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon)
            y ((map_ne_zero _).mpr hEpsilon) hY hOne) ∈
        ProjectiveDeterminant.specialProjectiveSubgroup := by
  obtain ⟨y, r, s, i, hY, hOne, hR, _, hRoot, hRatio, hI, hIrreducible, hMinDegree⟩ :=
    exists_even_psl_parameters p n hDegree epsilon hEpsilon
  have hTwo : (2 : GaloisField p (2 * n)) ≠ 0 := by
    intro hZero
    have hDvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p (2 * n)) p 2).mp hZero
    have := Nat.le_of_dvd (by decide : 0 < 2) hDvd
    omega
  have hBoth := base_prime_matrix_mem_psl_of_root
    (algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon) r y s i
    ((map_ne_zero _).mpr hEpsilon) hRoot hR hY hOne hTwo hRatio hI
  exact ⟨y, r, hY, hOne, hR, hRoot, hTwo, hIrreducible, hMinDegree, hBoth⟩

end QEC.Coding.ExpanderCodes.QuaternionGenerators
