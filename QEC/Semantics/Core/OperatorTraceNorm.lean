import QEC.Semantics.Core.Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Finite-dimensional operator trace norm

This module defines the Schatten-1 norm on `QEC.Semantics.Operator` through its
finite-dimensional dual characterization

`‖A‖₁ = ‖B ↦ Tr (B A)‖`,

where the norm on the test operator is the ordinary operator norm. It proves the
norm laws, the two-sided ideal estimates, the positive-operator specialization,
and the projection-tail identities used by the CLBT thermal-memory route.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- The ordinary operator norm of a finite-dimensional linear operator. -/
def operatorNorm (A : Operator H) : Real :=
  ‖LinearMap.toContinuousLinearMap A‖

/-- The continuous trace-pairing functional associated with an operator. -/
def tracePairing (A : Operator H) : (H →L[Complex] H) →L[Complex] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => LinearMap.trace Complex H (B.toLinearMap * A)
      map_add' := by
        intro B C
        simp [add_mul]
      map_smul' := by
        intro c B
        simp }

/--
The finite-dimensional Schatten-1 norm, defined by its canonical dual pairing
with the operator norm.
-/
def traceNorm (A : Operator H) : Real :=
  ‖tracePairing A‖

theorem operatorNorm_nonneg (A : Operator H) : 0 ≤ operatorNorm A :=
  ContinuousLinearMap.opNorm_nonneg _

theorem traceNorm_nonneg (A : Operator H) : 0 ≤ traceNorm A :=
  ContinuousLinearMap.opNorm_nonneg _

theorem tracePairing_add (A B : Operator H) :
    tracePairing (A + B) = tracePairing A + tracePairing B := by
  ext C
  simp [tracePairing, mul_add]

theorem tracePairing_smul (c : Complex) (A : Operator H) :
    tracePairing (c • A) = c • tracePairing A := by
  ext B
  simp [tracePairing]

theorem traceNorm_add_le (A B : Operator H) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  rw [traceNorm, traceNorm, traceNorm, tracePairing_add]
  exact (tracePairing A).opNorm_add_le (tracePairing B)

theorem traceNorm_smul (c : Complex) (A : Operator H) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  rw [traceNorm, traceNorm, tracePairing_smul]
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_smul_le c _
  · by_cases hc : c = 0
    · rw [hc]
      simp only [norm_zero, zero_mul]
      exact ContinuousLinearMap.opNorm_nonneg _
    · have h : ‖tracePairing A‖ ≤ ‖c⁻¹‖ * ‖c • tracePairing A‖ := by
        convert ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • tracePairing A) using 1
        simp [hc]
      calc
        ‖c‖ * ‖tracePairing A‖ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • tracePairing A‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg c)
        _ = ‖c • tracePairing A‖ := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul]

theorem trace_adjoint_mul_self_eq_zero_iff (A : Operator H) :
    LinearMap.trace Complex H (LinearMap.adjoint A * A) = 0 ↔ A = 0 := by
  let b := stdOrthonormalBasis Complex H
  rw [LinearMap.trace_eq_matrix_trace Complex b.toBasis]
  rw [LinearMap.toMatrix_mul]
  rw [LinearMap.toMatrix_adjoint]
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
  exact (LinearMap.toMatrix b.toBasis b.toBasis).map_eq_zero_iff

theorem traceNorm_eq_zero_iff (A : Operator H) : traceNorm A = 0 ↔ A = 0 := by
  rw [traceNorm, ContinuousLinearMap.opNorm_zero_iff]
  constructor
  · intro h
    have hpair := congrArg
      (fun f : (H →L[Complex] H) →L[Complex] Complex =>
        f (LinearMap.toContinuousLinearMap (LinearMap.adjoint A))) h
    simp only [tracePairing] at hpair
    exact (trace_adjoint_mul_self_eq_zero_iff A).mp hpair
  · rintro rfl
    ext B
    simp [tracePairing]

theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Operator H) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  change
    ‖tracePairing (∑ i ∈ s, f i)‖ ≤
      ∑ i ∈ s, ‖tracePairing (f i)‖
  rw [show
    tracePairing (∑ i ∈ s, f i) =
      ∑ i ∈ s, tracePairing (f i) by
    ext C
    simp [tracePairing, Finset.mul_sum]]
  exact norm_sum_le s (fun i => tracePairing (f i))

theorem traceNorm_mul_left_le (A B : Operator H) :
    traceNorm (A * B) ≤ operatorNorm A * traceNorm B := by
  change ‖tracePairing (A * B)‖ ≤ ‖LinearMap.toContinuousLinearMap A‖ * ‖tracePairing B‖
  apply (tracePairing (A * B)).opNorm_le_bound
  · exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
      (ContinuousLinearMap.opNorm_nonneg _)
  · intro C
    rw [show tracePairing (A * B) C =
        tracePairing B (C * LinearMap.toContinuousLinearMap A) by
      simp [tracePairing, mul_assoc]]
    calc
      ‖tracePairing B (C * LinearMap.toContinuousLinearMap A)‖ ≤
          traceNorm B * ‖C * LinearMap.toContinuousLinearMap A‖ :=
        (tracePairing B).le_opNorm _
      _ ≤ traceNorm B * (‖C‖ * operatorNorm A) := by
        exact mul_le_mul_of_nonneg_left
          (C.opNorm_comp_le (LinearMap.toContinuousLinearMap A))
          (ContinuousLinearMap.opNorm_nonneg _)
      _ = (operatorNorm A * traceNorm B) * ‖C‖ := by ring

theorem traceNorm_mul_right_le (A B : Operator H) :
    traceNorm (A * B) ≤ operatorNorm B * traceNorm A := by
  change ‖tracePairing (A * B)‖ ≤ ‖LinearMap.toContinuousLinearMap B‖ * ‖tracePairing A‖
  apply (tracePairing (A * B)).opNorm_le_bound
  · exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
      (ContinuousLinearMap.opNorm_nonneg _)
  · intro C
    rw [show tracePairing (A * B) C =
        tracePairing A (LinearMap.toContinuousLinearMap B * C) by
      change LinearMap.trace Complex H (C.toLinearMap * (A * B)) =
        LinearMap.trace Complex H
          ((LinearMap.toContinuousLinearMap B * C).toLinearMap * A)
      rw [show (LinearMap.toContinuousLinearMap B * C).toLinearMap =
          B * C.toLinearMap by
        ext x
        rfl]
      rw [← mul_assoc, LinearMap.trace_mul_cycle]]
    calc
      ‖tracePairing A (LinearMap.toContinuousLinearMap B * C)‖ ≤
          traceNorm A * ‖LinearMap.toContinuousLinearMap B * C‖ :=
        (tracePairing A).le_opNorm _
      _ ≤ traceNorm A * (operatorNorm B * ‖C‖) := by
        exact mul_le_mul_of_nonneg_left
          ((LinearMap.toContinuousLinearMap B).opNorm_comp_le C)
          (ContinuousLinearMap.opNorm_nonneg _)
      _ = (operatorNorm B * traceNorm A) * ‖C‖ := by ring

theorem traceNorm_rankOne_self_le (x : H) :
    traceNorm (InnerProductSpace.rankOne Complex x x).toLinearMap ≤ ‖x‖ ^ 2 := by
  change ‖tracePairing (InnerProductSpace.rankOne Complex x x).toLinearMap‖ ≤ ‖x‖ ^ 2
  apply (tracePairing (InnerProductSpace.rankOne Complex x x).toLinearMap).opNorm_le_bound
  · positivity
  · intro B
    rw [show tracePairing (InnerProductSpace.rankOne Complex x x).toLinearMap B =
        inner Complex x (B x) by
      change LinearMap.trace Complex H
          (B.toLinearMap * (InnerProductSpace.rankOne Complex x x).toLinearMap) = _
      rw [show B.toLinearMap * (InnerProductSpace.rankOne Complex x x).toLinearMap =
          (InnerProductSpace.rankOne Complex (B x) x).toLinearMap by
        ext y
        simp]
      exact InnerProductSpace.trace_rankOne (B x) x]
    calc
      ‖inner Complex x (B x)‖ ≤ ‖x‖ * ‖B x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖B‖ * ‖x‖) := by
        gcongr
        exact B.le_opNorm x
      _ = ‖x‖ ^ 2 * ‖B‖ := by ring

theorem norm_trace_le_traceNorm [Nontrivial H] (A : Operator H) :
    ‖LinearMap.trace Complex H A‖ ≤ traceNorm A := by
  have h := (tracePairing A).le_opNorm (ContinuousLinearMap.id Complex H)
  simpa [tracePairing, traceNorm, show (LinearMap.id : Operator H) = 1 from rfl] using h

/-- On positive operators, the trace norm specializes to the real trace. -/
theorem traceNorm_eq_re_trace_of_positive [Nontrivial H]
    (A : Operator H) (hA : LinearMap.IsPositive A) :
    traceNorm A = Complex.re (LinearMap.trace Complex H A) := by
  have hAclm : (LinearMap.toContinuousLinearMap A).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  obtain ⟨m, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hAclm
  have hA_sum : A = ∑ i : Fin m,
      (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hu
  have htrace : Complex.re (LinearMap.trace Complex H A) =
      ∑ i : Fin m, ‖u i‖ ^ 2 := by
    rw [hA_sum, map_sum]
    simp only [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    norm_num [pow_two, Complex.mul_re]
  apply le_antisymm
  · calc
      traceNorm A = traceNorm (∑ i : Fin m,
          (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :=
        congrArg traceNorm hA_sum
      _ ≤ ∑ i : Fin m,
          traceNorm (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
        exact traceNorm_sum_le Finset.univ _
      _ ≤ ∑ i : Fin m, ‖u i‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => traceNorm_rankOne_self_le (u i)
      _ = Complex.re (LinearMap.trace Complex H A) := htrace.symm
  · exact (Complex.re_le_norm _).trans (norm_trace_le_traceNorm A)

namespace DensityOperator

theorem traceNorm_eq_one [Nontrivial H] (rho : DensityOperator H) :
    traceNorm rho.toOperator = 1 := by
  rw [traceNorm_eq_re_trace_of_positive rho.toOperator rho.positive, rho.trace_one]
  norm_num

end DensityOperator

/-! ## Self-adjoint specialization -/

/-- The positive part of a finite-dimensional operator. -/
noncomputable def positivePart (A : Operator H) : Operator H :=
  ((LinearMap.toContinuousLinearMap A)⁺).toLinearMap

/-- The negative part of a finite-dimensional operator. -/
noncomputable def negativePart (A : Operator H) : Operator H :=
  ((LinearMap.toContinuousLinearMap A)⁻).toLinearMap

/-- A self-adjoint operator is its positive part minus its negative part. -/
theorem positivePart_sub_negativePart (A : Operator H) (hA : A.IsSymmetric) :
    positivePart A - negativePart A = A := by
  have hAclm : (LinearMap.toContinuousLinearMap A).IsSymmetric := hA
  apply LinearMap.toContinuousLinearMap.injective
  change (LinearMap.toContinuousLinearMap A)⁺ -
      (LinearMap.toContinuousLinearMap A)⁻ = LinearMap.toContinuousLinearMap A
  exact CFC.posPart_sub_negPart _ hAclm.isSelfAdjoint

/-- The positive part is positive. -/
theorem positivePart_positive (A : Operator H) : LinearMap.IsPositive (positivePart A) := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.posPart_nonneg _)

/-- The negative part is positive. -/
theorem negativePart_positive (A : Operator H) : LinearMap.IsPositive (negativePart A) := by
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.negPart_nonneg _)

/-- The support projection of the positive part. -/
noncomputable def positiveSupportProjection (A : Operator H) : H →L[Complex] H :=
  ((LinearMap.toContinuousLinearMap A)⁺).range.starProjection

/-- The support projection of the negative part. -/
noncomputable def negativeSupportProjection (A : Operator H) : H →L[Complex] H :=
  ((LinearMap.toContinuousLinearMap A)⁻).range.starProjection

theorem parts_range_isOrtho (A : Operator H) :
    ((LinearMap.toContinuousLinearMap A)⁺).range ⟂
      ((LinearMap.toContinuousLinearMap A)⁻).range := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  rcases hu with ⟨x, rfl⟩
  rcases hv with ⟨y, rfl⟩
  have hpos : ((LinearMap.toContinuousLinearMap A)⁺).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.posPart_nonneg _)
  calc
    inner Complex ((LinearMap.toContinuousLinearMap A)⁺ x)
        ((LinearMap.toContinuousLinearMap A)⁻ y) =
      inner Complex x
        ((LinearMap.toContinuousLinearMap A)⁺
          ((LinearMap.toContinuousLinearMap A)⁻ y)) :=
        hpos.inner_left_eq_inner_right x _
    _ = 0 := by
      simp only [← ContinuousLinearMap.mul_apply, CFC.posPart_mul_negPart,
        ContinuousLinearMap.zero_apply, inner_zero_right]

/-- The support projections of the positive and negative parts are orthogonal. -/
theorem positiveSupportProjection_mul_negativeSupportProjection (A : Operator H) :
    positiveSupportProjection A * negativeSupportProjection A = 0 := by
  exact (parts_range_isOrtho A).starProjection_comp_starProjection

theorem supportProjection_mul_positivePart (A : Operator H) :
    positiveSupportProjection A * (LinearMap.toContinuousLinearMap A)⁺ =
      (LinearMap.toContinuousLinearMap A)⁺ := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

theorem supportProjection_mul_negativePart (A : Operator H) :
    negativeSupportProjection A * (LinearMap.toContinuousLinearMap A)⁻ =
      (LinearMap.toContinuousLinearMap A)⁻ := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

theorem positiveSupportProjection_mul_negativePart (A : Operator H) :
    positiveSupportProjection A * (LinearMap.toContinuousLinearMap A)⁻ = 0 := by
  ext x
  unfold positiveSupportProjection
  change ((LinearMap.toContinuousLinearMap A)⁺).range.starProjection
    ((LinearMap.toContinuousLinearMap A)⁻ x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (Submodule.isOrtho_iff_le.mp (parts_range_isOrtho A).symm) ⟨x, rfl⟩

theorem negativeSupportProjection_mul_positivePart (A : Operator H) :
    negativeSupportProjection A * (LinearMap.toContinuousLinearMap A)⁺ = 0 := by
  ext x
  unfold negativeSupportProjection
  change ((LinearMap.toContinuousLinearMap A)⁻).range.starProjection
    ((LinearMap.toContinuousLinearMap A)⁺ x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (Submodule.isOrtho_iff_le.mp (parts_range_isOrtho A)) ⟨x, rfl⟩

/-- The sign of an operator, supported on its positive and negative parts. -/
noncomputable def spectralSign (A : Operator H) : H →L[Complex] H :=
  positiveSupportProjection A - negativeSupportProjection A

theorem spectralSign_norm_le_one (A : Operator H) : ‖spectralSign A‖ ≤ 1 := by
  let P := positiveSupportProjection A
  let N := negativeSupportProjection A
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hN : IsStarProjection N := isStarProjection_starProjection
  have hPN : P * N = 0 := by
    exact (parts_range_isOrtho A).starProjection_comp_starProjection
  have hNP : N * P = 0 := by
    exact (parts_range_isOrtho A).symm.starProjection_comp_starProjection
  have hsum : IsStarProjection (P + N) := hP.add hN hPN
  have hsquare : star (P - N) * (P - N) = P + N := by
    rw [star_sub, hP.isSelfAdjoint.star_eq, hN.isSelfAdjoint.star_eq]
    simp only [sub_mul, mul_sub, hP.isIdempotentElem.eq,
      hN.isIdempotentElem.eq, hPN, hNP, sub_zero, zero_sub, sub_neg_eq_add]
  have hsq : ‖P - N‖ * ‖P - N‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, hsquare]
    exact hsum.norm_le _
  change ‖P - N‖ ≤ 1
  nlinarith [norm_nonneg (P - N)]

theorem spectralSign_mul_of_isSymmetric (A : Operator H) (hA : A.IsSymmetric) :
    spectralSign A * LinearMap.toContinuousLinearMap A =
      (LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻ := by
  have hAclm : (LinearMap.toContinuousLinearMap A).IsSymmetric := hA
  calc
    spectralSign A * LinearMap.toContinuousLinearMap A =
        spectralSign A * ((LinearMap.toContinuousLinearMap A)⁺ -
          (LinearMap.toContinuousLinearMap A)⁻) := by
      rw [CFC.posPart_sub_negPart _ hAclm.isSelfAdjoint]
    _ = (LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻ := by
      simp only [spectralSign, sub_mul, mul_sub,
        supportProjection_mul_positivePart, supportProjection_mul_negativePart,
        positiveSupportProjection_mul_negativePart,
        negativeSupportProjection_mul_positivePart,
        sub_zero, zero_sub, sub_neg_eq_add]

theorem tracePairing_spectralSign (A : Operator H) (hA : A.IsSymmetric) :
    tracePairing A (spectralSign A) =
      LinearMap.trace Complex H (positivePart A) +
        LinearMap.trace Complex H (negativePart A) := by
  change LinearMap.trace Complex H ((spectralSign A).toLinearMap * A) = _
  have hmul := congrArg ContinuousLinearMap.toLinearMap
    (spectralSign_mul_of_isSymmetric A hA)
  rw [show (spectralSign A).toLinearMap * A =
      ((LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻).toLinearMap by
    simpa using hmul]
  simp [positivePart, negativePart]

@[simp] theorem traceNorm_neg (A : Operator H) : traceNorm (-A) = traceNorm A := by
  simpa using traceNorm_smul (-1 : Complex) A

/--
Self-adjoint specialization of the trace norm: it is the sum of the trace
norms of the positive and negative parts.
-/
theorem traceNorm_eq_sum_parts [Nontrivial H]
    (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm A = traceNorm (positivePart A) + traceNorm (negativePart A) := by
  apply le_antisymm
  · have hdecomp : positivePart A - negativePart A = A :=
      positivePart_sub_negativePart A hA
    calc
      traceNorm A = traceNorm (positivePart A - negativePart A) :=
        congrArg traceNorm hdecomp.symm
      _ ≤ traceNorm (positivePart A) + traceNorm (-negativePart A) := by
        simpa [sub_eq_add_neg] using traceNorm_add_le (positivePart A) (-negativePart A)
      _ = traceNorm (positivePart A) + traceNorm (negativePart A) := by
        rw [traceNorm_neg]
  · have hpair := (tracePairing A).le_opNorm (spectralSign A)
    have hpair_le : ‖tracePairing A (spectralSign A)‖ ≤ traceNorm A := by
      calc
        ‖tracePairing A (spectralSign A)‖ ≤
            traceNorm A * ‖spectralSign A‖ := hpair
        _ ≤ traceNorm A * 1 :=
          mul_le_mul_of_nonneg_left (spectralSign_norm_le_one A) (traceNorm_nonneg A)
        _ = traceNorm A := mul_one _
    rw [tracePairing_spectralSign A hA] at hpair_le
    have hpositive := positivePart_positive A
    have hnegative := negativePart_positive A
    have htrace_nonneg :
        0 ≤ LinearMap.trace Complex H (positivePart A) +
          LinearMap.trace Complex H (negativePart A) :=
      add_nonneg hpositive.trace_nonneg hnegative.trace_nonneg
    have hnorm_trace :
        ‖LinearMap.trace Complex H (positivePart A) +
          LinearMap.trace Complex H (negativePart A)‖ =
          Complex.re (LinearMap.trace Complex H (positivePart A) +
            LinearMap.trace Complex H (negativePart A)) := by
      have hcoe := Complex.eq_coe_norm_of_nonneg htrace_nonneg
      simpa using congrArg Complex.re hcoe.symm
    calc
      traceNorm (positivePart A) + traceNorm (negativePart A) =
          Complex.re (LinearMap.trace Complex H (positivePart A)) +
            Complex.re (LinearMap.trace Complex H (negativePart A)) := by
        rw [traceNorm_eq_re_trace_of_positive _ hpositive,
          traceNorm_eq_re_trace_of_positive _ hnegative]
      _ = Complex.re (LinearMap.trace Complex H (positivePart A) +
            LinearMap.trace Complex H (negativePart A)) := by
        rw [Complex.add_re]
      _ = ‖LinearMap.trace Complex H (positivePart A) +
            LinearMap.trace Complex H (negativePart A)‖ := hnorm_trace.symm
      _ ≤ traceNorm A := hpair_le

/-- Compress an operator to the complement of a projection. -/
def projectedTail (P A : Operator H) : Operator H :=
  (1 - P) * A * (1 - P)

theorem projectedTail_positive (P A : Operator H) (hP : IsStarProjection P)
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (projectedTail P A) := by
  have hQ : IsStarProjection (1 - P) := hP.one_sub
  have h := hA.conj_adjoint (1 - P)
  have hQsym : (1 - P).IsSymmetricProjection :=
    LinearMap.isStarProjection_iff_isSymmetricProjection.mp hQ
  rw [hQsym.2.adjoint_eq] at h
  change LinearMap.IsPositive ((1 - P).comp (A.comp (1 - P)))
  exact h

theorem projectedTail_trace (P A : Operator H) (hP : IsStarProjection P) :
    LinearMap.trace Complex H (projectedTail P A) =
      LinearMap.trace Complex H ((1 - P) * A) := by
  have hQ : IsStarProjection (1 - P) := hP.one_sub
  rw [projectedTail, LinearMap.trace_mul_cycle]
  rw [hQ.isIdempotentElem.eq]

theorem operatorNorm_projection_le (P : Operator H) (hP : IsStarProjection P) :
    operatorNorm P ≤ 1 := by
  have hPc : IsStarProjection (LinearMap.toContinuousLinearMap P) :=
    LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr hP
  obtain ⟨U, _hUProjection, hU⟩ :=
    isStarProjection_iff_eq_starProjection.mp hPc
  rw [operatorNorm, hU]
  exact U.starProjection_norm_le

theorem trace_projection_add_complement (P A : Operator H) :
    LinearMap.trace Complex H (P * A) +
      LinearMap.trace Complex H ((1 - P) * A) =
        LinearMap.trace Complex H A := by
  rw [← map_add, ← add_mul]
  simp

theorem traceNorm_projectedTail_eq_re_trace [Nontrivial H]
    (P A : Operator H) (hP : IsStarProjection P) (hA : LinearMap.IsPositive A) :
    traceNorm (projectedTail P A) =
      Complex.re (LinearMap.trace Complex H ((1 - P) * A)) := by
  rw [traceNorm_eq_re_trace_of_positive (projectedTail P A)
    (projectedTail_positive P A hP hA)]
  rw [projectedTail_trace P A hP]

theorem re_trace_complement_nonneg [Nontrivial H]
    (P A : Operator H) (hP : IsStarProjection P) (hA : LinearMap.IsPositive A) :
    0 ≤ Complex.re (LinearMap.trace Complex H ((1 - P) * A)) := by
  rw [← traceNorm_projectedTail_eq_re_trace P A hP hA]
  exact traceNorm_nonneg _

namespace DensityOperator

theorem traceNorm_projectedTail_eq_complementTrace [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H) :
    traceNorm (projectedTail P rho.toOperator) =
      Complex.re (LinearMap.trace Complex H ((1 - P) * rho.toOperator)) :=
  traceNorm_projectedTail_eq_re_trace P rho.toOperator hP rho.positive

theorem projectionTrace_add_complementTrace (P : Operator H) (rho : DensityOperator H) :
    LinearMap.trace Complex H (P * rho.toOperator) +
      LinearMap.trace Complex H ((1 - P) * rho.toOperator) = 1 := by
  rw [trace_projection_add_complement, rho.trace_one]

end DensityOperator

end

end Semantics
end QEC
