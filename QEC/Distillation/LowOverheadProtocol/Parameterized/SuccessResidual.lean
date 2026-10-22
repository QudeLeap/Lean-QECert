import QEC.Distillation.LowOverheadProtocol.Parameterized.PhysicalEndpoint

/-!
# Parameterized HH18 success and residual mass

This layer derives the accepted all-zero lower bound and the accepted nonzero
residual bound directly from the parameterized physical endpoint expansion,
the actual finite physical-error-word support, and the established HH18
distance theorem.  It stops before conditional decoded densities, protocol
runs, or iteration.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instSuccessClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The all-zero physical error word has its literal product Bernoulli mass
over the actual parameterized physical input carrier. -/
theorem allZeroErrorWordWeight (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    HH18NoisyInput.errorWordWeight epsilon (0 : PhysicalErrorWord m w) =
      (1 - epsilon.1) ^ physicalInputCount m w := by
  simp [HH18NoisyInput.errorWordWeight, HH18NoisyInput.bitErrorWeight,
    physicalInputCount]

/-- The actual accepted Bernoulli mass contains its nonnegative all-zero
physical-error summand. -/
theorem acceptedBernoulliMass_allZeroWord_le {w r m : Nat}
    (_h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 - epsilon.1) ^ physicalInputCount m w ≤
      acceptedBernoulliMass w r m epsilon := by
  classical
  rw [acceptedBernoulliMass]
  calc
    (1 - epsilon.1) ^ physicalInputCount m w =
        if Accepts w r m (0 : PhysicalErrorWord m w) then
          HH18NoisyInput.errorWordWeight epsilon (0 : PhysicalErrorWord m w)
        else 0 := by
      rw [if_pos (accepts_zero w r m)]
      exact (allZeroErrorWordWeight m w epsilon).symm
    _ ≤ (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then HH18NoisyInput.errorWordWeight epsilon error else 0) := by
      exact Finset.single_le_sum
        (s := physicalErrorWords m w)
        (f := fun error : PhysicalErrorWord m w =>
          if Accepts w r m error then HH18NoisyInput.errorWordWeight epsilon error else 0)
        (fun error _ => by
          by_cases haccept : Accepts w r m error
          · simp [haccept, HH18NoisyInput.errorWordWeight_nonneg epsilon error]
          · simp [haccept])
        (mem_physicalErrorWords m w 0)

/-- The accepted physical Bernoulli mass is strictly positive throughout the
declared diagonal-noise domain. -/
theorem acceptedBernoulliMass_pos {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < acceptedBernoulliMass w r m epsilon := by
  have hfactor : 0 < 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  exact lt_of_lt_of_le (pow_pos hfactor _)
    (acceptedBernoulliMass_allZeroWord_le h epsilon)

/-- The actual accepted endpoint has strictly positive Born mass for every
allowed independent diagonal resource family. -/
theorem endpointWeight_accepted_pos {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < endpointWeight h hdegree (noisyResources m w epsilon) .accepted := by
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  exact acceptedBernoulliMass_pos h epsilon

/-- The all-zero summand gives a uniform accepted-mass lower bound on the
declared `0 ≤ ε ≤ 1/2` domain. -/
theorem acceptedBernoulliMass_half_power_le {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 / 2 : ℝ) ^ physicalInputCount m w ≤ acceptedBernoulliMass w r m epsilon := by
  calc
    (1 / 2 : ℝ) ^ physicalInputCount m w ≤
        (1 - epsilon.1) ^ physicalInputCount m w := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [epsilon.property.2]
    _ ≤ acceptedBernoulliMass w r m epsilon :=
      acceptedBernoulliMass_allZeroWord_le h epsilon

/-- The actual accepted endpoint retains the uniform lower bound inherited
from its all-zero physical resource-error branch. -/
theorem endpointWeight_accepted_half_power_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 / 2 : ℝ) ^ physicalInputCount m w ≤
      endpointWeight h hdegree (noisyResources m w epsilon) .accepted := by
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  exact acceptedBernoulliMass_half_power_le h epsilon

/-- The literal mass of accepted nonzero physical error words, prior to
normalization by the actual accepted Born weight. -/
noncomputable def rawAcceptedResidualErrorMass (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  (physicalErrorWords m w).sum (fun error =>
    if Accepts w r m error ∧ error ≠ 0 then
      HH18NoisyInput.errorWordWeight epsilon error
    else 0)

theorem rawAcceptedResidualErrorMass_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 ≤ rawAcceptedResidualErrorMass w r m epsilon := by
  unfold rawAcceptedResidualErrorMass
  apply Finset.sum_nonneg
  intro error _
  by_cases hresidual : Accepts w r m error ∧ error ≠ 0
  · simp [hresidual, HH18NoisyInput.errorWordWeight_nonneg epsilon error]
  · simp [hresidual]

/-- The actual Bernoulli weight of a word whose Hamming weight is at least the
parameterized code distance is at most the matching error monomial. -/
theorem errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge {w r m : Nat}
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord m w)
    (hweight : codeDistance r w ≤ HammingWeight error) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ codeDistance r w := by
  rw [HH18NoisyInput.errorWordWeight_eq_hammingWeight]
  have hepsilon_nonneg : 0 ≤ epsilon.1 := epsilon.property.1
  have hepsilon_le_one : epsilon.1 ≤ 1 := by
    linarith [epsilon.property.2]
  have hclean_nonneg : 0 ≤ 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  have hclean_le_one : 1 - epsilon.1 ≤ 1 := by
    linarith [epsilon.property.1]
  calc
    epsilon.1 ^ HammingWeight error *
        (1 - epsilon.1) ^ (Fintype.card (PhysicalSite m w) - HammingWeight error) ≤
      epsilon.1 ^ HammingWeight error * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ hclean_nonneg hclean_le_one) (pow_nonneg hepsilon_nonneg _)
    _ = epsilon.1 ^ HammingWeight error := by ring
    _ ≤ epsilon.1 ^ codeDistance r w := by
      exact pow_le_pow_of_le_one hepsilon_nonneg hepsilon_le_one hweight

/-- Every accepted nonzero physical word is bounded by the error monomial at
the actual constructed parameterized code distance. -/
theorem acceptedNonzeroErrorWordWeight_le_codeDistance_pow {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (error : PhysicalErrorWord m w)
    (hresidual : Accepts w r m error ∧ error ≠ 0) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ codeDistance r w :=
  errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge epsilon error
    (accepted_nonzero_hammingWeight_ge_codeDistance h error hresidual.2 hresidual.1)

/-- The actual physical error-history type has exactly the binary-word
cardinality of the parameterized physical input carrier. -/
theorem physicalErrorWord_card (m w : Nat) :
    Fintype.card (PhysicalErrorWord m w) = 2 ^ physicalInputCount m w := by
  simp [PhysicalErrorWord, HH18NoisyInput.PhysicalErrorWord, physicalInputCount]

/-- The accepted nonzero residual mass is bounded by the actual finite number
of physical error words times its distance-power Bernoulli monomial. -/
theorem rawAcceptedResidualErrorMass_le_card_distance_pow {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawAcceptedResidualErrorMass w r m epsilon ≤
      (Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w := by
  unfold rawAcceptedResidualErrorMass
  calc
    (physicalErrorWords m w).sum (fun error =>
      if Accepts w r m error ∧ error ≠ 0 then
        HH18NoisyInput.errorWordWeight epsilon error
      else 0) ≤
        (physicalErrorWords m w).sum (fun _error => epsilon.1 ^ codeDistance r w) := by
      apply Finset.sum_le_sum
      intro error _
      by_cases hresidual : Accepts w r m error ∧ error ≠ 0
      · rw [if_pos hresidual]
        exact acceptedNonzeroErrorWordWeight_le_codeDistance_pow h epsilon error hresidual
      · simp [hresidual, pow_nonneg epsilon.property.1]
    _ = (physicalErrorWords m w).card * epsilon.1 ^ codeDistance r w := by simp
    _ = (Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w := by
      rw [physicalErrorWords_card]

/-- The normalized residual probability uses the actual accepted endpoint
Born mass as its denominator. -/
noncomputable def acceptedResidualError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  rawAcceptedResidualErrorMass w r m epsilon /
    endpointWeight h hdegree (noisyResources m w epsilon) .accepted

/-- The explicit finite coefficient in the distance-power residual bound. -/
noncomputable def residualCoefficient (w _r m : Nat) : ℝ :=
  (Fintype.card (PhysicalErrorWord m w) : ℝ) /
    (1 / 2 : ℝ) ^ physicalInputCount m w

/-- The finite residual coefficient is nonnegative. -/
theorem residualCoefficient_nonneg (w r m : Nat) :
    0 ≤ residualCoefficient w r m := by
  unfold residualCoefficient
  exact div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (pow_pos (by norm_num) _))

/-- The parameterized accepted residual is bounded by its explicit finite
coefficient times the actual code-distance error monomial. -/
theorem acceptedResidualError_le_residualCoefficient {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError h hdegree epsilon ≤
      residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by
  unfold acceptedResidualError residualCoefficient
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  have hsuccess : 0 < acceptedBernoulliMass w r m epsilon :=
    acceptedBernoulliMass_pos h epsilon
  have hmass : 0 ≤ rawAcceptedResidualErrorMass w r m epsilon :=
    rawAcceptedResidualErrorMass_nonneg w r m epsilon
  have hbound : 0 ≤ (Fintype.card (PhysicalErrorWord m w) : ℝ) *
      epsilon.1 ^ codeDistance r w := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg epsilon.property.1 _)
  calc
    rawAcceptedResidualErrorMass w r m epsilon / acceptedBernoulliMass w r m epsilon ≤
        ((Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w) /
          acceptedBernoulliMass w r m epsilon := by
      exact div_le_div_of_nonneg_right
        (rawAcceptedResidualErrorMass_le_card_distance_pow h epsilon) hsuccess.le
    _ ≤ ((Fintype.card (PhysicalErrorWord m w) : ℝ) * epsilon.1 ^ codeDistance r w) /
          ((1 / 2 : ℝ) ^ physicalInputCount m w) := by
      exact div_le_div_of_nonneg_left hbound (by positivity)
        (acceptedBernoulliMass_half_power_le h epsilon)
    _ = residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by
      unfold residualCoefficient
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

private theorem physicalInputCount_pos {w r m : Nat}
    (h : Admissible w r m) : 0 < physicalInputCount m w := by
  unfold physicalInputCount
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨(fun _ : Fin m => (1 : ZMod 2)), ?_⟩⟩
  rcases h with ⟨_, hwr, hrm⟩
  have hwm : w < m := by
    omega
  simpa [Coding.ReedMuller.pointWeight, HammingWeight, hammingSupport] using hwm

/-- A source-facing form of the finite residual theorem in the conventional
`(n * ε)^d` scale, where `n` is the actual physical input count. -/
theorem acceptedResidualError_le_sourceScaled {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError h hdegree epsilon ≤
      residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w := by
  calc
    acceptedResidualError h hdegree epsilon ≤
        residualCoefficient w r m * epsilon.1 ^ codeDistance r w :=
      acceptedResidualError_le_residualCoefficient h hdegree epsilon
    _ ≤ residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w := by
      apply mul_le_mul_of_nonneg_left
      · apply pow_le_pow_left₀ epsilon.property.1
        have hcount : (1 : ℝ) ≤ physicalInputCount m w := by
          exact_mod_cast (Nat.succ_le_iff.mpr (physicalInputCount_pos h))
        nlinarith [mul_le_mul_of_nonneg_right hcount epsilon.property.1]
      · exact residualCoefficient_nonneg w r m

end HH18Parameterized
end Distillation
end QEC
