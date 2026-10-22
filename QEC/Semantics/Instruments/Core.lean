import QEC.Semantics.Channels.Kraus
/-!
# Finite selective quantum instruments

This module groups the operators of a finite Kraus family into observable
outcomes. Raw branches, Born weights, normalized positive-mass branches, and
their reconstruction laws are derived from the operators; the instrument
stores none of those conclusions.
-/

universe u v w

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

/--
A finite Kraus family together with the observable outcome of each internal
Kraus index.
-/
structure FiniteInstrument (κ : Type v) [Fintype κ] (Ω : Type w) [Fintype Ω]
    (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] where
  kraus : FiniteKrausFamily κ H K
  observe : κ → Ω

namespace FiniteInstrument

variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

local instance : DecidableEq Ω := Classical.decEq Ω

/-- The raw operator contributed by one observable outcome. -/
noncomputable def branchOperator (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (A : Operator H) : Operator K :=
  ∑ i : κ, if I.observe i = outcome then
    (I.kraus.operator i).comp
      (A.comp (LinearMap.adjoint (I.kraus.operator i)))
  else 0

@[simp]
theorem branchOperator_apply (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (A : Operator H) :
    I.branchOperator outcome A =
      ∑ i : κ, if I.observe i = outcome then
        (I.kraus.operator i).comp
          (A.comp (LinearMap.adjoint (I.kraus.operator i)))
      else 0 :=
  rfl

/-- Every observable branch sends positive operators to positive operators. -/
theorem branchOperator_positive (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    {A : Operator H} (hA : LinearMap.IsPositive A) :
    LinearMap.IsPositive (I.branchOperator outcome A) := by
  classical
  unfold branchOperator
  apply LinearMap.isPositive_sum Finset.univ
  intro i _hi
  split_ifs
  · simpa [LinearMap.comp_assoc] using
      hA.adjoint_conj (LinearMap.adjoint (I.kraus.operator i))
  · exact LinearMap.isPositive_zero

/-- The real Born weight of an observable outcome on a density input. -/
noncomputable def bornWeight (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) : ℝ :=
  Complex.re
    (LinearMap.trace Complex K (I.branchOperator outcome rho.toOperator))

/-- Positivity makes the branch trace equal to its real Born weight. -/
theorem trace_branchOperator_eq_bornWeight
    (I : FiniteInstrument κ Ω H K) (outcome : Ω) (rho : DensityOperator H) :
    LinearMap.trace Complex K (I.branchOperator outcome rho.toOperator) =
      (I.bornWeight outcome rho : Complex) := by
  have htrace :=
    (I.branchOperator_positive outcome rho.positive).trace_nonneg
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp htrace).2.symm

/-- Born weights derived from Kraus branches are nonnegative. -/
theorem bornWeight_nonneg (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) :
    0 ≤ I.bornWeight outcome rho := by
  exact
    (Complex.nonneg_iff.mp
      (I.branchOperator_positive outcome rho.positive).trace_nonneg).1

/-- Summing all observable branches recovers the raw Kraus operator sum. -/
theorem sum_branchOperator_eq_inducedMap (I : FiniteInstrument κ Ω H K)
    (A : Operator H) :
    ∑ outcome : Ω, I.branchOperator outcome A =
      I.kraus.inducedMap A := by
  classical
  rw [FiniteKrausFamily.inducedMap_apply]
  unfold branchOperator
  rw [Finset.sum_comm]
  simp only [eq_comm, Fintype.sum_ite_eq']

/--
For a complete Kraus family, observable Born weights sum to the real part of
the input trace.
-/
theorem sum_bornWeight_eq_trace_re (I : FiniteInstrument κ Ω H K)
    (hComplete : I.kraus.Complete) (rho : DensityOperator H) :
    ∑ outcome : Ω, I.bornWeight outcome rho =
      Complex.re (LinearMap.trace Complex H rho.toOperator) := by
  unfold bornWeight
  rw [← Complex.re_sum, ← map_sum, I.sum_branchOperator_eq_inducedMap]
  rw [I.kraus.inducedMap_trace_preserving hComplete]

/-- Observable Born weights of a complete instrument sum to one. -/
theorem sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (hComplete : I.kraus.Complete) (rho : DensityOperator H) :
    ∑ outcome : Ω, I.bornWeight outcome rho = 1 := by
  rw [I.sum_bornWeight_eq_trace_re hComplete rho, rho.trace_one]
  norm_num

/-- Observable raw branches reconstruct the complete channel output. -/
theorem sum_branchOperator_eq_mapDensity_toOperator
    (I : FiniteInstrument κ Ω H K) (hComplete : I.kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome : Ω, I.branchOperator outcome rho.toOperator =
      ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator := by
  rw [I.sum_branchOperator_eq_inducedMap]
  rfl

private theorem positiveOperator_eq_zero_of_trace_eq_zero
    {A : Operator K} (hA : LinearMap.IsPositive A)
    (htrace : LinearMap.trace Complex K A = 0) :
    A = 0 := by
  classical
  let b := stdOrthonormalBasis Complex K
  have hmatrix :
      (LinearMap.toMatrix b.toBasis b.toBasis A).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).2 hA
  have hmatrixTrace :
      Matrix.trace (LinearMap.toMatrix b.toBasis b.toBasis A) = 0 := by
    rw [← LinearMap.trace_eq_matrix_trace Complex b.toBasis]
    exact htrace
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  simpa using (hmatrix.trace_eq_zero_iff).1 hmatrixTrace

/-- A zero Born weight forces the corresponding positive raw branch to vanish. -/
theorem branchOperator_eq_zero_of_bornWeight_eq_zero
    (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) (hzero : I.bornWeight outcome rho = 0) :
    I.branchOperator outcome rho.toOperator = 0 := by
  apply positiveOperator_eq_zero_of_trace_eq_zero
    (I.branchOperator_positive outcome rho.positive)
  rw [I.trace_branchOperator_eq_bornWeight outcome rho, hzero]
  norm_num

/--
Normalize a strictly positive observable branch.

The positivity witness is mandatory; zero-weight outcomes remain raw zero
branches rather than receiving an invented conditional state.
-/
noncomputable def conditionalDensity (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H)
    (hpos : 0 < I.bornWeight outcome rho) :
    DensityOperator K where
  toOperator :=
    ((I.bornWeight outcome rho : Complex)⁻¹) •
      I.branchOperator outcome rho.toOperator
  positive := by
    apply (I.branchOperator_positive outcome rho.positive).smul_of_nonneg
    simp [Complex.nonneg_iff, hpos.le]
  trace_one := by
    rw [map_smul, I.trace_branchOperator_eq_bornWeight outcome rho]
    simp [hpos.ne']

@[simp]
theorem conditionalDensity_toOperator (I : FiniteInstrument κ Ω H K)
    (outcome : Ω) (rho : DensityOperator H)
    (hpos : 0 < I.bornWeight outcome rho) :
    (I.conditionalDensity outcome rho hpos).toOperator =
      ((I.bornWeight outcome rho : Complex)⁻¹) •
        I.branchOperator outcome rho.toOperator :=
  rfl

/-- Weighting a positive-mass conditional density recovers its raw branch. -/
theorem bornWeight_smul_conditionalDensity_toOperator
    (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) (hpos : 0 < I.bornWeight outcome rho) :
    (I.bornWeight outcome rho : Complex) •
        (I.conditionalDensity outcome rho hpos).toOperator =
      I.branchOperator outcome rho.toOperator := by
  rw [I.conditionalDensity_toOperator outcome rho hpos]
  simp [smul_smul, hpos.ne']

/--
The positive observable branches, weighted by their Born probabilities,
reconstruct the unconditional complete-channel output. Zero-weight outcomes
are omitted only after proving that their raw branches vanish.
-/
theorem sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
    (I : FiniteInstrument κ Ω H K) (hComplete : I.kraus.Complete)
    (rho : DensityOperator H) :
    (∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
        (I.bornWeight outcome.1 rho : Complex) •
          (I.conditionalDensity outcome.1 rho outcome.2).toOperator) =
      ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator := by
  classical
  calc
    (∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
        (I.bornWeight outcome.1 rho : Complex) •
          (I.conditionalDensity outcome.1 rho outcome.2).toOperator) =
        ∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
          I.branchOperator outcome.1 rho.toOperator := by
            apply Finset.sum_congr rfl
            intro outcome _houtcome
            exact I.bornWeight_smul_conditionalDensity_toOperator
              outcome.1 rho outcome.2
    _ = ∑ outcome : Ω, I.branchOperator outcome rho.toOperator := by
          let positiveOutcomes : Finset Ω :=
            Finset.univ.filter
              (fun outcome : Ω => 0 < I.bornWeight outcome rho)
          let positiveOutcomeEquiv :
              {outcome : Ω // 0 < I.bornWeight outcome rho} ≃
                positiveOutcomes :=
            Equiv.subtypeEquivProp (by
              funext outcome
              simp [positiveOutcomes])
          have hfiltered :
              (∑ outcome ∈ positiveOutcomes,
                I.branchOperator outcome rho.toOperator) =
                ∑ outcome : Ω, I.branchOperator outcome rho.toOperator := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro outcome _houtcome hnot
            have hnpos : ¬ 0 < I.bornWeight outcome rho := by
              simpa using hnot
            have hzero : I.bornWeight outcome rho = 0 :=
              le_antisymm (not_lt.mp hnpos)
                (I.bornWeight_nonneg outcome rho)
            exact I.branchOperator_eq_zero_of_bornWeight_eq_zero
              outcome rho hzero
          calc
            (∑ outcome : {outcome : Ω //
                0 < I.bornWeight outcome rho},
              I.branchOperator outcome.1 rho.toOperator) =
                ∑ outcome : positiveOutcomes,
                  I.branchOperator outcome.1 rho.toOperator := by
                    exact Fintype.sum_equiv positiveOutcomeEquiv _ _
                      (fun _ => rfl)
            _ = ∑ outcome ∈ positiveOutcomes,
                  I.branchOperator outcome rho.toOperator := by
                    exact Finset.sum_coe_sort positiveOutcomes
                      (fun outcome : Ω =>
                        I.branchOperator outcome rho.toOperator)
            _ = ∑ outcome : Ω,
                  I.branchOperator outcome rho.toOperator :=
                    hfiltered
    _ = ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator :=
      I.sum_branchOperator_eq_mapDensity_toOperator hComplete rho

end FiniteInstrument
end
end Semantics
end QEC
