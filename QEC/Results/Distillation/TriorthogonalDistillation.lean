import QEC.Distillation.Triorthogonal.Concatenation

/-!
# Triorthogonal-code distillation

Final theorem assembly over the reusable Distillation methods.
-/

noncomputable section

namespace QEC.Distillation.Triorthogonal.BH12Concatenation

open Semantics
open BH12EvenFamily BH12NoisyInjection BH12Protocol
open Filter Topology

/-- The complete source-backed BH12 public realization for one positive
family index.  Every component is derived from the concrete #753--#756
construction: the explicit CSS family, its corrected transversal action, the
independent diagonal physical input and syndrome-postselected run, the
level-indexed fresh-parent expected-yield accounting, and the exact finite
block exponent.  The multi-level predicate is intentionally additive rather
than an invalid fixed-register `DistillationProtocolFamily`. -/
theorem bh12TriorthogonalCodeDistillation (q : Nat) (p : ErrorParameter)
    (hq : 0 < q) (hp : 0 < p.rate)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    bh12InputCount q = 3 * bh12OutputCount q + 8 ∧
      Fintype.card (OddRow q) = bh12OutputCount q ∧
        Coding.PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 ∧
          ((family q).encodedCode (isTriorthogonal q)).ImplementsLogicalGate
              (family q).correctedAllSiteT (allSiteT (Index := OddRow q)) ∧
            (InputErrorModel.independent (bh12IndependentInputModel q p)).Permits
                (noisyResources q p) ∧
              (∀ port : OddRow q, ∃ hsuccess : 0 < rawSuccessMass q p,
                0 < (bh12ActualRun q p).successProbability ∧
                  bh12SelectedPortTransportedDensity q p port =
                    OneQubit.diagonalAResource
                      (bh12DecodedMarginalErrorParameter q p hsuccess port) ∧
                  (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
                    quadraticCoefficient q * p.rate ^ 2) ∧
                DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                  (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
                  (bh12PathScheduleTargetError q p)
                  (fun index =>
                    (bh12PathParameter q p index.depth index.path).rate)
                  (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
                  (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) ∧
                  (∀ path : depthOutputPath q 1,
                    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong 1 path =
                      (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost (path 0)) ∧
                    (∀ epsilon : ℝ, 0 < epsilon →
                      ∃ z : Nat, ∀ path : depthOutputPath q z,
                        0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
                          0 < (bh12PathRun q p z path).successProbability ∧
                            (∀ port : OddRow q,
                              bh12PathSelectedPortTransportedDensity q p z path port =
                                OneQubit.diagonalAResource
                                  (bh12TotalNextParameter q
                                    (bh12PathParameter q p z path) port)) ∧
                              (bh12PathParameter q p z path).rate ≤ epsilon) ∧
                      bh12BlockExponent q =
                        Real.log (((3 * bh12OutputCount q + 8 : Nat) : ℝ) /
                          (bh12OutputCount q : ℝ)) / Real.log 2 ∧
                        Tendsto (fun index : Nat => bh12BlockExponent (index + 1)) atTop
                          (𝓝 (Real.log 3 / Real.log 2)) ∧
                          bh12BlockExponent q ≠ Real.log 3 / Real.log 2 ∧
                            (∀ k : Nat, Even k → 0 < k →
                              ∃ index : Nat, 0 < index ∧ k = logicalCount index ∧
                                bh12BlockExponent index =
                                  Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) /
                                    Real.log 2 ∧
                                  Real.log 3 / Real.log 2 < bh12BlockExponent index) := by
  refine ⟨bh12InputCount_eq_three_mul_output_add_eight q, ?_,
    pureZLogicalMinimumDistance_two hq, ?_, bh12IndependentInputModel_permits q p,
    ?_, bh12PathSchedule_physicalPolylogarithmicExpectedYieldOverhead q p hsmall
      hhalf hstrong hp hq, ?_, ?_, ?_,
    bh12BlockExponent_succ_tendsto_log_three_div_log_two,
    bh12BlockExponent_ne_log_three_div_log_two hq, ?_⟩
  · simpa [bh12OutputCount] using card_oddRow q
  · exact BinaryRowFamily.correctedAllSiteT_implements_logicalAllSiteT
      (family q) (isTriorthogonal q)
  · intro port
    obtain ⟨hsuccess, hactualSuccess, hdensity, hquadratic, _, _, _, _⟩ :=
      bh12OneStepPhysicalInvariant q p port hsmall hhalf (hstrong.trans (by norm_num))
    exact ⟨hsuccess, hactualSuccess, hdensity, hquadratic⟩
  · intro path
    exact bh12PathTypedSuccessfulOutputCost_depth_one_eq_oneLevelFamily q p hsmall
      hhalf hstrong path
  · intro epsilon hepsilon
    exact bh12PathSchedule_cofinalActualOutputError q p hsmall hhalf hstrong epsilon hepsilon
  · exact bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq hq rfl
  · intro k hk hkpos
    exact bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos hk hkpos

end QEC.Distillation.Triorthogonal.BH12Concatenation
