import QEC.Coding.ExpanderCodes.LPSOriginalLevelMapGeometry
import QEC.Coding.ExpanderCodes.LPSOriginalFullMeromorphicFunctionField
/-!
# Full original function-field pullback along actual levels

Every chart-meromorphic function on the original filled level-N curve pulls
back along the same filled forget-level map to the level-M curve. Its literal
upper-half-plane pullback agrees with the lower-level function. This gives an
inclusion of the entire meromorphic restriction subfields. Faithfulness and
the already proved full-field equivalence then give inclusion of the same
original generated complex function fields C(j,j_N) into C(j,j_M).

These internal lemmas support the original LPS/Hecke route behind pinned PK22
main.tex ex:Xpq:484–486 and th:qLDPC:231–238. Those claims do not directly assert
these separate modular-curve lemmas. Rational descent, arithmetic normalization,
good reduction, the second Hecke map, Frobenius/Weil, the LPS spectrum and the
exact arbitrary-field quantum family require further proofs.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
lemma lpsOriginalFilledChartMeromorphic_comp_forgetLevel
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledChartMeromorphic M (dvd_trans hN hNM)
      (F ∘ lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
  intro x z hz
  cases x with
  | inl y =>
    have hpos : 0 < z.im :=
      lpsOriginalFilledInteriorChart_target_pos M (dvd_trans hN hNM) y z hz
    have hm := lpsOriginalFilledMeromorphicPullback_meromorphic N hN F hF z hpos
    have he : (F ∘ lpsOriginalFilledForgetLevel N M hNM) ∘
        (chartAt ℂ (Sum.inl y : LPSOriginalFilledCurve M)).symm =
        lpsOriginalFilledMeromorphicPullback N F := by
      funext q
      change F (lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledInteriorChart M (dvd_trans hN hNM) y).symm q)) = _
      rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledForgetLevel_projection]
      rfl
    rw [he]
    exact hm
  | inr c =>
    let d := lpsOriginalCuspForgetLevel N M hNM c
    let eM := lpsOriginalFilledCuspChart M c
    let eN := lpsOriginalFilledCuspChart N d
    let e := lpsOriginalCuspLevelDegree N M (lpsOriginalCuspRepresentative M c)
    obtain ⟨α,hα,hαnorm,h⟩ :=
      lpsOriginalFilledForgetLevel_preferredCuspCoordinates N M hNM c
    have htarget : α*z^e ∈ eN.target := (h z hz).1
    have hm : MeromorphicAt (F ∘ eN.symm) (α*z^e) :=
      hF (Sum.inr d) (α*z^e) htarget
    have ha : AnalyticAt ℂ (fun q : ℂ => α*q^e) z :=
      analyticAt_const.mul (analyticAt_id.pow e)
    have he : (F ∘ eN.symm) ∘ (fun q : ℂ => α*q^e) =ᶠ[𝓝 z]
        (F ∘ lpsOriginalFilledForgetLevel N M hNM) ∘ eM.symm := by
      filter_upwards [eM.open_target.mem_nhds hz] with q hq
      exact (congrArg F ((h q hq).2.1)).symm
    exact (hm.comp_analyticAt (g := fun q : ℂ => α*q^e) (x := z) ha).congr (he.filter_mono nhdsWithin_le_nhds)

lemma lpsOriginalFilledMeromorphicPullback_forgetLevel
    (N M : ℕ) (hNM : N ∣ M) (F : LPSOriginalFilledCurve N → ℂ) :
    lpsOriginalFilledMeromorphicPullback M
      (F ∘ lpsOriginalFilledForgetLevel N M hNM) =
      lpsOriginalFilledMeromorphicPullback N F := by
  funext z
  rfl

lemma lpsOriginalFilledMeromorphicRestrictionSubfield_level_le
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N) :
    lpsOriginalFilledMeromorphicRestrictionSubfield N hN ≤
      lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) := by
  rintro A ⟨F,hF,hA⟩
  refine ⟨F ∘ lpsOriginalFilledForgetLevel N M hNM,
    lpsOriginalFilledChartMeromorphic_comp_forgetLevel N M hNM hN F hF,?_⟩
  rw [lpsOriginalFilledMeromorphicPullback_forgetLevel]
  exact hA
/-- Actual level inclusion for the same original generated complex function fields. -/
lemma lpsOriginalGeneratedFunctionField_level_le
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    lpsOriginalGeneratedFunctionField N hposN ≤ lpsOriginalGeneratedFunctionField M hposM := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  intro x hx
  have hn : lpsOriginalHolomorphicFractionToMeromorphicGerm x ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield N hN :=
    lpsOriginalGeneratedFunctionField_mem_full_meromorphic N hposN hN ⟨x,hx⟩
  have hm : lpsOriginalHolomorphicFractionToMeromorphicGerm x ∈
      lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) :=
    (lpsOriginalFilledMeromorphicRestrictionSubfield_level_le N M hNM hN) hn
  let A : lpsOriginalFilledMeromorphicRestrictionSubfield M (dvd_trans hN hNM) :=
    ⟨lpsOriginalHolomorphicFractionToMeromorphicGerm x,hm⟩
  let e := lpsOriginalGeneratedFullMeromorphicEquiv M hposM (dvd_trans hN hNM)
  let z : lpsOriginalGeneratedFunctionField M hposM := e.symm A
  have hz : lpsOriginalHolomorphicFractionToMeromorphicGerm z.val =
      lpsOriginalHolomorphicFractionToMeromorphicGerm x := by
    have he := congrArg Subtype.val (e.apply_symm_apply A)
    change (lpsOriginalGeneratedFullMeromorphicEquiv M hposM
      (dvd_trans hN hNM) z).val = lpsOriginalHolomorphicFractionToMeromorphicGerm x at he
    rw [lpsOriginalGeneratedFullMeromorphicEquiv_apply] at he
    exact he
  have he : z.val = x := lpsOriginalHolomorphicFractionToMeromorphicGerm_injective hz
  rw [←he]
  exact z.property

end
end QEC.Coding.TannerLiftedProduct
