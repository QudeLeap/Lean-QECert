import QEC.Coding.ExpanderCodes.LPSOriginalNormalizedIntegral

/-!
# Actual cusp germs under normalization

One genuine nonzero cusp phase transfers punctured chart equality to pullback equality near infinity. Normalization preserves that germ. Nonnegative actual cusp orders then produce analytic normalized cusp representatives and genuine boundedness.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

/-- Punctured equality in the actual cusp chart gives equality of genuine cusp pullbacks near infinity. -/
lemma lpsOriginalCuspPullback_eventuallyEq
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F G : LPSOriginalFilledCurve N → ℂ)
    (he : letI := lpsOriginalFilledTopology N
      (F ∘ (lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm)
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (G ∘ (lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm)) :
    (fun τ : ℍ => F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))
      =ᶠ[UpperHalfPlane.atImInfty]
    (fun τ : ℍ => G (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let D : LPSOriginalFilledCurve N → ℂ := fun x => F x - G x
  obtain ⟨α, hα, hphase⟩ := lpsOriginalFilledMeromorphic_cusp_phase N ρ D
  have hw : 0 < w := lpsOriginalCuspGroup_width_positive N r
  have ht : Tendsto (fun τ : ℍ => α * Function.Periodic.qParam w (τ : ℂ))
      UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero] using
        tendsto_const_nhds.mul (UpperHalfPlane.qParam_tendsto_atImInfty hw)
    · exact Filter.Eventually.of_forall (fun τ =>
        mul_ne_zero hα (Function.Periodic.qParam_ne_zero _))
  have hh := ht.eventually he
  filter_upwards [hh, Filter.preimage_mem_comap (Filter.Ioi_mem_atTop (1 : ℝ))]
    with τ hτ hhigh
  have hp := hphase ⟨τ, hhigh⟩
  change D (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧) =
    D ((lpsOriginalFilledCuspChart N c).symm
      (α * Function.Periodic.qParam w (τ : ℂ))) at hp
  change F _ = G _ at hτ
  dsimp only [D] at hp
  rw [hτ, sub_self] at hp
  exact sub_eq_zero.mp hp

/-- Normalization preserves the actual cusp pullback germ near infinity. -/
lemma lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    (fun τ : ℍ => lpsOriginalNormalizedFilledFunction N hN F
      (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))
      =ᶠ[UpperHalfPlane.atImInfty]
    (fun τ : ℍ => F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply lpsOriginalCuspPullback_eventuallyEq
  let x : LPSOriginalFilledCurve N := Sum.inr (lpsOriginalCuspOrbit N ρ)
  have hx : chartAt ℂ x x = (0 : ℂ) :=
    lpsOriginalFilledCuspChart_cusp N (lpsOriginalCuspOrbit N ρ)
  have hz : (0 : ℂ) ∈ (chartAt ℂ x).target := hx ▸ mem_chart_target ℂ x
  exact ((chartNormalizedMeromorphicFunction_chart_eventually F hF x 0 hz).filter_mono nhdsWithin_le_nhds).trans
    (MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (hF x) hz)

/-- Nonnegative actual cusp orders make the normalized cusp representatives analytic at zero. -/
lemma lpsOriginalNormalizedFilledFunction_cusp_analytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun q => lpsOriginalNormalizedFilledFunction N hN F
      ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let x : LPSOriginalFilledCurve N := Sum.inr c
  have hx : chartAt ℂ x x = (0 : ℂ) := lpsOriginalFilledCuspChart_cusp N c
  have hz : (0 : ℂ) ∈ (chartAt ℂ x).target := hx ▸ mem_chart_target ℂ x
  have ho : 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) 0 := hx ▸ hc c
  exact chartNormalizedMeromorphicFunction_analyticAt F hF x 0 hz ho

/-- The analytic normalized cusp extension gives genuine boundedness near every cusp. -/
lemma lpsOriginalNormalizedFilledFunction_cusp_bounded
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (ρ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      lpsOriginalNormalizedFilledFunction N hN F
        (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  have hb := lpsOriginalFilledMeromorphic_delta_cusp_bounded N ρ
    (lpsOriginalNormalizedFilledFunction N hN F) 0
    (by simpa only [pow_zero, one_mul] using
      (lpsOriginalNormalizedFilledFunction_cusp_analytic N hN F hF hc
        (lpsOriginalCuspOrbit N ρ)))
  simpa only [pow_zero, one_mul] using hb

end
end QEC.Coding.TannerLiftedProduct
