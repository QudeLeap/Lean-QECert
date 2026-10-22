import QEC.Coding.ExpanderCodes.LPSOriginalDifferentialCoefficients

/-!
# LPSOriginalDifferentialGluing

Concrete coefficients on the same original filled curve satisfy all four actual derivative-weighted chart transition laws.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

/-- The concrete coefficient family on the actual preferred interior and cusp charts. -/
def lpsOriginalFilledCoordinateCoefficient (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    LPSOriginalFilledCurve N → ℂ → ℂ :=
  Sum.elim (fun _ => (f : ℍ→ℂ)∘UpperHalfPlane.ofComplex)
    (fun c => lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c))

/-- Every actual preferred-chart target has an analytic differential coefficient. -/
lemma lpsOriginalFilledCoordinateCoefficient_analytic (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    AnalyticAt ℂ (lpsOriginalFilledCoordinateCoefficient N f x) z := by
  cases x with
  | inl y =>
    have hp := lpsOriginalFilledInteriorChart_target_pos N hN y z hz
    exact lpsOriginalCuspForm_ofComplex_analytic N f ⟨z,hp⟩
  | inr c =>
    let r := lpsOriginalCuspRepresentative N c
    have hw : 0<(lpsOriginalCuspGroup N r).strictWidthInfty :=
      lpsOriginalCuspGroup_width_positive N r
    have he : Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N r).strictWidthInfty)<1 := by
      rw [Real.exp_lt_one_iff]
      exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hw
    change ‖z‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N r).strictWidthInfty) at hz
    exact lpsOriginalCuspQCoefficient_analytic N f r z (hz.trans he)

/-- The actual interior-to-cusp overlap satisfies the derivative-weighted differential law. -/
lemma lpsOriginalFilled_interior_cusp_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
        (lpsOriginalFilledCuspChart N c)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)
    lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) (e z) *
      deriv e z = f (UpperHalfPlane.ofComplex z) := by
  let := lpsOriginalFilledTopology N
  change z∈(lpsOriginalFilledInteriorChart N hN x).target ∧
    (lpsOriginalFilledInteriorChart N hN x).symm z∈
      (lpsOriginalFilledCuspChart N c).source at hz
  have hp := lpsOriginalFilledInteriorChart_target_pos N hN x z hz.1
  let τ : ℍ := ⟨z,hp⟩
  have hx := hz.2
  rw [lpsOriginalFilledInteriorChart_symm] at hx
  rw [lpsOriginalFilledCuspChart_source,UpperHalfPlane.ofComplex_apply_of_im_pos hp] at hx
  have hd := lpsOriginalCuspCoordinate_differential_pullback N f
    (lpsOriginalCuspRepresentative N c) τ hx
  have he : (((lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)) : ℂ→ℂ)=
      (fun w : ℂ => lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex w)))) := by
    funext w
    rw [OpenPartialHomeomorph.trans_apply,lpsOriginalFilledInteriorChart_symm]
    rfl
  dsimp only
  rw [he]
  simpa only [τ,UpperHalfPlane.ofComplex_apply_of_im_pos hp] using hd

/-- The actual cusp-to-interior overlap satisfies the reverse differential law. -/
lemma lpsOriginalFilled_cusp_interior_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledInteriorChart N hN x)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledInteriorChart N hN x)
    f (UpperHalfPlane.ofComplex (e z)) * deriv e z =
      lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z := by
  let := lpsOriginalFilledTopology N
  let e := (lpsOriginalFilledCuspChart N c).symm.trans
    (lpsOriginalFilledInteriorChart N hN x)
  have hf := lpsOriginalFilled_interior_cusp_differential N hN f x c (e z)
    (e.map_source hz)
  have ha := lpsOriginalFilled_interior_cusp_analytic N hN x c (e z) (e.map_source hz)
  have hi := lpsOpenPartialHomeomorph_inverse_deriv e.symm (e z)
    (e.map_source hz) ha.1 ha.2
  have hsym : e.symm=(lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c) := by
    simp only [e,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  rw [←hsym] at hf
  have hf' : lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z *
      deriv e.symm (e z) = f (UpperHalfPlane.ofComplex (e z)) := by
    simpa only [e.left_inv hz] using hf
  have hi' : deriv e z * deriv e.symm (e z) = 1 := by
    simpa only [OpenPartialHomeomorph.symm_symm,e.left_inv hz] using hi
  dsimp only
  rw [←hf',mul_assoc,mul_comm (deriv e.symm (e z)) (deriv e z),hi',mul_one]

/-- True cusp overlaps are either identical or empty and satisfy the differential law. -/
lemma lpsOriginalFilled_cusp_cusp_differential (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N d)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledCuspChart N c).symm.trans (lpsOriginalFilledCuspChart N d)
    lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) (e z) *
      deriv e z = lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z := by
  let := lpsOriginalFilledTopology N
  by_cases hcd : c=d
  · subst d
    have he : (((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledCuspChart N c)) : ℂ→ℂ) =ᶠ[𝓝 z] id := by
      have hn : ∀ᶠ w in 𝓝 z, w∈(lpsOriginalFilledCuspChart N c).target :=
        (lpsOriginalFilledCuspChart N c).open_target.mem_nhds hz.1
      filter_upwards [hn] with w hw
      exact (lpsOriginalFilledCuspChart N c).right_inv hw
    dsimp only
    rw [he.eq_of_nhds,he.deriv_eq,deriv_id,mul_one]
    rfl
  · have hd := lpsOriginalFilledCuspPartialEquiv_sources_disjoint N
      (lpsOriginalCuspRepresentative N c) (lpsOriginalCuspRepresentative N d)
      (by simpa only [lpsOriginalCuspRepresentative_orbit] using hcd)
    exact False.elim (Set.disjoint_left.mp hd
      ((lpsOriginalFilledCuspChart N c).map_target hz.1) hz.2)

/-- True original quotient interior overlaps preserve the original differential. -/
lemma lpsOriginalFilled_interior_interior_differential (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
        (lpsOriginalFilledInteriorChart N hN y)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledInteriorChart N hN y)
    f (UpperHalfPlane.ofComplex (e z)) * deriv e z = f (UpperHalfPlane.ofComplex z) := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective proj := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change z∈(lpsOriginalFilledInteriorChart N hN x).target ∧
    (lpsOriginalFilledInteriorChart N hN x).symm z∈
      (lpsOriginalFilledInteriorChart N hN y).source at hz
  have hpos := lpsOriginalFilledInteriorChart_target_pos N hN x z hz.1
  let τ : ℍ := ⟨z,hpos⟩
  have hm := hz.2
  rw [lpsOriginalFilledInteriorChart_symm,
    UpperHalfPlane.ofComplex_apply_of_im_pos hpos] at hm
  change Sum.inl (proj τ)∈Sum.inl ''(chartAt ℂ y).source at hm
  obtain ⟨a,ha,he⟩ := hm
  have hs : proj τ∈(chartAt ℂ y).source := by
    have he' := Sum.inl.inj he
    rwa [he'] at ha
  change proj τ∈((hf.localInverseAt (r y)).trans UpperHalfPlane.ofComplex.symm).source at hs
  have hd := lpsGamma0_localInverse_differential_pullback N hN f (r y) τ hs.1
  have heq : (((lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledInteriorChart N hN y)) : ℂ→ℂ)=
      (fun w : ℂ => ((hf.localInverseAt (r y)) (proj (UpperHalfPlane.ofComplex w)) : ℂ)) := by
    funext w
    rw [OpenPartialHomeomorph.trans_apply,lpsOriginalFilledInteriorChart_symm]
    change ((chartAt ℂ y).lift_openEmbedding
      (lpsOriginalFilledTopology_interior_openEmbedding N)) (Sum.inl (proj (UpperHalfPlane.ofComplex w)))=_
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  dsimp only
  rw [heq]
  simp only [UpperHalfPlane.ofComplex_apply]
  simpa only [τ,UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using hd

/-- All four actual preferred-chart transitions satisfy the derivative-weighted cocycle. -/
lemma lpsOriginalFilledCoordinateCoefficient_cocycle (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    let e := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    lpsOriginalFilledCoordinateCoefficient N f y (e z) * deriv e z =
      lpsOriginalFilledCoordinateCoefficient N f x z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl x =>
    cases y with
    | inl y => exact lpsOriginalFilled_interior_interior_differential N hN f x y z hz
    | inr c => exact lpsOriginalFilled_interior_cusp_differential N hN f x c z hz
  | inr c =>
    cases y with
    | inl x => exact lpsOriginalFilled_cusp_interior_differential N hN f x c z hz
    | inr d => exact lpsOriginalFilled_cusp_cusp_differential N f c d z hz


end
end QEC.Coding.TannerLiftedProduct
