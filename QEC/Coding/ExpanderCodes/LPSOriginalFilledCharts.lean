import QEC.Coding.ExpanderCodes.LPSOriginalFilledTopology
import QEC.Coding.ExpanderCodes.LPSGamma0Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# LPSOriginalFilledCharts

Actual full minimal-width q charts and lifted original interior charts form a covering complex charted space on the SAME original filled topology. Continuity uses the proved true parametrization, and exact coordinate/inverse laws are retained. Analytic compatibility is proved in LPSOriginalFilledAnalytic; no arithmetic or PK22 magnitude conclusion is claimed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

-- Actual PartialEquiv with its exact q-coordinate, now continuity proved by real parametrization.
/-- The actual minimal-width q partial equivalence is a full-disc open partial homeomorphism for the specified original filling topology. -/
def lpsOriginalFilledCuspChart (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    OpenPartialHomeomorph (LPSOriginalFilledCurve N) ℂ := by
  let := lpsOriginalFilledTopology N
  let r := lpsOriginalCuspRepresentative N c
  let D := (lpsOriginalFilledCuspPartialEquiv N r).target
  let : Nonempty D := ⟨⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N r⟩⟩
  let e := (lpsOriginalFilledTopology_param_openEmbedding N c).toOpenPartialHomeomorph
    (lpsOriginalFilledCuspParam N c)
  refine { toPartialEquiv := lpsOriginalFilledCuspPartialEquiv N r
           open_source := by
             rw [←lpsOriginalFilledCuspParam_range N c]
             exact (lpsOriginalFilledTopology_param_openEmbedding N c).isOpen_range
           open_target := lpsOriginalFilledCuspPartialEquiv_target_open N r
           continuousOn_toFun := ?_
           continuousOn_invFun := ?_ }
  · have hc : ContinuousOn (fun x => (e.symm x).val) (Set.range (lpsOriginalFilledCuspParam N c)) :=
      continuous_subtype_val.comp_continuousOn (by
        change ContinuousOn e.invFun (Set.range (lpsOriginalFilledCuspParam N c))
        have ht : e.target=Set.range (lpsOriginalFilledCuspParam N c) := by
          simp only [e,IsOpenEmbedding.toOpenPartialHomeomorph_target]
        rw [←ht]
        exact e.continuousOn_invFun)
    rw [lpsOriginalFilledCuspParam_range] at hc
    apply hc.congr
    intro x hx
    have hxr : x∈Set.range (lpsOriginalFilledCuspParam N c) := by
      rw [lpsOriginalFilledCuspParam_range];exact hx
    have hp := (lpsOriginalFilledTopology_param_openEmbedding N c).toOpenPartialHomeomorph_right_inv
      (lpsOriginalFilledCuspParam N c) hxr
    have hq := (lpsOriginalFilledCuspPartialEquiv N r).right_inv (e.symm x).property
    change lpsOriginalFilledCuspPartialEquiv N r
      (lpsOriginalFilledCuspParam N c (e.symm x))=(e.symm x).val at hq
    rw [hp] at hq
    exact hq
  · exact continuousOn_iff_continuous_domRestrict.mpr
      (lpsOriginalFilledTopology_param_continuous N c)

/-- The true filled chart retains exactly the previously constructed original q-coordinate. -/
lemma lpsOriginalFilledCuspChart_toFun (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledCuspChart N c : LPSOriginalFilledCurve N → ℂ)=
      lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c) := rfl

/-- The selected genuine cusp is the zero of its actual filled chart. -/
lemma lpsOriginalFilledCuspChart_cusp (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    lpsOriginalFilledCuspChart N c (Sum.inr c)=0 := by
  let := lpsOriginalFilledTopology N
  change lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c) (Sum.inr c)=0
  simpa only [lpsOriginalCuspRepresentative_orbit] using
    lpsOriginalFilledCuspPartialEquiv_cusp N (lpsOriginalCuspRepresentative N c)

/-- The full chart source is exactly the original punctured neighborhood plus its genuine cusp. -/
lemma lpsOriginalFilledCuspChart_source (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledCuspChart N c).source=
      lpsOriginalFilledCuspSource N (lpsOriginalCuspRepresentative N c) := rfl

/-- Every genuine cusp lies in the source of its selected true chart. -/
lemma lpsOriginalFilledCuspChart_mem_cusp (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    Sum.inr c∈(lpsOriginalFilledCuspChart N c).source := by
  let := lpsOriginalFilledTopology N
  change Sum.inr c∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source
  simpa only [lpsOriginalCuspRepresentative_orbit] using
    lpsOriginalFilledCuspPartialEquiv_cusp_mem N (lpsOriginalCuspRepresentative N c)

-- Preserve the actual already-proved original complex atlas through the true open embedding.
/-- Lift the already proved original complex quotient chart through its actual open interior embedding. -/
def lpsOriginalFilledInteriorChart (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalFilledTopology N
    OpenPartialHomeomorph (LPSOriginalFilledCurve N) ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  exact (chartAt ℂ x).lift_openEmbedding (lpsOriginalFilledTopology_interior_openEmbedding N)

/-- Every original interior point belongs to its lifted actual chart source. -/
lemma lpsOriginalFilledInteriorChart_mem (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalFilledTopology N
    Sum.inl x∈(lpsOriginalFilledInteriorChart N hN x).source := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  exact ⟨x,ChartedSpace.mem_chart_source x,rfl⟩

/-- Actual original interior charts and one true minimal-width cusp chart per genuine cusp cover the same filled space. -/
@[instance_reducible]
def lpsOriginalFilledChartedSpace (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    ChartedSpace ℂ (LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  refine { atlas := Set.range (lpsOriginalFilledInteriorChart N hN) ∪
                Set.range (lpsOriginalFilledCuspChart N)
           chartAt := Sum.elim (lpsOriginalFilledInteriorChart N hN)
                (lpsOriginalFilledCuspChart N)
           mem_chart_source := ?_
           chart_mem_atlas := ?_ }
  · intro x
    cases x with
    | inl y => exact lpsOriginalFilledInteriorChart_mem N hN y
    | inr c => exact lpsOriginalFilledCuspChart_mem_cusp N c
  · intro x
    cases x with
    | inl y => exact Or.inl ⟨y,rfl⟩
    | inr c => exact Or.inr ⟨c,rfl⟩

/-- The lifted interior inverse is exactly the original quotient projection of ofComplex, with no new lift or orbit. -/
lemma lpsOriginalFilledInteriorChart_symm (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (z : ℂ) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledInteriorChart N hN x).symm z=
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
        (UpperHalfPlane.ofComplex z)) := by
  let := lpsOriginalFilledTopology N
  let π := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective π := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change Sum.inl (((hf.localInverseAt (r x)).trans UpperHalfPlane.ofComplex.symm).symm z)=_
  simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply,OpenPartialHomeomorph.symm_symm,hf.localInverseAt_symm]

/-- Every true lifted interior chart target point lies in the actual upper half-plane. -/
lemma lpsOriginalFilledInteriorChart_target_pos (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (z : ℂ)
    (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) : 0<z.im := by
  let := lpsOriginalFilledTopology N
  let π := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  have hp : Function.Surjective π := Quotient.mk_surjective
  let r := hp.hasRightInverse.choose
  change z∈((hf.localInverseAt (r x)).trans UpperHalfPlane.ofComplex.symm).target at hz
  simpa [UpperHalfPlane.ofComplex] using hz.1


end
end QEC.Coding.TannerLiftedProduct
