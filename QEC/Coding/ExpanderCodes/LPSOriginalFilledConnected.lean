import QEC.Coding.ExpanderCodes.LPSOriginalFilledAnalytic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ClusterPt

/-!
# LPSOriginalFilledConnected

Density of the actual original Gamma0 interior in its true cusp-gluing topology
proves connectedness of the same compact filled curve. The genuine analytic atlas
and compact complex maximum modulus prove that every global holomorphic complex
function is constant. Original arithmetic model, reduction and Weil magnitude
remain unproved; this module supplies no replacement curve or assumed topology.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Density of the actual original interior at every genuine added cusp; used by whole-curve connectedness. -/
lemma lpsOriginalFilledTopology_interior_dense (N : ℕ) [NeZero N] :
    letI := lpsOriginalFilledTopology N
    DenseRange (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  intro x
  cases x with
  | inl y => exact subset_closure ⟨y,rfl⟩
  | inr c =>
    rw [mem_closure_iff]
    intro U hU hc
    let r := lpsOriginalCuspRepresentative N c
    let e := lpsOriginalFilledCuspPartialEquiv N r
    let q0 : e.target := ⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N r⟩
    have hzero : lpsOriginalFilledCuspParam N c q0=Sum.inr c :=
      lpsOriginalFilledCuspParam_zero N c q0 rfl
    have hV : IsOpen (lpsOriginalFilledCuspParam N c ⁻¹' U) :=
      hU.preimage (lpsOriginalFilledTopology_param_continuous N c)
    have hW : IsOpen (Subtype.val '' (lpsOriginalFilledCuspParam N c ⁻¹' U)) :=
      (lpsOriginalFilledCuspPartialEquiv_target_open N r).isOpenMap_subtype_val _ hV
    have hn : (Subtype.val '' (lpsOriginalFilledCuspParam N c ⁻¹' U)).Nonempty :=
      ⟨0,q0,by change lpsOriginalFilledCuspParam N c q0∈U;rw [hzero];exact hc,rfl⟩
    obtain ⟨q,hq,hqw⟩ := (dense_compl_singleton (0:ℂ)).exists_mem_open hW hn
    obtain ⟨z,hz,he⟩ := hqw
    have hz0 : z.val≠0 := by simpa only [he,Set.mem_compl_iff,Set.mem_singleton_iff] using hq
    obtain ⟨τ,hτ,_⟩ := lpsOriginalFilledCuspParam_nonzero_lift N c z hz0
    refine ⟨lpsOriginalFilledCuspParam N c z,hz,?_⟩
    exact ⟨lpsOriginalCuspProjection N r τ,hτ.symm⟩

/-- Connectedness in the actual cusp-gluing topology; used by the global holomorphic constant theorem. -/
lemma lpsOriginalFilledTopology_connectedSpace (N : ℕ) [NeZero N] :
    letI := lpsOriginalFilledTopology N
    ConnectedSpace (LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  let : PreconnectedSpace (LPSOriginalFilledCurve N) :=
    (lpsOriginalFilledTopology_interior_dense N).preconnectedSpace
      (lpsOriginalFilledTopology_interior_continuous N)
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

/-- Every global holomorphic complex function on this same compact connected curve is constant; used to exclude a holomorphic extension of j. -/
lemma lpsOriginalFilled_holomorphic_eq_const (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : LPSOriginalFilledCurve N → ℂ)
    (hf : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ c : ℂ, f=Function.const (LPSOriginalFilledCurve N) c := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let := lpsOriginalFilledTopology_compactSpace N
  let := lpsOriginalFilledTopology_connectedSpace N
  exact hf.exists_eq_const_of_compactSpace



end
end QEC.Coding.TannerLiftedProduct
