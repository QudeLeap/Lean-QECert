import QEC.Coding.ExpanderCodes.LPSOriginalFunctionField
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Algebra.Field.Basic

/-!
# Genuine meromorphic germ fields on the upper half plane

This module belongs to the source-grounded original LPS analytic proof closure.
Milne, *Modular Functions and Modular Forms*, Theorem 6.1 (PDF85 / printed82)
and Propositions 1.16–1.18 motivate the genuine function-field degree argument.
The filled original Gamma0(N) manifold statements retain their proved scope
4 divides N, including the actual theta levels 16*q_graph^2.

The all-meromorphic objects use actual chartwise-meromorphic representatives
and genuine germ equality. They are never defined as the generated C(j,j_N).
The public arbitrary-field/all-rate PK22 theorem, arithmetic normalization,
uniform good reduction and geometric Weil estimate remain further proof work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

/-- Actual meromorphic representatives modulo codiscrete equality, with pointwise ring operations. -/
def lpsOriginalMeromorphicGermSubring (U : Set ℂ) :
    Subring (Filter.Germ (Filter.codiscreteWithin U) ℂ) where
  carrier := {A | ∃ f : ℂ → ℂ, MeromorphicOn f U ∧
    A = (f : Filter.Germ (Filter.codiscreteWithin U) ℂ)}
  zero_mem' := ⟨0, MeromorphicOn.const 0, rfl⟩
  one_mem' := ⟨1, MeromorphicOn.const 1, rfl⟩
  add_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g,hf.add hg,rfl⟩
  neg_mem' := by
    rintro A ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩

/-- The underlying ring of actual meromorphic germs on the indicated complex domain. -/
abbrev LPSOriginalMeromorphicGermRing (U : Set ℂ) :=
  ↥(lpsOriginalMeromorphicGermSubring U)

/-- Every infinite-order local germ vanishes in the actual codiscrete quotient. -/
lemma lpsOriginalMeromorphicGerm_zero_of_orders_top
    (U : Set ℂ) (f : ℂ → ℂ)
    (h : ∀ x ∈ U, meromorphicOrderAt f x = ⊤) :
    (f : Filter.Germ (Filter.codiscreteWithin U) ℂ) = 0 := by
  change (f : Filter.Germ (Filter.codiscreteWithin U) ℂ) =
    (0 : ℂ → ℂ)
  apply Filter.Germ.coe_eq.mpr
  change {z : ℂ | f z = 0} ∈ Filter.codiscreteWithin U
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp (h x hx)] with z hz
  exact Or.inl hz

/-- A nonzero meromorphic germ on a connected domain has an actual inverse representative. -/
lemma lpsOriginalMeromorphicGerm_isUnit
    (U : Set ℂ) (hU : IsConnected U)
    (A : LPSOriginalMeromorphicGermRing U) (hA : A ≠ 0) : IsUnit A := by
  obtain ⟨f,hf,he⟩ := A.property
  have hf0 : (f : Filter.Germ (Filter.codiscreteWithin U) ℂ) ≠ 0 := by
    intro h
    apply hA
    apply Subtype.ext
    exact he.trans h
  have hex : ∃ x ∈ U, meromorphicOrderAt f x ≠ ⊤ := by
    by_contra! hn
    exact hf0 (lpsOriginalMeromorphicGerm_zero_of_orders_top U f hn)
  have hall := (hf.exists_meromorphicOrderAt_ne_top_iff_forall_mem hU).mp hex
  have hne := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hf hall
  let B : LPSOriginalMeromorphicGermRing U :=
    ⟨(f⁻¹ : Filter.Germ (Filter.codiscreteWithin U) ℂ), f⁻¹, hf.inv, rfl⟩
  have hab : A*B=1 := by
    apply Subtype.ext
    change A.val * (f⁻¹ : Filter.Germ (Filter.codiscreteWithin U) ℂ)=1
    rw [he]
    change ((f*f⁻¹ : ℂ → ℂ) : Filter.Germ (Filter.codiscreteWithin U) ℂ) =
      (1 : ℂ → ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hne] with z hz
    exact mul_inv_cancel₀ hz
  exact isUnit_iff_exists_inv.mpr ⟨B,hab⟩

/-- The field structure derived from genuine meromorphic inverses on a connected domain. -/
@[instance_reducible]
def lpsOriginalMeromorphicGermField
    (U : Set ℂ) [NeBot (Filter.codiscreteWithin U)] (hU : IsConnected U) :
    Field (LPSOriginalMeromorphicGermRing U) :=
  Field.ofIsUnitOrEqZero (fun A => by
    by_cases hA : A=0
    · exact Or.inr hA
    · exact Or.inl (lpsOriginalMeromorphicGerm_isUnit U hU A hA))

/-- The genuine upper-half-plane codiscrete filter is nontrivial. -/
lemma lpsOriginalUpperHalfMeromorphicFilter_neBot :
    NeBot (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) := by
  have hi : Complex.I ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simp [UpperHalfPlane.upperHalfPlaneSet]
  have hh : NeBot (𝓝[UpperHalfPlane.upperHalfPlaneSet \ {Complex.I}] Complex.I) := by
    rw [Set.sdiff_eq, nhdsWithin_inter_of_mem
      (nhdsWithin_le_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hi))]
    infer_instance
  let := hh
  apply Filter.neBot_of_le
    (show 𝓝[UpperHalfPlane.upperHalfPlaneSet \ {Complex.I}] Complex.I ≤
      Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet from ?_)
  exact le_iSup_of_le Complex.I (le_iSup_of_le hi le_rfl)

/-- The actual meromorphic germ field on the connected upper half plane. -/
instance lpsOriginalUpperHalfMeromorphicField :
    Field (LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) := by
  letI := lpsOriginalUpperHalfMeromorphicFilter_neBot
  exact lpsOriginalMeromorphicGermField UpperHalfPlane.upperHalfPlaneSet
    (Complex.isConnected_of_upperHalfPlane subset_rfl (by
      intro z hz
      exact (show 0 < z.im from hz).le))

/-- Every actual upper-half-plane holomorphic function has a meromorphic complex representative. -/
lemma lpsOriginalHolomorphic_ofComplex_meromorphic (f : LPSOriginalHolomorphicRing) :
    MeromorphicOn (f.val ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet :=
  ((UpperHalfPlane.mdifferentiable_iff.mp f.property).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet).meromorphicOn

/-- Restrict the actual holomorphic ring to genuine upper-half-plane meromorphic germs. -/
def lpsOriginalHolomorphicToMeromorphicGerm :
    LPSOriginalHolomorphicRing →+*
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet where
  toFun f := ⟨(f.val ∘ UpperHalfPlane.ofComplex :
    Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ),
      f.val ∘ UpperHalfPlane.ofComplex,lpsOriginalHolomorphic_ofComplex_meromorphic f,rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Punctured equality and continuity make the actual holomorphic-to-germ map faithful. -/
lemma lpsOriginalHolomorphicToMeromorphicGerm_injective :
    Function.Injective lpsOriginalHolomorphicToMeromorphicGerm := by
  intro f g h
  have hh := congrArg (fun A :
    LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet => A.val) h
  have he : (f.val ∘ UpperHalfPlane.ofComplex) =ᶠ[
      Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet]
      (g.val ∘ UpperHalfPlane.ofComplex) := Filter.Germ.coe_eq.mp hh
  apply Subtype.ext
  funext τ
  have hnear : (f.val ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝[≠] (τ : ℂ)]
      (g.val ∘ UpperHalfPlane.ofComplex) := by
    have hm := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he (τ : ℂ) τ.im_pos
    have hH : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ), z ∈ UpperHalfPlane.upperHalfPlaneSet :=
      nhdsWithin_le_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    filter_upwards [hm,hH] with z hz hzin
    exact hz.resolve_right (by simpa using hzin)
  have hf := (UpperHalfPlane.mdifferentiableAt_iff.mp (f.property τ)).continuousAt
  have hg := (UpperHalfPlane.mdifferentiableAt_iff.mp (g.property τ)).continuousAt
  have heq := tendsto_nhds_unique
    (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hnear.symm)
  simpa only [Function.comp_apply,UpperHalfPlane.ofComplex_apply] using heq

/-- The complex algebra structure from actual constant holomorphic functions. -/
instance lpsOriginalUpperHalfMeromorphicAlgebra :
    Algebra ℂ (LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet) :=
  (lpsOriginalHolomorphicToMeromorphicGerm.comp
    (algebraMap ℂ LPSOriginalHolomorphicRing)).toAlgebra

/-- The genuine germ map preserves the actual complex constants. -/
lemma lpsOriginalHolomorphicToMeromorphicGerm_constant (c : ℂ) :
    lpsOriginalHolomorphicToMeromorphicGerm
      (algebraMap ℂ LPSOriginalHolomorphicRing c) =
      algebraMap ℂ (LPSOriginalMeromorphicGermRing
        UpperHalfPlane.upperHalfPlaneSet) c := rfl

/-- Localize the faithful holomorphic-ring map into the actual meromorphic field. -/
def lpsOriginalHolomorphicFractionToMeromorphicGerm :
    LPSOriginalHolomorphicFractionField →+*
      LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet :=
  IsFractionRing.lift lpsOriginalHolomorphicToMeromorphicGerm_injective

/-- The actual fraction embedding agrees with the original holomorphic germ map. -/
lemma lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic
    (f : LPSOriginalHolomorphicRing) :
    lpsOriginalHolomorphicFractionToMeromorphicGerm
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f) =
      lpsOriginalHolomorphicToMeromorphicGerm f :=
  IsFractionRing.lift_algebraMap _ f

/-- The holomorphic fraction field embeds faithfully into genuine meromorphic germs. -/
lemma lpsOriginalHolomorphicFractionToMeromorphicGerm_injective :
    Function.Injective lpsOriginalHolomorphicFractionToMeromorphicGerm :=
  lpsOriginalHolomorphicFractionToMeromorphicGerm.injective

end
end QEC.Coding.TannerLiftedProduct
