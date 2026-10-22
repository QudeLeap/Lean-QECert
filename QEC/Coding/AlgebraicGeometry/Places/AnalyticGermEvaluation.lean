import QEC.Coding.AlgebraicGeometry.Places.MeromorphicGerms
import Mathlib.Topology.Instances.Complex

/-!
# Punctured meromorphic and analytic germs

The local order valuation, integral-element bounds, and analytic evaluation
are constructed from actual representatives. These lemmas are consumed by
the original normalization's point construction.
-/

namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

lemma analytic_value_eq_of_punctured_germ
    {f g : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x)
    (he : f =ᶠ[𝓝[≠] x] g) : f x = g x := by
  have hsub : Tendsto (fun z => f z - g z) (𝓝[≠] x) (𝓝 (f x - g x)) :=
    (hf.continuousAt.sub hg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hzero : (fun z => f z - g z) =ᶠ[𝓝[≠] x] (fun _ => (0 : ℂ)) :=
    he.mono (fun z hz => sub_eq_zero.mpr hz)
  have ht : Tendsto (fun z => f z - g z) (𝓝[≠] x) (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds.congr' hzero.symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub ht)

def analyticGermSubring (x : ℂ) : Subring (Germ (𝓝[≠] x) ℂ) where
  carrier := {A | ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧ A = (f : Germ (𝓝[≠] x) ℂ)}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g,hf.add hg,rfl⟩
  neg_mem' := by
    rintro A ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩

abbrev AnalyticGermRing (x : ℂ) := ↥(analyticGermSubring x)

def analyticGermRepresentative (x : ℂ) (A : AnalyticGermRing x) : ℂ → ℂ :=
  Classical.choose (show ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧
    A.val = (f : Germ (𝓝[≠] x) ℂ) from A.property)

lemma analyticGermRepresentative_spec (x : ℂ) (A : AnalyticGermRing x) :
    AnalyticAt ℂ (analyticGermRepresentative x A) x ∧
      A.val = (analyticGermRepresentative x A : Germ (𝓝[≠] x) ℂ) :=
  Classical.choose_spec (show ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧
    A.val = (f : Germ (𝓝[≠] x) ℂ) from A.property)

def analyticGermValue (x : ℂ) (A : AnalyticGermRing x) : ℂ :=
  analyticGermRepresentative x A x

lemma analyticGermValue_rep (x : ℂ) (A : AnalyticGermRing x)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f x) (he : A.val = (f : Germ (𝓝[≠] x) ℂ)) :
    analyticGermValue x A = f x := by
  obtain ⟨hg,hgerm⟩ := analyticGermRepresentative_spec x A
  have heq : (analyticGermRepresentative x A : Germ (𝓝[≠] x) ℂ) =
      (f : Germ (𝓝[≠] x) ℂ) := hgerm.symm.trans he
  exact analytic_value_eq_of_punctured_germ hg hf (Filter.Germ.coe_eq.mp heq)

def analyticGermEvaluation (x : ℂ) : AnalyticGermRing x →+* ℂ where
  toFun := analyticGermValue x
  map_one' := analyticGermValue_rep x 1 1 analyticAt_const rfl
  map_zero' := analyticGermValue_rep x 0 0 analyticAt_const rfl
  map_add' := by
    intro A B
    obtain ⟨f,hf,he⟩ := A.property
    obtain ⟨g,hg,hgerm⟩ := B.property
    rw [analyticGermValue_rep x A f hf he, analyticGermValue_rep x B g hg hgerm]
    apply analyticGermValue_rep x (A+B) (f+g) (hf.add hg)
    change A.val+B.val = _
    rw [he,hgerm]; rfl
  map_mul' := by
    intro A B
    obtain ⟨f,hf,he⟩ := A.property
    obtain ⟨g,hg,hgerm⟩ := B.property
    rw [analyticGermValue_rep x A f hf he, analyticGermValue_rep x B g hg hgerm]
    apply analyticGermValue_rep x (A*B) (f*g) (hf.mul hg)
    change A.val*B.val = _
    rw [he,hgerm]; rfl

lemma meromorphicGerm_noPole_iff_analytic (x : ℂ) (A : MeromorphicGermRing x) :
    0 ≤ meromorphicOrderValuation x A ↔ A.val ∈ analyticGermSubring x := by
  obtain ⟨f,hf,he⟩ := A.property
  change 0 ≤ germOrder x A.val ↔ ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧
    A.val = (g : Germ (𝓝[≠] x) ℂ)
  rw [he, germOrder_coe, hf.meromorphicOrderAt_nonneg_iff]
  constructor
  · rintro ⟨g,hg,heq⟩
    exact ⟨g,hg,Filter.Germ.coe_eq.mpr heq⟩
  · rintro ⟨g,hg,heq⟩
    exact ⟨g,hg,Filter.Germ.coe_eq.mp heq⟩

def meromorphicNoPoleToAnalytic (x : ℂ) :
    (AddValuation.toValuation (meromorphicOrderValuation x)).integer →+* AnalyticGermRing x where
  toFun A := by
    have hp : 0 ≤ meromorphicOrderValuation x A.val := A.property
    exact ⟨A.val.val,(meromorphicGerm_noPole_iff_analytic x A.val).mp hp⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

def meromorphicNoPoleEvaluation (x : ℂ) :
    (AddValuation.toValuation (meromorphicOrderValuation x)).integer →+* ℂ :=
  (analyticGermEvaluation x).comp (meromorphicNoPoleToAnalytic x)

lemma meromorphicNoPoleEvaluation_rep (x : ℂ)
    (A : (AddValuation.toValuation (meromorphicOrderValuation x)).integer)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f x)
    (he : A.val.val = (f : Germ (𝓝[≠] x) ℂ)) :
    meromorphicNoPoleEvaluation x A = f x :=
  analyticGermValue_rep x (meromorphicNoPoleToAnalytic x A) f hf he

lemma meromorphicNoPoleEvaluation_eq_zero_iff_order_pos
    (x : ℂ) (A : (AddValuation.toValuation (meromorphicOrderValuation x)).integer) :
    meromorphicNoPoleEvaluation x A = 0 ↔ 0 < meromorphicOrderValuation x A.val := by
  have hp : 0 ≤ meromorphicOrderValuation x A.val := A.property
  obtain ⟨f,hf,he⟩ := (meromorphicGerm_noPole_iff_analytic x A.val).mp hp
  rw [meromorphicNoPoleEvaluation_rep x A f hf he]
  change f x = 0 ↔ 0 < germOrder x A.val.val
  rw [he,germOrder_coe]
  have ht : Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
    hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro hz
    exact (tendsto_zero_iff_meromorphicOrderAt_pos hf.meromorphicAt).mp (hz ▸ ht)
  · intro ho
    exact tendsto_nhds_unique ht (tendsto_zero_of_meromorphicOrderAt_pos ho)

end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
