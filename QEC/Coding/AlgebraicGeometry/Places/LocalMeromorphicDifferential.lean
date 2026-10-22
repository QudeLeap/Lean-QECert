import QEC.Coding.AlgebraicGeometry.Places.DiscreteAnalyticOrder
import QEC.Coding.AlgebraicGeometry.Places.MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Local meromorphic coefficients and regular Kähler differentials

For a complex function field embedded in genuine punctured meromorphic germs,
construct its actual differential coefficient map. When its order ring is a
DVR and its universal differential space is one-dimensional, the image of
the local Kähler module is exactly the no-pole coefficient submodule. The
DVR uniformizer order may be any positive integer; the discrete order gap
supplies the reverse inclusion. No regularity or generator law is assumed.
-/

namespace QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
local instance : Algebra ℂ (MeromorphicGermRing a) := (germComplexConstants a).toAlgebra
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]

/-- Pull actual meromorphic order back through the field algebra map. -/
abbrev localFieldOrder : AddValuation K (WithTop ℤ) :=
  AddValuation.comap (algebraMap K (MeromorphicGermRing a)) (meromorphicOrderValuation a)

/-- The literal no-pole valuation subring of the embedded function field. -/
abbrev localValuationRing : ValuationSubring K :=
  Valuation.valuationSubring (AddValuation.toValuation (localFieldOrder K a))

/-- Differentiate the actual local germ of each function-field element. -/
def fieldLocalDerivation : Derivation ℂ K (MeromorphicGermRing a) :=
  (germCoefficientDerivation a).compAlgebraMap K

/-- Map universal field differentials to genuine differentiated local germ coefficients. -/
def fieldLocalDifferentialMap : (KaehlerDifferential ℂ K) →ₗ[K] (MeromorphicGermRing a) :=
  (fieldLocalDerivation K a).liftKaehlerDifferential

/-- Universal df maps to the derivative of its actual punctured local germ. -/
lemma fieldLocalDifferentialMap_D (f : K) :
    fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K f) =
      germDerivative a ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) f) := by
  exact (fieldLocalDerivation K a).liftKaehlerDifferential_comp_D f

/-- The valuation-ring span of df for regular field elements. -/
def localDifferentialLattice : Submodule (localValuationRing K a) (KaehlerDifferential ℂ K) :=
  Submodule.span (localValuationRing K a) (Set.range fun f : (localValuationRing K a) => KaehlerDifferential.D ℂ K (f : K))

/-- Universal differentials whose true local coefficients have no pole. -/
def analyticRegularDifferentialSubmodule : Submodule (localValuationRing K a) (KaehlerDifferential ℂ K) where
  carrier := {ω | 0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a ω)}
  zero_mem' := by simp
  add_mem' := by
    intro ω η hω hη
    change 0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a (ω + η))
    rw [map_add]
    exact (meromorphicOrderValuation a).map_le_add hω hη
  smul_mem' := by
    intro c ω hω
    change 0 ≤ meromorphicOrderValuation a
      (fieldLocalDifferentialMap K a ((c : K) • ω))
    rw [map_smul, Algebra.smul_def]
    change 0 ≤ meromorphicOrderValuation a
      ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) c.val * fieldLocalDifferentialMap K a ω)
    rw [(meromorphicOrderValuation a).map_mul]
    exact add_nonneg c.property hω

/-- Regular field functions differentiate to analytic local coefficients. -/
lemma localDifferentialLattice_le_analyticRegular :
    localDifferentialLattice K a ≤
      analyticRegularDifferentialSubmodule K a := by
  apply Submodule.span_le.mpr
  rintro ω ⟨f,rfl⟩
  change 0 ≤ meromorphicOrderValuation a
    (fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K f.val))
  rw [fieldLocalDifferentialMap_D K a]
  exact germDerivative_nonnegative a _ f.property

/-- The genuine local coefficient of dπ has order m-1 for uniformizer order m. -/
lemma uniformizerDifferential_order (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) :
    meromorphicOrderValuation a
      (fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K (π : K))) =
      ((m - 1 : ℤ) : WithTop ℤ) := by
  rw [fieldLocalDifferentialMap_D K a]
  exact germDerivative_order a _ m (ne_of_gt hm) he

/-- Positive finite uniformizer order makes its universal differential nonzero. -/
lemma uniformizerDifferential_ne_zero (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) :
    KaehlerDifferential.D ℂ K (π : K) ≠ 0 := by
  intro hz
  have ho := uniformizerDifferential_order K a π m hm he
  rw [hz,map_zero,(meromorphicOrderValuation a).map_zero] at ho
  exact WithTop.top_ne_coe ho

/-- One-dimensionality expands every universal differential in the genuine dπ basis. -/
lemma differential_uniformizer_expansion (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) (ω : (KaehlerDifferential ℂ K)) :
    ∃ f : K, ω = f • KaehlerDifferential.D ℂ K (π : K) := by
  have hp : e (KaehlerDifferential.D ℂ K (π : K)) ≠ 0 := by
    intro hz
    exact uniformizerDifferential_ne_zero K a π m hm he
      (e.injective (hz.trans (map_zero e).symm))
  refine ⟨e ω / e (KaehlerDifferential.D ℂ K (π : K)),?_⟩
  apply e.injective
  rw [map_smul]
  exact (div_mul_cancel₀ (e ω) hp).symm

variable [IsDiscreteValuationRing (localValuationRing K a)]

/-- The DVR order gap forces a no-pole differential coefficient into the regular lattice. -/
lemma analyticRegular_le_localDifferentialLattice (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) :
    analyticRegularDifferentialSubmodule K a ≤
      localDifferentialLattice K a := by
  obtain ⟨π,m,hπ,hm,he⟩ := exists_uniformizer_order (localFieldOrder K a)
  intro ω hω
  obtain ⟨f,hf⟩ := differential_uniformizer_expansion K a π m hm he e ω
  by_cases hf0 : f = 0
  · rw [hf,hf0,zero_smul]
    exact Submodule.zero_mem _
  · have hbound : 0 ≤ (localFieldOrder K a) f + ((m-1 : ℤ) : WithTop ℤ) := by
      change 0 ≤ meromorphicOrderValuation a
        (fieldLocalDifferentialMap K a ω) at hω
      rw [hf,map_smul, Algebra.smul_def] at hω
      change 0 ≤ meromorphicOrderValuation a
        ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) f *
          fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K (π : K))) at hω
      rw [(meromorphicOrderValuation a).map_mul,
        uniformizerDifferential_order K a π m hm he] at hω
      exact hω
    have hv : 0 ≤ (localFieldOrder K a) f := (valuation_uniformizer_derivative_shift (localFieldOrder K a) π hπ hm he hf0).mp hbound
    rw [hf]
    exact (localDifferentialLattice K a).smul_mem (⟨f,hv⟩ : (localValuationRing K a))
      (Submodule.subset_span ⟨π,rfl⟩)

/-- The regular df lattice equals the true analytic no-pole submodule. -/
lemma localDifferentialLattice_eq_analyticRegular (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) :
    localDifferentialLattice K a =
      analyticRegularDifferentialSubmodule K a :=
  le_antisymm (localDifferentialLattice_le_analyticRegular K a)
    (analyticRegular_le_localDifferentialLattice K a e)


/-- Literal complex constants lie in the actual local valuation ring. -/
def complexConstantsToValuationRing : ℂ →+* (localValuationRing K a) :=
  (algebraMap ℂ K).codRestrict (localValuationRing K a) (fun c => by
    change 0 ≤ meromorphicOrderValuation a ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) (algebraMap ℂ K c))
    rw [(IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)).commutes]
    change 0 ≤ meromorphicOrderValuation a (germComplexConstants a c)
    change 0 ≤ germOrder a (((fun _ : ℂ => c) : Germ (𝓝[≠] a) ℂ))
    rw [germOrder_coe]
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) a).meromorphicOrderAt_nonneg)

section LocalKaehlerImage
local instance : Algebra ℂ (localValuationRing K a) := (complexConstantsToValuationRing K a).toAlgebra
local instance : IsScalarTower ℂ (localValuationRing K a) K := .of_algebraMap_eq fun c => by rfl

omit [IsDiscreteValuationRing (localValuationRing K a)] in
/-- The regular df lattice is the image of the genuine local Kähler differential map. -/
lemma localDifferentialLattice_eq_KaehlerRange :
    localDifferentialLattice K a =
      ((KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)).liftKaehlerDifferential.range := by
  let D := (KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)
  change Submodule.span (localValuationRing K a) (Set.range D) = D.liftKaehlerDifferential.range
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f,rfl⟩
    exact ⟨KaehlerDifferential.D ℂ (localValuationRing K a) f,D.liftKaehlerDifferential_comp_D f⟩
  · rintro ω ⟨η,rfl⟩
    have hη : η ∈ Submodule.span (localValuationRing K a) (Set.range (KaehlerDifferential.D ℂ (localValuationRing K a))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hη
    · rintro _ ⟨f,rfl⟩
      rw [D.liftKaehlerDifferential_comp_D]
      exact Submodule.subset_span ⟨f,rfl⟩
    · exact Submodule.zero_mem _
    · intro ξ ζ _ _ hξ hζ
      rw [map_add]
      exact Submodule.add_mem _ hξ hζ
    · intro c ξ _ hξ
      rw [map_smul]
      exact Submodule.smul_mem _ c hξ

/-- The real local Kähler image is detected exactly by analytic coefficient regularity. -/
lemma localKaehlerRange_iff_noPole (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) (ω : (KaehlerDifferential ℂ K)) :
    ω ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a ω) := by
  rw [← localDifferentialLattice_eq_KaehlerRange K a,
    localDifferentialLattice_eq_analyticRegular K a e]
  rfl

end LocalKaehlerImage

end
end QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
