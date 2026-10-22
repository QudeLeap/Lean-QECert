import QEC.Coding.AlgebraicGeometry.Places.ArtinSchreierOrder
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialLocal
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Orders at specified primes of a local integral closure

The place is constructed from the given height-one prime. Restriction scales
orders by its actual ramification index, not by an assumed pole/different law.
This isolates the reusable calculation from the source-tower compositum proof.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

variable {k : Type*} [Field k] [Finite k]

/-- The global place attached to a supplied height-one prime. It is
definitionally that prime's valuation, so it does not choose an upper
prime. -/
noncomputable def integralClosurePlace
    {O L : Type*} [CommRing O] [_root_.Field L] [Algebra k L]
    [Algebra O L] [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L)) :
    GlobalPlace k L where
  valuation := H.valuation L
  normalized := H.valuation_surjective L

private theorem integralClosurePlace_order_integral
    {O L : Type*} [CommRing O] [_root_.Field L] [Algebra k L]
    [Algebra O L] [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    {z : integralClosure O L} (hz : z ≠ 0) :
    (integralClosurePlace (k := k) H).order
        (algebraMap (integralClosure O L) L z) =
      (multiplicity H.asIdeal (Ideal.span {z}) : ℤ) := by
  unfold integralClosurePlace GlobalPlace.order
  rw [H.valuation_of_algebraMap,
    H.intValuation_eq_exp_neg_multiplicity hz, WithZero.log_exp]
  ring

private theorem integralClosurePlace_order_integralUnit
    {O L : Type*} [CommRing O] [_root_.Field L] [Algebra k L]
    [Algebra O L] [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    (u : Oˣ) :
    (integralClosurePlace (k := k) H).order
        (algebraMap (integralClosure O L) L
          (algebraMap O (integralClosure O L) (u : O))) = 0 := by
  let C := integralClosure O L
  let uC : Cˣ := Units.map (algebraMap O C) u
  have huC_ne : (uC : C) ≠ 0 := uC.ne_zero
  change (integralClosurePlace (k := k) H).order
    (algebraMap C L (uC : C)) = 0
  rw [integralClosurePlace_order_integral H huC_ne]
  have huC_unit : IsUnit (uC : C) := uC.isUnit
  rw [Ideal.span_singleton_eq_top.mpr huC_unit]
  norm_cast
  have hH_nonunit : ¬ IsUnit H.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact H.isPrime.ne_top
  simpa only [Ideal.one_eq_top] using multiplicity_of_one_right hH_nonunit

/-- The supplied height-one contraction scales a lower uniformizer by its
ramification index. -/
private theorem integralClosurePlace_order_uniformizer
    {K L : Type*} [_root_.Field K] [_root_.Field L] [Algebra k K]
    [Algebra k L] [Algebra K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L)) :
    (integralClosurePlace (k := k) H).order
        (algebraMap K L
          (algebraMap P.valuationRing K P.uniformizerInValuationRing)) =
      ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal : ℤ) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let t : O := P.uniformizerInValuationRing
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    intro x y hxy
    apply ValuationSubring.subtype_injective O
    apply (algebraMap K L).injective
    simp only [IsScalarTower.algebraMap_apply O K L,
      ValuationSubring.algebraMap_apply] at hxy
    exact hxy
  letI : Module.IsTorsionFree O C := IsIntegralClosure.isTorsionFree O L
  letI : FaithfulSMul O C :=
    Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : IsScalarTower O C L := IsScalarTower.of_algebraMap_eq' rfl
  have hm_ne_bot : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hmap_ne_bot : Ideal.map (algebraMap O C) m ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hm_ne_bot
  have hm_span : m = Ideal.span ({t} : Set O) := by
    simpa only [O, m, t] using P.maximalIdeal_eq_span_uniformizer
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hm_span
  have ht_ne : algebraMap O C t ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective O C).ne ht_irreducible.ne_zero
  have hspan : Ideal.span ({algebraMap O C t} : Set C) =
      Ideal.map (algebraMap O C) m := by
    calc
      Ideal.span ({algebraMap O C t} : Set C) =
          Ideal.map (algebraMap O C) (Ideal.span ({t} : Set O)) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap O C) m := by rw [← hm_span]
  rw [← IsScalarTower.algebraMap_apply O K L,
    IsScalarTower.algebraMap_apply O C L]
  rw [integralClosurePlace_order_integral H ht_ne]
  norm_cast
  calc
    multiplicity H.asIdeal (Ideal.span ({algebraMap O C t} : Set C)) =
        multiplicity H.asIdeal (Ideal.map (algebraMap O C) m) := by rw [hspan]
    _ = m.ramificationIdx' H.asIdeal :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        hmap_ne_bot H.isPrime).symm

private theorem integralClosureOrder_zpow
    {k L : Type*} [_root_.Field k] [Finite k] [_root_.Field L] [Algebra k L]
    (P : GlobalPlace k L) (z : L) (n : ℤ) :
    P.order (z ^ n) = n * P.order z := by
  unfold GlobalPlace.order
  rw [map_zpow₀, WithZero.log_zpow]
  simp only [smul_eq_mul]
  ring

private theorem integralClosureOrder_baseUnit
    {K : Type*} [_root_.Field K] [Algebra k K]
    (P : GlobalPlace k K) (u : P.valuationRingˣ) :
    P.order (algebraMap P.valuationRing K (u : P.valuationRing)) = 0 := by
  let u' : P.valuationRing.unitGroup :=
    P.valuationRing.unitGroupMulEquiv.symm u
  have hu' : P.valuation ((u' : Kˣ) : K) = 1 :=
    (Valuation.mem_unitGroup_iff K P.valuation (u' : Kˣ)).mp u'.property
  have hu : P.valuation
      (algebraMap P.valuationRing K (u : P.valuationRing)) = 1 := by
    simp only [u', ValuationSubring.coe_unitGroupMulEquiv_symm_apply] at hu'
    exact hu'
  unfold GlobalPlace.order
  rw [hu, WithZero.log_one]
  simp

/-- Normalized order at the place defined by a supplied height-one
contraction scales lower nonzero elements by its ramification index.  This is
the regular arm's zero-correction transport; it is proved from the supplied
contraction, not assumed as a selected-place property. -/
theorem integralClosurePlace_order_algebraMap
    {K L : Type*} [_root_.Field K] [_root_.Field L] [Algebra k K]
    [Algebra k L] [Algebra K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [hDedekind : IsDedekindDomain
      (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L))
    (y : K) (hy : y ≠ 0) :
    (integralClosurePlace (k := k) H).order
        (algebraMap K L y) =
      ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal : ℤ) *
        P.order y := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let Q := integralClosurePlace (k := k) H
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible P.uniformizerInValuationRing := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer
      P.uniformizerInValuationRing).mpr
    exact P.maximalIdeal_eq_span_uniformizer
  obtain ⟨n, u, hyfactor⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      ht_irreducible hy
  have hyfactor' :
      y = algebraMap O K (u : O) *
        algebraMap O K P.uniformizerInValuationRing ^ n := by
    simpa only [O, Units.smul_def, Algebra.smul_def] using hyfactor
  have ht_lower :
      P.order (algebraMap O K P.uniformizerInValuationRing) = 1 := by
    change P.order P.uniformizer = 1
    exact P.order_uniformizer
  have hu_lower : P.order (algebraMap O K (u : O)) = 0 := by
    simpa only [O] using
      integralClosureOrder_baseUnit P u
  have htK_ne : algebraMap O K P.uniformizerInValuationRing ≠ 0 := by
    intro ht0
    apply ht_irreducible.ne_zero
    apply Subtype.ext
    exact ht0
  have huK_ne : algebraMap O K (u : O) ≠ 0 := by
    intro hu0
    apply u.ne_zero
    apply Subtype.ext
    exact hu0
  have hn_lower : P.order y = n := by
    rw [hyfactor', P.order_mul huK_ne (zpow_ne_zero n htK_ne),
      integralClosureOrder_zpow, hu_lower, ht_lower]
    ring
  have hyfactorUpper := congrArg (algebraMap K L) hyfactor'
  simp only [map_mul, map_zpow₀] at hyfactorUpper
  have hu_upper : Q.order
      (algebraMap K L (algebraMap O K (u : O))) = 0 := by
    letI : IsScalarTower O C L := IsScalarTower.of_algebraMap_eq' rfl
    rw [← IsScalarTower.algebraMap_apply O K L,
      IsScalarTower.algebraMap_apply O C L]
    exact integralClosurePlace_order_integralUnit H u
  have ht_upper : Q.order
      (algebraMap K L (algebraMap O K P.uniformizerInValuationRing)) =
        (m.ramificationIdx' H.asIdeal : ℤ) := by
    simpa only [O, m, Q] using
      integralClosurePlace_order_uniformizer P H
  calc
    Q.order (algebraMap K L y) =
        Q.order (algebraMap K L (algebraMap O K (u : O)) *
          algebraMap K L (algebraMap O K P.uniformizerInValuationRing) ^ n) := by
      rw [hyfactorUpper]
    _ = Q.order (algebraMap K L (algebraMap O K (u : O))) +
        Q.order (algebraMap K L
          (algebraMap O K P.uniformizerInValuationRing) ^ n) := by
      apply GlobalPlace.order_mul
      · simpa only [map_zero] using (algebraMap K L).injective.ne huK_ne
      · exact zpow_ne_zero n (by
          simpa only [map_zero] using (algebraMap K L).injective.ne htK_ne)
    _ = 0 + n * (m.ramificationIdx' H.asIdeal : ℤ) := by
      rw [integralClosureOrder_zpow, hu_upper, ht_upper]
    _ = (m.ramificationIdx' H.asIdeal : ℤ) * P.order y := by
      rw [hn_lower]
      ring


/-- At any specified prime of a genuine degree-two extension, the literal
Artin--Schreier equation preserves the normalized-pole/regular alternative.
Order compatibility and the ramification bound are derived here from the
prime and the field degree; the caller supplies only the equation and the
lower order, as in the basic edges of Property (A). -/
theorem integralClosurePlace_artinSchreier_order_dichotomy
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [Algebra.IsSeparable K L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    (H : IsDedekindDomain.HeightOneSpectrum
      (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (hdegree : Module.finrank K L = 2)
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    (integralClosurePlace (k := k) H).order y = -1 ∨
      0 ≤ (integralClosurePlace (k := k) H).order y := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  letI : Module.IsTorsionFree O L :=
    Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.IsTorsionFree O C := IsIntegralClosure.isTorsionFree O L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have he0 : 0 < m.ramificationIdx' H.asIdeal :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver H.asIdeal hm0)
  have he2 : m.ramificationIdx' H.asIdeal ≤ 2 := by
    rw [← hdegree]
    exact Ideal.ramificationIdx_le_finrank C K L H.asIdeal
  apply P.artinSchreier_root_order_dichotomy
    (integralClosurePlace (k := k) H) a y (m.ramificationIdx' H.asIdeal) he0 he2 hy
  · by_cases ha0 : a = 0
    · simp [ha0, GlobalPlace.order]
    · exact integralClosurePlace_order_algebraMap P H a ha0
  · exact ha

end

end QEC.Coding.AlgebraicGeometry
