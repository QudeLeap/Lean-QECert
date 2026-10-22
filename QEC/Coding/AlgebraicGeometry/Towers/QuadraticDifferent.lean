import QEC.Coding.AlgebraicGeometry.Differents.Transport
import QEC.Coding.AlgebraicGeometry.Places.IntegralClosureOrder
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticLocalModels

/-!
# Different ideals of literal quadratic Artin--Schreier extensions

The local model calculations are transported to the actual generated field.
At a simple pole the different is the extension of the lower maximal ideal;
at a regular parameter it is the unit ideal. These are ideal equalities, so
they apply to every upper prime, without a selected-prime uniqueness argument.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]

/-- At a normalized simple pole, the actual different is the extended
maximal ideal of the lower valuation ring. -/
theorem quadraticLiteral_different_eq_map_maximalIdeal
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (a : K) (ha : P.order a = -1)
    (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) :
    differentIdeal P.valuationRing (integralClosure P.valuationRing L) =
      Ideal.map (algebraMap P.valuationRing (integralClosure P.valuationRing L))
        (IsLocalRing.maximalIdeal P.valuationRing) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let S := QuadraticArtinSchreierField P a ha
  let B := QuadraticArtinSchreierIntegralClosure P a ha
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  let e : S ≃ₐ[K] L := quadraticSimplePoleLiteralEquiv P a ha y hy hdegree
  let σ : B ≃ₐ[O] C := AlgEquiv.mapIntegralClosure (e.restrictScalars O)
  have hmodel : differentIdeal O B =
      Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) := by
    rw [quadraticArtinSchreierDifferentIdeal_eq_span,
      map_maximalIdeal_eq_span_quadraticArtinSchreierIntegralUniformizer]
  calc
    differentIdeal O C = Ideal.map σ (differentIdeal O B) :=
      (differentIdeal_map_algEquiv_eq O B C σ).symm
    _ = Ideal.map σ (Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O)) := by
      rw [hmodel]
    _ = Ideal.map (algebraMap O C) (IsLocalRing.maximalIdeal O) := by
      change Ideal.map σ.toRingHom
        (Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O)) = _
      rw [Ideal.map_map]
      congr 1
      exact σ.toAlgHom.comp_algebraMap

/-- An integral parameter gives the unit different on the actual quadratic
field, not merely on its isomorphic polynomial model. -/
theorem quadraticLiteral_different_eq_top
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (a : K) (ha : 0 ≤ P.order a)
    (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤) :
    differentIdeal P.valuationRing (integralClosure P.valuationRing L) = ⊤ := by
  let O := P.valuationRing
  let C := integralClosure O L
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  have haO : a ∈ O := by
    by_cases hzero : a = 0
    · simpa only [hzero] using O.zero_mem
    · exact (P.regularAt_iff_mem_valuationRing a).mp
        ((P.regularAt_iff_order_nonnegative hzero).mpr ha)
  let b : O := ⟨a, haO⟩
  let hirr := quadraticRegularLiteralPolynomial_irreducible P b y hy hdegree hgen
  let S := RegularQuadraticArtinSchreierField P b hirr
  let B := RegularQuadraticArtinSchreierIntegralClosure P b hirr
  let e : S ≃ₐ[K] L := quadraticRegularLiteralEquiv P b y hy hdegree hgen
  let σ : B ≃ₐ[O] C := AlgEquiv.mapIntegralClosure (e.restrictScalars O)
  calc
    differentIdeal O C = Ideal.map σ (differentIdeal O B) :=
      (differentIdeal_map_algEquiv_eq O B C σ).symm
    _ = ⊤ := by
      rw [regularQuadraticArtinSchreierDifferentIdeal_eq_top, Ideal.map_top]

omit [Algebra F256 K] in
private theorem integralClosure_ramificationIdx_eq_one_of_different_eq_top
    {O : Type*} [CommRing O] [Algebra O K] [IsFractionRing O K]
    [Algebra O L] [IsScalarTower O K L]
    [IsDedekindDomain O] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    [Module.IsTorsionFree O (integralClosure O L)]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    [H.asIdeal.LiesOver p]
    (hd : differentIdeal O (integralClosure O L) = ⊤) :
    p.ramificationIdx' H.asIdeal = 1 := by
  let C := integralClosure O L
  letI : Module.IsTorsionFree O L :=
    Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : Algebra (FractionRing O) (FractionRing C) := FractionRing.liftAlgebra _ _
  letI : Algebra.IsSeparable (FractionRing O) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv O K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    apply IsFractionRing.ringHom_ext (A := O)
    intro x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv O K).symm (FractionRing.algEquiv C L).symm
      (algebraMap O K x)
  have hnot : ¬ H.asIdeal ∣ differentIdeal O C := by
    rw [hd, Ideal.dvd_iff_le]
    intro h
    exact H.isPrime.ne_top (top_unique h)
  letI : Algebra.IsUnramifiedAt O H.asIdeal :=
    (not_dvd_differentIdeal_iff (A := O) (B := C)).mp hnot
  have hp0 : p ≠ ⊥ := by
    rw [Ideal.over_def H.asIdeal p]
    exact Ideal.under_ne_bot O H.ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p H.asIdeal hp0]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := O) (p := H.asIdeal)

omit [Algebra F256 K] in
/-- A unit different gives ramification index one at every actual upper
prime of a finite separable integral model. -/
theorem ramificationIdx_eq_one_of_unit_different
    {O : Type*} [CommRing O] [Algebra O K] [IsFractionRing O K]
    [Algebra O L] [IsScalarTower O K L]
    [IsDedekindDomain O] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDedekindDomain (integralClosure O L)]
    [IsFractionRing (integralClosure O L) L]
    [Module.IsTorsionFree O (integralClosure O L)]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure O L))
    [H.asIdeal.LiesOver p]
    (hd : differentIdeal O (integralClosure O L) = ⊤) :
    p.ramificationIdx' H.asIdeal = 1 :=
  integralClosure_ramificationIdx_eq_one_of_different_eq_top (K := K) p H hd

/-- Every upper prime of a literal quadratic Artin--Schreier extension with
a normalized simple-pole or regular parameter has weak different exponent.
The quantifier is over supplied upper primes, not a selected extension of a
place. The only generator hypotheses are its equation and field generation. -/
theorem quadraticLiteral_allPrime_weakDifferent
    [Algebra F256 L] [Algebra.IsSeparable K L]
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L))
    [H.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    multiplicity H.asIdeal
        (differentIdeal P.valuationRing (integralClosure P.valuationRing L)) =
      2 * ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' H.asIdeal - 1) := by
  let O := P.valuationRing
  let C := integralClosure O L
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  letI : Module.IsTorsionFree O L :=
    Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : Module.Finite O C := IsIntegralClosure.finite O K L C
  letI : NoZeroSMulDivisors O C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  have hm0 : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  rcases ha with hpole | hregular
  · have ha0 : a ≠ 0 := by
      intro h
      simp [h, GlobalPlace.order] at hpole
    have he0 : 0 < m.ramificationIdx' H.asIdeal :=
      Nat.pos_iff_ne_zero.mpr
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver H.asIdeal hm0)
    have he2 : m.ramificationIdx' H.asIdeal ≤ 2 := by
      calc
        m.ramificationIdx' H.asIdeal ≤ Module.finrank K L :=
          Ideal.ramificationIdx_le_finrank C K L H.asIdeal
        _ = 2 := hdegree
    have he := (P.artinSchreier_root_order_of_simplePole
      (integralClosurePlace (k := F256) H) a y
      (m.ramificationIdx' H.asIdeal) he0 he2 hy
      (integralClosurePlace_order_algebraMap P H a ha0) hpole).1
    have hd := quadraticLiteral_different_eq_map_maximalIdeal P a hpole y hy hdegree
    rw [hd]
    have hmap0 : Ideal.map (algebraMap O C) m ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hm0
    rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0 H.isPrime]
    change m.ramificationIdx' H.asIdeal = 2 * (m.ramificationIdx' H.asIdeal - 1)
    rw [he]
  · have hd := quadraticLiteral_different_eq_top P a hregular y hy hdegree hgen
    have he := integralClosure_ramificationIdx_eq_one_of_different_eq_top
      (K := K) (L := L) m H hd
    have hmult : multiplicity H.asIdeal (differentIdeal O C) = 0 := by
      rw [hd]
      apply multiplicity_eq_zero.mpr
      rw [Ideal.dvd_iff_le]
      intro h
      exact H.isPrime.ne_top (top_unique h)
    change multiplicity H.asIdeal (differentIdeal O C) =
      2 * (m.ramificationIdx' H.asIdeal - 1)
    rw [hmult, he]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
