import QEC.Coding.ExpanderCodes.LPSOriginalCuspNormalization
import QEC.Coding.ExpanderCodes.LPSOriginalReciprocalE4Equation

/-!
# Construct actual original reciprocal modular numerators

Normalize the actual j-power-cleared representative. Delta clearing gives a level-N modular numerator because the cusp germs equal E4^(3k) times the normalized cusp-regular original function. Prove the literal numerator multiplication identity in genuine germs, including denominator zeros.

Derived internal PK22 ex:Xpq closure, pinned main.tex484–486, for parent #449.
Reciprocal point coverage, global differential/sheaf comparison, good reduction,
Hecke/Frobenius/Weil and the public quantum-family theorem remain further work.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)

/-- Construct the actual j-power product with the normalized original representative. -/
def lpsOriginalReciprocalClearedRepresentative
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (k : ℕ) :
    LPSOriginalFilledMeromorphicFunctionRing N hN :=
  (⟨lpsOriginalFilledJ N, lpsOriginalFilledChartMeromorphic_j N hN⟩ :
    LPSOriginalFilledMeromorphicFunctionRing N hN)^k *
    ⟨lpsOriginalNormalizedFilledFunction N hN F,
      lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF⟩

/-- Delta clearing of the normalized product is cusp bounded through the actual E4 power identity. -/
lemma lpsOriginalReciprocalClearedRepresentative_cusp_bounded
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ) (ρ : SL(2,ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      ModularForm.discriminant τ^k *
      lpsOriginalNormalizedFilledFunction N hN
        (lpsOriginalReciprocalClearedRepresentative N hN F hF k).val
        (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  have he := lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
    N hN ρ G.val G.property
  have hmult : (fun τ : ℍ => ModularForm.discriminant τ^k *
      lpsOriginalNormalizedFilledFunction N hN G.val
        (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) =ᶠ[UpperHalfPlane.atImInfty]
      (fun τ : ℍ => (ModularForm.E₄ τ^3)^k *
        lpsOriginalNormalizedFilledFunction N hN F
          (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
    filter_upwards [he] with τ hτ
    rw [hτ]
    change ModularForm.discriminant τ^k *
      (lpsOriginalFilledJ N (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)^k *
        lpsOriginalNormalizedFilledFunction N hN F
          (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) = _
    rw [lpsOriginalFilledJ_projection,
      lpsOriginalJInvariant_SL_invariant _ ⟨ρ,rfl⟩ τ, ←mul_assoc,
      lpsOriginalDelta_j_power]
  have hd : UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => (ModularForm.E₄ τ^3)^k) := by
    have hfun : (lpsOriginalE4CubePower k : ℍ → ℂ) =
        (fun τ : ℍ => (ModularForm.E₄ τ^3)^k) :=
      funext (lpsOriginalE4CubePower_apply k)
    rw [←hfun]
    exact ModularFormClass.bdd_at_infty (lpsOriginalE4CubePower k)
  have hf := lpsOriginalNormalizedFilledFunction_cusp_bounded N hN F hF hc ρ
  exact (BoundedAtFilter.mul hd hf).congr' hmult.symm (Filter.EventuallyEq.refl _ _)

/-- Construct the genuine level-N weight12k numerator from proved interior orders and cusp bounds. -/
def lpsOriginalReciprocalNumeratorModularForm
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ)
    (hi : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt
          ((lpsOriginalReciprocalClearedRepresentative N hN F hF k).val ∘
            (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    LPSOriginalMeromorphicLevelForm N k :=
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  lpsOriginalFilledFunctionDeltaModularForm N
    (lpsOriginalNormalizedFilledFunction N hN G.val) k
    (lpsOriginalNormalizedFilledFunction_upstairs_holomorphic N hN G.val G.property hi)
    (lpsOriginalReciprocalClearedRepresentative_cusp_bounded N hN F hF hc k)

end
end QEC.Coding.TannerLiftedProduct


namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet

/-- Bundle the genuine modular discriminant with its proved holomorphy. -/
def lpsOriginalDeltaHolomorphic : R :=
  ⟨ModularForm.discriminant, ModularFormClass.holo CuspForm.discriminant⟩

/-- The actual discriminant-j identity holds in the genuine holomorphic ring. -/
lemma lpsOriginalHolomorphic_delta_j_power (k : ℕ) :
    lpsOriginalDeltaHolomorphic^k * lpsOriginalJHolomorphic^k =
      lpsOriginalE4PowerHolomorphic k := by
  apply Subtype.ext
  funext τ
  change ModularForm.discriminant τ^k * lpsOriginalJInvariant τ^k = _
  rw [lpsOriginalE4PowerHolomorphic_apply]
  exact lpsOriginalDelta_j_power k τ

/-- The constructed product retains the literal j-power times original restriction germ. -/
lemma lpsOriginalReciprocalClearedRepresentative_restriction
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (k : ℕ) :
    let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
    (lpsOriginalFilledMeromorphicRestriction N hN G.val G.property).val =
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)^k *
      (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  let J : LPSOriginalFilledMeromorphicFunctionRing N hN :=
    ⟨lpsOriginalFilledJ N, lpsOriginalFilledChartMeromorphic_j N hN⟩
  let Fnorm : LPSOriginalFilledMeromorphicFunctionRing N hN :=
    ⟨lpsOriginalNormalizedFilledFunction N hN F,
      lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF⟩
  let e := lpsOriginalFilledFunctionToRestrictedMeromorphic N hN
  have hp : e G = e J^k * e Fnorm := by
    change e (J^k * Fnorm) = _
    rw [map_mul, map_pow]
  have he := congrArg Subtype.val hp
  change (lpsOriginalFilledMeromorphicRestriction N hN G.val G.property).val =
    ((lpsOriginalFilledMeromorphicRestriction N hN J.val J.property).val)^k *
      (lpsOriginalFilledMeromorphicRestriction N hN Fnorm.val Fnorm.property).val at he
  rw [lpsOriginalFilledMeromorphicRestriction_j,
    lpsOriginalNormalizedFilledFunction_restriction] at he
  exact he

/-- The constructed modular numerator equals E4 cube power times the original function in genuine germs. -/
lemma lpsOriginalReciprocalNumerator_germ_identity
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ)
    (hi : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt
          ((lpsOriginalReciprocalClearedRepresentative N hN F hF k).val ∘
            (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    let A := lpsOriginalReciprocalNumeratorModularForm N hN F hF hc k hi
    lpsOriginalHolomorphicToMeromorphicGerm
      (lpsOriginalLevelFormHolomorphic N k A) =
      lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalE4PowerHolomorphic k) *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  let Gn := lpsOriginalNormalizedFilledFunction N hN G.val
  let hGn := lpsOriginalNormalizedFilledFunction_meromorphic N hN G.val G.property
  let A := lpsOriginalReciprocalNumeratorModularForm N hN F hF hc k hi
  have ha : lpsOriginalHolomorphicToMeromorphicGerm
      (lpsOriginalLevelFormHolomorphic N k A) =
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalDeltaHolomorphic)^k *
        (lpsOriginalFilledMeromorphicRestriction N hN Gn hGn).val := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun z => rfl)
  rw [lpsOriginalNormalizedFilledFunction_restriction N hN G.val G.property,
    lpsOriginalReciprocalClearedRepresentative_restriction] at ha
  calc
    _ = (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalDeltaHolomorphic)^k *
      ((lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)^k *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val) := ha
    _ = lpsOriginalHolomorphicToMeromorphicGerm
        (lpsOriginalDeltaHolomorphic^k * lpsOriginalJHolomorphic^k) *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by
      rw [map_mul, map_pow, map_pow, mul_assoc]
    _ = _ := by rw [lpsOriginalHolomorphic_delta_j_power]

end
end QEC.Coding.TannerLiftedProduct
