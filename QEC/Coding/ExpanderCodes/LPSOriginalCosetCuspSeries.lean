import QEC.Coding.ExpanderCodes.LPSOriginalCuspPhaseResidue
import QEC.Coding.ExpanderCodes.LPSOriginalCuspSeriesReduction

/-!
# LPSOriginalCosetCuspSeries

The full, untruncated Laurent series of the actual inverse Gamma0-coset
branches live over the actual integral level-phase algebra; only the formal
parameter is inverted. Coefficient specialization to its proved residue
field gives pairwise distinct full branches when p does not divide N.
Their complex cleared numerators are precisely the Taylor expansions of
the same actual analytic branches, with the true nome pullback identity.

These proved internal bridges support the original modular-polynomial
reduction route behind pinned PK22 ex:Xpq, main.tex:484-486, and th:qLDPC,
main.tex:231-238. Modular-polynomial separability, Gauss unramifiedness,
uniform good reduction, Hecke/Frobenius/Weil and the quantum family remain
unproved. Distinct formal series alone are not a good-reduction theorem.
-/

open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
noncomputable section

attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

lemma lpsOriginalCuspJNumerator_constant (R : Type*) [CommRing R] :
    PowerSeries.constantCoeff (lpsOriginalCuspJNumerator R) = 1 := by
  rw [lpsOriginalCuspJNumerator, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff,
    lpsOriginalJZSeries_constant,map_one]

def lpsOriginalPhaseCuspNumerator
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R) : PowerSeries R :=
  PowerSeries.C (ζ^(N-1)) * PowerSeries.expand m hm
    (PowerSeries.rescale ζ (lpsOriginalCuspJNumerator R))

lemma lpsOriginalPhaseCuspNumerator_constant
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    PowerSeries.constantCoeff (lpsOriginalPhaseCuspNumerator R N m hm ζ) =
      ζ^(N-1) := by
  rw [lpsOriginalPhaseCuspNumerator,map_mul,PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_expand,← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_rescale,pow_zero,one_mul,PowerSeries.coeff_zero_eq_constantCoeff,
    lpsOriginalCuspJNumerator_constant,mul_one]

def lpsOriginalPhaseCuspSeries
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    lpsOriginalCuspSeriesRing R :=
  (IsLocalization.Away.invSelf (S := lpsOriginalCuspSeriesRing R)
    (PowerSeries.X : PowerSeries R))^m *
    algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
      (lpsOriginalPhaseCuspNumerator R N m hm ζ)

lemma lpsOriginalPhaseCuspSeries_clear
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R)
    (D : ℕ) (hD : m ≤ D) :
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^D *
      lpsOriginalPhaseCuspSeries R N m hm ζ =
      algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
        (PowerSeries.X^(D-m) * lpsOriginalPhaseCuspNumerator R N m hm ζ) := by
  rw [lpsOriginalPhaseCuspSeries, ← mul_assoc]
  have hc := lpsOriginalCuspParameter_cancelPowers (R := R) 1 D m hD
  simp only [one_mul] at hc
  rw [hc,map_mul,map_pow]

lemma lpsOriginalLevelRoot_neZero
    (R : Type*) [CommRing R] [Nontrivial R] (N : ℕ) (hN : 0 < N)
    (ζ : R) (hζ : ζ^N = 1) : ζ ≠ 0 := by
  intro h
  rw [h, zero_pow hN.ne'] at hζ
  exact zero_ne_one hζ

lemma lpsOriginalLevelRoot_inversePower
    (R : Type*) [CommRing R] (N : ℕ) (hN : 0 < N)
    (ζ : R) (hζ : ζ^N = 1) : ζ * ζ^(N-1) = 1 := by
  rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hN]
  exact hζ

lemma lpsOriginalPhaseCuspSeries_ne_of_slope_lt
    (R : Type*) [CommRing R] [IsDomain R]
    (N : ℕ) (hN : 0 < N) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ζ η : R) (hη : η^N = 1) (hmn : m < n) :
    lpsOriginalPhaseCuspSeries R N m hm ζ ≠
      lpsOriginalPhaseCuspSeries R N n hn η := by
  intro he
  have hc := congrArg (fun j : lpsOriginalCuspSeriesRing R =>
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^n * j) he
  rw [lpsOriginalPhaseCuspSeries_clear R N m hm ζ n hmn.le,
    lpsOriginalPhaseCuspSeries_clear R N n hn η n (le_refl n),
    Nat.sub_self,pow_zero,one_mul] at hc
  have hs := lpsOriginalCuspSeriesAlgebraMap_injective R hc
  have hconst := congrArg PowerSeries.constantCoeff hs
  rw [map_mul,map_pow,PowerSeries.constantCoeff_X,
    zero_pow (Nat.sub_pos_of_lt hmn).ne',zero_mul,
    lpsOriginalPhaseCuspNumerator_constant] at hconst
  exact (pow_ne_zero (N-1) (lpsOriginalLevelRoot_neZero R N hN η hη)) hconst.symm

lemma lpsOriginalPhaseCuspSeries_equalData
    (R : Type*) [CommRing R] [IsDomain R]
    (N : ℕ) (hN : 0 < N) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ζ η : R) (hζ : ζ^N = 1) (hη : η^N = 1)
    (he : lpsOriginalPhaseCuspSeries R N m hm ζ =
      lpsOriginalPhaseCuspSeries R N n hn η) : m = n ∧ ζ = η := by
  have hmn : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · exact False.elim ((lpsOriginalPhaseCuspSeries_ne_of_slope_lt
        R N hN m n hm hn ζ η hη h) he)
    · exact h
    · exact False.elim ((lpsOriginalPhaseCuspSeries_ne_of_slope_lt
        R N hN n m hn hm η ζ hζ h) he.symm)
  refine ⟨hmn, ?_⟩
  subst n
  have hc := congrArg (fun j : lpsOriginalCuspSeriesRing R =>
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^m * j) he
  rw [lpsOriginalPhaseCuspSeries_clear R N m hm ζ m (le_refl m),
    lpsOriginalPhaseCuspSeries_clear R N m hm η m (le_refl m)] at hc
  simp only [Nat.sub_self,pow_zero,one_mul] at hc
  have hs := lpsOriginalCuspSeriesAlgebraMap_injective R hc
  have hi := congrArg PowerSeries.constantCoeff hs
  rw [lpsOriginalPhaseCuspNumerator_constant,
    lpsOriginalPhaseCuspNumerator_constant] at hi
  apply mul_right_cancel₀ (pow_ne_zero (N-1)
    (lpsOriginalLevelRoot_neZero R N hN η hη))
  calc
    ζ * η^(N-1) = ζ * ζ^(N-1) := by rw [hi]
    _ = 1 := lpsOriginalLevelRoot_inversePower R N hN ζ hζ
    _ = η * η^(N-1) := (lpsOriginalLevelRoot_inversePower R N hN η hη).symm

lemma lpsOriginalPhaseCuspNumerator_map
    (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S)
    (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    PowerSeries.map f (lpsOriginalPhaseCuspNumerator R N m hm ζ) =
      lpsOriginalPhaseCuspNumerator S N m hm (f ζ) := by
  rw [lpsOriginalPhaseCuspNumerator,map_mul,PowerSeries.map_C,f.map_pow,
    PowerSeries.map_expand,← PowerSeries.rescale_map,
    lpsOriginalCuspCoefficientMap_integerNumerator]
  rfl

lemma lpsOriginalPhaseCuspSeries_map
    (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S)
    (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    lpsOriginalCuspCoefficientMap f (lpsOriginalPhaseCuspSeries R N m hm ζ) =
      lpsOriginalPhaseCuspSeries S N m hm (f ζ) := by
  rw [lpsOriginalPhaseCuspSeries,map_mul,map_pow,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    lpsOriginalPhaseCuspNumerator_map]
  rfl

lemma lpsOriginalCosetCuspData_slope_pos
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    0 < (lpsOriginalCosetCuspData N hN x).1 :=
  (lpsOriginalCosetCuspWitness N hN x).1.property

def lpsOriginalCosetIntegralCuspSeries
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspSeriesRing (lpsOriginalLevelPhaseRing N) :=
  lpsOriginalPhaseCuspSeries (lpsOriginalLevelPhaseRing N) N
    (lpsOriginalCosetCuspData N hN x).1
    (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
    (lpsOriginalCosetPhaseElement N hN x)

def lpsOriginalCosetResidueCuspSeries
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp) :=
  lpsOriginalPhaseCuspSeries (LPSOriginalLevelPhaseResidue N hN p hp) N
    (lpsOriginalCosetCuspData N hN x).1
    (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
    (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
      (lpsOriginalCosetPhaseElement N hN x))

lemma lpsOriginalCosetCuspSeries_reduction
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspCoefficientMap
      (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp))
      (lpsOriginalCosetIntegralCuspSeries N hN x) =
        lpsOriginalCosetResidueCuspSeries N hN p hp x :=
  lpsOriginalPhaseCuspSeries_map _ _ _ N _ _ _

lemma lpsOriginalCosetResiduePhase_pow
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
      (lpsOriginalCosetPhaseElement N hN x))^N = 1 := by
  rw [← map_pow,lpsOriginalCosetPhaseElement_pow,map_one]

lemma lpsOriginalCosetResidueCuspSeries_injective
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalCosetResidueCuspSeries N hN p hp) := by
  intro x y hxy
  have hd := lpsOriginalPhaseCuspSeries_equalData
    (LPSOriginalLevelPhaseResidue N hN p hp) N hN
    (lpsOriginalCosetCuspData N hN x).1
    (lpsOriginalCosetCuspData N hN y).1
    (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
    (lpsOriginalCosetCuspData_slope_pos N hN y).ne'
    _ _ (lpsOriginalCosetResiduePhase_pow N hN p hp x)
    (lpsOriginalCosetResiduePhase_pow N hN p hp y) hxy
  apply lpsOriginalCosetCuspResidueData_injective N hN p hp hpN
  exact Prod.ext hd.1 hd.2


lemma lpsOriginalLevelRoot_inversePower_eq (R : Type*) [Field R]
    (N : ℕ) (hN : 0 < N) (ζ : R) (hζ : ζ^N = 1) :
    ζ^(N-1) = ζ⁻¹ := by
  apply (mul_eq_one_iff_eq_inv₀
    (lpsOriginalLevelRoot_neZero R N hN ζ hζ)).mp
  rw [mul_comm]
  exact lpsOriginalLevelRoot_inversePower R N hN ζ hζ

lemma lpsOriginalPhaseCuspNumerator_taylor
    (N : ℕ) (hN : 0 < N) (m : ℕ) (hm : m ≠ 0) (r : ℚ)
    (hr : ∃ z : ℤ, (N : ℚ) * r = z) :
    lpsOriginalPhaseCuspNumerator ℂ N m hm
      (Function.Periodic.qParam 1 (r : ℂ)) =
        lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp m m r) := by
  have hf : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r : ℂ)*q)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq (by fun_prop) (by simp)
  rw [lpsOriginalClearedAffineCusp_taylor m m hm r]
  simp only [Nat.sub_self,pow_zero,one_mul]
  rw [lpsOriginalTaylorSeries_comp_pow hf m hm,
    lpsOriginalTaylorSeries_comp_const_mul lpsOriginalJQCoefficient_analytic_zero,
    ← lpsOriginalJZSeries_mapC]
  rw [lpsOriginalPhaseCuspNumerator,
    lpsOriginalLevelRoot_inversePower_eq ℂ N hN _
      (lpsOriginalLevelNomePhase_pow N r hr)]
  rfl

lemma lpsOriginalPhaseCuspNumerator_shifted_taylor
    (N : ℕ) (hN : 0 < N) (B m : ℕ) (hm : m ≠ 0) (r : ℚ)
    (hr : ∃ z : ℤ, (N : ℚ) * r = z) :
    PowerSeries.X^(B-m) * lpsOriginalPhaseCuspNumerator ℂ N m hm
      (Function.Periodic.qParam 1 (r : ℂ)) =
        lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B m r) := by
  rw [lpsOriginalPhaseCuspNumerator_taylor N hN m hm r hr,
    lpsOriginalClearedAffineCusp_taylor m m hm r,
    lpsOriginalClearedAffineCusp_taylor B m hm r]
  simp only [Nat.sub_self,pow_zero,one_mul]
  ring

lemma lpsOriginalCosetCuspNumerator_taylor
    (N : ℕ) (hN : 0 < N) (B : ℕ) (x : LPSOriginalCuspIndex N) :
    PowerSeries.map (lpsOriginalLevelPhaseRing N).val
      (PowerSeries.X^(B-(lpsOriginalCosetCuspData N hN x).1) *
        lpsOriginalPhaseCuspNumerator (lpsOriginalLevelPhaseRing N) N
          (lpsOriginalCosetCuspData N hN x).1
          (lpsOriginalCosetCuspData_slope_pos N hN x).ne'
          (lpsOriginalCosetPhaseElement N hN x)) =
      lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B
        (lpsOriginalCosetCuspWitness N hN x).1.val
        (lpsOriginalCosetCuspWitness N hN x).2.val) := by
  rw [map_mul,map_pow,PowerSeries.map_X,
    lpsOriginalPhaseCuspNumerator_map]
  exact lpsOriginalPhaseCuspNumerator_shifted_taylor N hN B _ _ _
    (lpsOriginalCosetCuspWitness N hN x).2.property.2.1

lemma lpsOriginalCosetClearedCusp_pullback
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) (σ : ℍ) :
    lpsOriginalClearedAffineCusp (N^2)
      (lpsOriginalCosetCuspWitness N hN x).1.val
      (lpsOriginalCosetCuspWitness N hN x).2.val
      (Function.Periodic.qParam 1 (σ : ℂ)) =
      Function.Periodic.qParam 1 (σ : ℂ)^(N^2) *
        lpsOriginalJDilated N hN
          (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • σ)) := by
  let w := lpsOriginalCosetCuspWitness N hN x
  rw [lpsOriginalClearedAffineCusp_pullback (N^2) w.1.val w.1.property
    w.2.property.1 w.2.val σ, ← w.2.property.2.2 σ]

end
end QEC.Coding.TannerLiftedProduct
