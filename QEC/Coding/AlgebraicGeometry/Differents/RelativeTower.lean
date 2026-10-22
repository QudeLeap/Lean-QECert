import QEC.Coding.AlgebraicGeometry.Differents.ExponentTower
import QEC.Coding.AlgebraicGeometry.Differents.TrivialFieldExtension

/-!
# Different transitivity using specified fraction fields

This wrapper derives separability of canonical fraction rings from the
actual fraction fields, so callers do not change their scalar actions when
applying the different tower law.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/-- The self extension contributes zero different exponent and index one. -/
theorem self_weakDifferent (R : Type*) [CommRing R] [IsDedekindDomain R]
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    multiplicity H.asIdeal (differentIdeal R R) =
      2 * (H.asIdeal.ramificationIdx' H.asIdeal - 1) := by
  letI : H.asIdeal.LiesOver H.asIdeal := ⟨by simp [Ideal.under]⟩
  exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
    R R (FractionRing R) (FractionRing R) H H (Module.finrank_self _)).2

/-- The weak different law composes using the actual specified fraction
fields; canonical-fraction separability is proved internally. -/
theorem weakDifferent_tower_of_fractionFields
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite B C] [Module.Finite A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
    [Algebra A K] [IsFractionRing A K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra.IsSeparable K L]
    (p : IsDedekindDomain.HeightOneSpectrum A)
    (P : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C)
    [P.asIdeal.LiesOver p.asIdeal] [Q.asIdeal.LiesOver P.asIdeal]
    (hAB : multiplicity P.asIdeal (differentIdeal A B) =
      2 * (p.asIdeal.ramificationIdx' P.asIdeal - 1))
    (hBC : multiplicity Q.asIdeal (differentIdeal B C) =
      2 * (P.asIdeal.ramificationIdx' Q.asIdeal - 1)) :
    multiplicity Q.asIdeal (differentIdeal A C) =
      2 * (p.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    apply IsFractionRing.ringHom_ext (A := A)
    intro x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv A K).symm (FractionRing.algEquiv C L).symm
      (algebraMap A K x)
  exact differentIdeal_multiplicity_eq_two_mul_ramificationIdx_sub_one_tower
    A B C p.asIdeal P.asIdeal Q.asIdeal p.ne_bot hAB hBC

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
