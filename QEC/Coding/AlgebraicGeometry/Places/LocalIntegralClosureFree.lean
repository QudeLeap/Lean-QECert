import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID

/-!
# Integral closures over a local Dedekind base

In the localized Garcia--Stichtenoth different calculation, an intermediate
integral closure is Dedekind but need not itself be local.  Its maximal ideals
all lie over the unique maximal ideal of the local base, so there are only
finitely many of them.  The resulting principal-ideal structure supplies the
free module required by trace-dual localization.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- A Dedekind integral extension of a local domain is a principal ideal
ring when it is torsion-free over the base. -/
theorem isPrincipalIdealRing_of_isLocalRing_of_isIntegral
    (A B : Type*)
    [CommRing A] [CommRing B]
    [IsDomain A] [IsLocalRing A]
    [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] :
    IsPrincipalIdealRing B := by
  apply IsPrincipalIdealRing.of_finite_maximals
  refine
    (IsDedekindDomain.primesOver_finite
      (IsLocalRing.maximalIdeal A) B).subset ?_
  intro I hI
  letI : I.IsMaximal := hI
  have hunder : (I.under A).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I
  have hover : IsLocalRing.maximalIdeal A = I.under A :=
    (IsLocalRing.eq_maximalIdeal hunder).symm
  exact ⟨hI.isPrime, ⟨hover⟩⟩

/-- An integral closure over a Dedekind extension of a local domain is free
over that intermediate Dedekind ring. -/
theorem integralClosure_moduleFree_over_integralLocalBase
    (A B K L C : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [CommRing C]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra C L] [IsIntegralClosure C B L]
    [Algebra B C] [IsScalarTower B C L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L] :
    Module.Free B C := by
  letI : IsPrincipalIdealRing B :=
    isPrincipalIdealRing_of_isLocalRing_of_isIntegral A B
  exact IsIntegralClosure.module_free B K L C

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
