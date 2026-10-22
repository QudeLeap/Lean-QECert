import QEC.Coding.AlgebraicGeometry.Towers.ClosureUnramified
import QEC.Coding.AlgebraicGeometry.Towers.WBaseDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialPlaceTransport

/-!
# No dz divisor away from the actual w zero and pole

At unit w the already proved source regular chain has index one. Its lower
rational w-place also has unit w, hence dz has order zero at the original
upper place. The integral model is the actual centre of that place.
-/

open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree

variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]

theorem sourceClosureW_integralModel_dz_order_of_generator_order_zero
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)))
    (hw : (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q).order
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 0) :
    differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  let R := heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q
  have hwval : R.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1 := by
    have hlog : WithZero.log
        (R.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m)) = 0 := by
      change -WithZero.log
        (R.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m)) = 0 at hw
      omega
    have hn := R.valuation.ne_zero_iff.mpr (sourceGaloisWClosureGenerator_ne_zero m)
    rw [← WithZero.exp_log hn, hlog]
    simp
  have he := (sourceClosureW_integralModel_regular m A Q hwval).1
  letI : Q.asIdeal.LiesOver (Q.under A).asIdeal := ⟨rfl⟩
  have hs := heightOnePlace_order_algebraMap (k := F256)
    (K := sourceClosureWBase m) (L := SourceGaloisClosureField m)
    (Q.under A) Q (sourceGaloisWClosureGenerator m) (sourceClosureWBase_generator_ne_zero m)
  rw [he, Nat.cast_one, one_mul] at hs
  have hlow : (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A)).order
      (sourceGaloisWClosureGenerator m) = 0 := hs.symm.trans hw
  have hb := sourceClosureWBase_dz_order_of_generator_order_zero m _ hlow
  rw [sourceClosureW_integralModel_differentialGeneratorOrder m A Q, hb, he]
  norm_num

/-- The actual source normal closure has dz-order zero at every supplied
global place with unit w; the model centre does not change that place. -/
theorem sourceClosure_dz_order_of_generator_order_zero
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.order (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 0) :
    differentialOrder Q
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  let W := sourceClosureWBase m
  let B := AmbientPlaceModels.baseRing W Q
  let H := AmbientPlaceModels.prime W Q
  have ho := AmbientPlaceModels.prime_order W Q
  have hg := differentialGenerator_order_eq_of_order_eq
    (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) H) Q ho
  rw [← hg]
  apply sourceClosureW_integralModel_dz_order_of_generator_order_zero m B H
  change (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) H).order _ = 0
  rw [ho, hw]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
