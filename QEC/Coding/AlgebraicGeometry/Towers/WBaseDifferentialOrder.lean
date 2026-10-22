import QEC.Coding.AlgebraicGeometry.Towers.ClosureDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Differentials.RationalDifferentialTransport
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWClosurePlaces

/-!
# The literal dz on the rational intermediate w-field

The source equation z = w^15, in characteristic two, gives dz = w^14 dw.
The existing rational w-equivalence computes dw at every place, while the
function-field differential keeps its original z-presentation throughout.
-/

open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 5000] Algebra.toSMul Algebra.toModule
attribute [local instance] wConstantBaseTower

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance wBaseField (m : ℕ) : _root_.Field (sourceClosureWBase m) :=
  (sourceClosureWBase m).toField

local instance wBaseOriginalBaseAlgebra (m : ℕ) :
    Algebra GaloisBaseField (sourceClosureWBase m) := sourceGaloisWClosureFieldAlgebra m

local instance wBaseOriginalRationalAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (sourceClosureWBase m) := sourceClosureWBase_zAlgebra m

local instance wBaseOriginalConstantAlgebra (m : ℕ) :
    Algebra F256 (sourceClosureWBase m) := (sourceClosureWBase m).algebra'

local instance wBaseCharacteristic (m : ℕ) : CharP (sourceClosureWBase m) 2 := by
  letI : CharP F256 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  exact charP_of_injective_algebraMap (algebraMap F256 (sourceClosureWBase m)).injective 2

local instance wBaseConstantTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (sourceClosureWBase m) :=
  @IsScalarTower.of_algebraMap_eq' F256 GaloisBaseField (sourceClosureWBase m)
    _ _ _ _ (sourceGaloisWClosureFieldAlgebra m) (sourceClosureWBase m).algebra' (by
      apply RingHom.ext
      intro c
      apply Subtype.ext
      exact IsScalarTower.algebraMap_apply F256 GaloisBaseField (SourceGaloisClosureField m) c)

/-- The source's actual rational w-equivalence, on the common closure subfield. -/
def sourceClosureWBase_wEquiv (m : ℕ) : RatFunc F256 ≃ₐ[F256] sourceClosureWBase m :=
  sourceGaloisWFieldEquivRatFunc.trans
    ((sourceGaloisWFieldEquivClosureField m).restrictScalars F256)

theorem sourceClosureWBase_wEquiv_X (m : ℕ) :
    sourceClosureWBase_wEquiv m RatFunc.X = sourceGaloisWClosureGenerator m := by
  change (sourceGaloisWFieldEquivClosureField m)
    (sourceGaloisWFieldEquivRatFunc RatFunc.X) = _
  rw [sourceGaloisWFieldEquivRatFunc_X]
  apply Subtype.ext
  exact sourceGaloisWFieldEquivClosureField_generator m

theorem sourceClosureWBase_generator_ne_zero (m : ℕ) :
    (sourceGaloisWClosureGenerator m : sourceClosureWBase m) ≠ 0 := by
  rw [← sourceClosureWBase_wEquiv_X]
  exact (map_ne_zero (sourceClosureWBase_wEquiv m)).mpr RatFunc.X_ne_zero

theorem sourceClosureWBase_generator_pow_fifteen (m : ℕ) :
    (sourceGaloisWClosureGenerator m : sourceClosureWBase m) ^ 15 =
      algebraMap (RatFunc F256) (sourceClosureWBase m) RatFunc.X := by
  apply Subtype.ext
  change ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
    SourceGaloisClosureField m) ^ 15 =
      algebraMap GaloisBaseField (SourceGaloisClosureField m)
        (galoisBaseFieldEquivRatFunc RatFunc.X)
  have hz : galoisBaseFieldEquivRatFunc RatFunc.X = AdjoinSimple.gen F256 galoisBaseZ := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X galoisBaseZ galoisBaseZ_transcendental
  rw [hz]
  exact sourceGaloisWClosureGenerator_pow_fifteen m

/-- Differentiating the literal source relation computes dw/dz. -/
theorem sourceClosureWBase_generator_derivative (m : ℕ) :
    functionFieldDerivation (k := F256) (F := sourceClosureWBase m)
      (sourceGaloisWClosureGenerator m) =
        (sourceGaloisWClosureGenerator m : sourceClosureWBase m)⁻¹ ^ 14 := by
  let w : sourceClosureWBase m := sourceGaloisWClosureGenerator m
  have hw : w ≠ 0 := sourceClosureWBase_generator_ne_zero m
  have h := congrArg (functionFieldDerivation (k := F256) (F := sourceClosureWBase m))
    (sourceClosureWBase_generator_pow_fifteen m)
  rw [functionFieldDerivation_apply_X] at h
  change functionFieldDerivation (k := F256) (F := sourceClosureWBase m) (w ^ 15) = 1 at h
  erw [(functionFieldDerivation (k := F256) (F := sourceClosureWBase m)).leibniz_pow w 15] at h
  change 15 • (w ^ 14 * functionFieldDerivation (k := F256) w) = 1 at h
  have hfifteen : ((15 : ℕ) : sourceClosureWBase m) = 1 := by
    have htwo : (2 : sourceClosureWBase m) = 0 := CharTwo.two_eq_zero
    linear_combination 7 * htwo
  erw [nsmul_eq_mul, hfifteen, one_mul] at h
  change functionFieldDerivation (k := F256) w = w⁻¹ ^ 14
  apply (mul_left_cancel₀ (pow_ne_zero 14 hw))
  rw [h]
  erw [← mul_pow, mul_inv_cancel₀ hw, one_pow]

theorem sourceClosureWBase_generator_derivative_order (m : ℕ)
    (P : GlobalPlace F256 (sourceClosureWBase m)) :
    P.order (functionFieldDerivation (k := F256) (F := sourceClosureWBase m)
      (sourceGaloisWClosureGenerator m)) =
      -14 * P.order (sourceGaloisWClosureGenerator m) := by
  rw [sourceClosureWBase_generator_derivative]
  unfold GlobalPlace.order
  erw [P.valuation.map_pow, map_inv₀, WithZero.log_pow, WithZero.log_inv]
  simp only [nsmul_eq_mul]
  ring

theorem sourceClosureWBase_dz_order_zero_fibre (m : ℕ)
    (P : GlobalPlace F256 (sourceClosureWBase m))
    (hw : P.order (sourceGaloisWClosureGenerator m) = 1) :
    differentialOrder P (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
      functionFieldDifferentialGenerator_ne_zero = 14 := by
  obtain ⟨_, h⟩ := differentialGenerator_order_of_order_one_or_neg_one P
    (sourceGaloisWClosureGenerator m) (sourceClosureWBase_generator_ne_zero m) (.inl hw)
  rw [h, sourceClosureWBase_generator_derivative_order, hw]
  norm_num

theorem sourceClosureWBase_dz_order_infinity_fibre (m : ℕ)
    (P : GlobalPlace F256 (sourceClosureWBase m))
    (hw : P.order (sourceGaloisWClosureGenerator m) = -1) :
    differentialOrder P (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
      functionFieldDifferentialGenerator_ne_zero = -16 := by
  obtain ⟨_, h⟩ := differentialGenerator_order_of_order_one_or_neg_one P
    (sourceGaloisWClosureGenerator m) (sourceClosureWBase_generator_ne_zero m) (.inr hw)
  rw [h, sourceClosureWBase_generator_derivative_order, hw]
  norm_num

/-- At every other place of the actual rational w-field, dz has order zero. -/
theorem sourceClosureWBase_dz_order_of_generator_order_zero (m : ℕ)
    (P : GlobalPlace F256 (sourceClosureWBase m))
    (hw : P.order (sourceGaloisWClosureGenerator m) = 0) :
    differentialOrder P (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  let e := sourceClosureWBase_wEquiv m
  let R := GlobalPlace.comapAlgEquiv e P
  obtain ⟨_, h⟩ := differentialGenerator_order_rationalEquiv e P R (fun _ => rfl)
  have hX : R.order RatFunc.X = 0 := by
    change P.order (sourceClosureWBase_wEquiv m RatFunc.X) = 0
    rw [sourceClosureWBase_wEquiv_X, hw]
  have hr := rational_differentialGenerator_order_of_order_X_zero R hX
  change _ = _ - P.order (functionFieldDerivation (k := F256)
    (sourceClosureWBase_wEquiv m RatFunc.X)) at h
  rw [hr, sourceClosureWBase_wEquiv_X, sourceClosureWBase_generator_derivative_order, hw] at h
  simpa using h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
