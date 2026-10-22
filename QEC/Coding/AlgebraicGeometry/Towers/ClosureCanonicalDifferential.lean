import QEC.Coding.AlgebraicGeometry.Towers.ClosureDifferentialDivisor
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisSelectedDivisor

/-!
# The actual source canonical differential d(z-1)/(z-1)

This is the logarithmic differential of the literal selected vanishing
function. Its intrinsic divisor has the coefficients used by Ngu24, and
its residue at every enumerated selected point is one.
-/

open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

local instance canonicalDifferentialModule (m : ℕ) :
    Module (SourceGaloisClosureField m) (Differential F256 (SourceGaloisClosureField m)) :=
  instModuleKaehlerDifferentialOfSMulCommClass F256 (SourceGaloisClosureField m)
    (R' := SourceGaloisClosureField m)

local instance canonicalDifferentialSMul (m : ℕ) :
    SMul (SourceGaloisClosureField m) (Differential F256 (SourceGaloisClosureField m)) :=
  (canonicalDifferentialModule m).toSMul

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem sourceClosure_selectedVanishing_eq_z_sub_one (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m =
      algebraMap (RatFunc F256) (SourceGaloisClosureField m) RatFunc.X - 1 := by
  rw [sourceGaloisClosureSelectedVanishingFunction_eq]
  congr 1
  have h := congrArg (algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m))
    (sourceClosureWBase_generator_pow_fifteen m)
  erw [map_pow, ← IsScalarTower.algebraMap_apply (RatFunc F256)
    (sourceClosureWBase m) (SourceGaloisClosureField m)] at h
  exact h

theorem sourceClosure_selectedVanishing_derivative (m : ℕ) :
    functionFieldDerivation (k := F256) (F := SourceGaloisClosureField m)
      (sourceGaloisClosureSelectedVanishingFunction m) = 1 := by
  rw [sourceClosure_selectedVanishing_eq_z_sub_one, map_sub,
    functionFieldDerivation_apply_X, Derivation.map_one_eq_zero, sub_zero]

/-- The literal logarithmic differential eta = d(z-1)/(z-1). -/
def sourceClosureCanonicalDifferential (m : ℕ) : Differential F256 (SourceGaloisClosureField m) :=
  Differential.logarithmicDifferential (sourceGaloisClosureSelectedVanishingFunction m)

theorem sourceClosureCanonicalDifferential_eq_inverse_smul_dz (m : ℕ) :
    sourceClosureCanonicalDifferential m =
      (sourceGaloisClosureSelectedVanishingFunction m : SourceGaloisClosureField m)⁻¹ •
        functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m) := by
  rw [sourceClosureCanonicalDifferential, Differential.logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    sourceClosure_selectedVanishing_derivative]
  exact congrArg (fun omega => (sourceGaloisClosureSelectedVanishingFunction m)⁻¹ • omega)
    ((canonicalDifferentialModule m).one_smul _)

theorem sourceClosureCanonicalDifferential_ne_zero (m : ℕ) :
    sourceClosureCanonicalDifferential m ≠ 0 := by
  rw [sourceClosureCanonicalDifferential_eq_inverse_smul_dz]
  exact smul_ne_zero (inv_ne_zero (sourceGaloisClosureSelectedVanishingFunction_ne_zero m))
    functionFieldDifferentialGenerator_ne_zero

/-- The canonical divisor is constructed from the actual nonzero eta. -/
def sourceClosureCanonicalDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) :=
  differentialDivisor (sourceClosureCanonicalDifferential m)
    (sourceClosureCanonicalDifferential_ne_zero m)

theorem sourceClosureCanonicalDivisor_isCanonical (m : ℕ) :
    IsCanonicalDivisor (k := F256) (F := SourceGaloisClosureField m)
      (sourceClosureCanonicalDivisor m) :=
  differentialDivisor_isCanonical _ _

/-- The paper's displayed divisor identity, for the actual intrinsic
canonical divisor and the actual reduced fibres. -/
theorem sourceClosureCanonicalDivisor_eq (m : ℕ) :
    sourceClosureCanonicalDivisor m =
      (16 * (sourceGaloisWZeroRamificationIndex m : ℤ) - 2) • sourceGaloisWZeroFibreDivisor m +
        ((sourceGaloisWInfinityRamificationIndex m : ℤ) - 2) •
          sourceGaloisWInfinityFibreDivisor m - sourceGaloisClosureSelectedDivisor m := by
  classical
  ext Q
  have hz := congrArg (fun D : Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) => D Q)
    (sourceClosure_dz_divisor m)
  have hf := congrArg (fun D : Divisor (GlobalPlace F256 (SourceGaloisClosureField m)) => D Q)
    (sourceGaloisClosureSelectedVanishingFunction_principalDivisor m)
  simp only [differentialDivisor_apply, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at hz
  simp only [GlobalPlace.principalDivisor_apply, Units.val_mk0, Finsupp.sub_apply,
    Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at hf
  have horder : differentialOrder Q (sourceClosureCanonicalDifferential m)
      (sourceClosureCanonicalDifferential_ne_zero m) =
      Q.order (sourceGaloisClosureSelectedVanishingFunction m)⁻¹ +
        differentialOrder Q (functionFieldDifferentialGenerator (k := F256)
          (F := SourceGaloisClosureField m)) functionFieldDifferentialGenerator_ne_zero := by
    simpa only [sourceClosureCanonicalDifferential_eq_inverse_smul_dz] using
      Differential.differentialOrder_smul Q _ (inv_ne_zero (sourceGaloisClosureSelectedVanishingFunction_ne_zero m))
        _ (functionFieldDifferentialGenerator_ne_zero (k := F256) (F := SourceGaloisClosureField m))
  rw [sourceClosureCanonicalDivisor, differentialDivisor_apply, horder, Q.order_inv, hz, hf]
  simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- The same actual eta, regarded in the simple-pole lattice of any place. -/
def sourceClosureCanonicalDifferentialAtPlace (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) : Differential.simplePoleDifferentialLattice Q :=
  Differential.logarithmicDifferentialAtSimplePole Q
    (sourceGaloisClosureSelectedVanishingFunction m)
    (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)

theorem sourceClosureCanonicalDifferentialAtPlace_coe (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m)) :
    (sourceClosureCanonicalDifferentialAtPlace m Q : Differential F256 (SourceGaloisClosureField m)) =
      sourceClosureCanonicalDifferential m := rfl

/-- At each actual enumerated rational point, eta has residue one. -/
theorem sourceClosureCanonicalDifferential_selected_residue (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    Differential.simplePoleResidue (sourceGaloisClosureSelectedRationalPlace m j).place
      (sourceClosureCanonicalDifferentialAtPlace m (sourceGaloisClosureSelectedRationalPlace m j).place) =
        1 := by
  rw [sourceClosureCanonicalDifferentialAtPlace,
    Differential.simplePoleResidue_logarithmicDifferential,
    sourceGaloisClosureSelectedRationalPlace_order_vanishingFunction, Int.cast_one]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
