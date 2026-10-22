import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialTrace
import QEC.Coding.AlgebraicGeometry.Residues.Rational.InvolutionResidueTransport

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Differential trace under the inverse rational coordinate

Changing the rational coordinate by `X ↦ X⁻¹` transports the field trace by
the same involution.  The induced differential trace is therefore the actual
rational differential involution of the original trace.  The proof is
symbolic: it uses trace functoriality, the inverse rule, and the proved
rank-one differential coordinate.

No local residue sum, global residue theorem, duality, genus formula, or
Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport

open scoped Polynomial RatFunc
open FunctionFieldDifferential

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance directConstantAlgebra : Algebra k F :=
  AffinePlace.constantAlgebra k F

noncomputable local instance directConstantScalarTower :
    IsScalarTower k k⟮X⟯ F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap k⟮X⟯ F (algebraMap k k⟮X⟯ c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F (Polynomial.C c))

local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F

/-- The transported rational algebra still extends the same explicit
constant algebra: the rational involution fixes every constant. -/
@[reducible]
private noncomputable def inverseConstantScalarTower :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    IsScalarTower k k⟮X⟯ F := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro c
  calc
    algebraMap k F c =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (algebraMap k k⟮X⟯ c) :=
      by
        change (@algebraMap k[X] F _ _ oldPolynomialAlgebra) (Polynomial.C c) =
          (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
            (algebraMap k k⟮X⟯ c)
        simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
          (@IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F _ _ _
            (inferInstance : Algebra k[X] k⟮X⟯) oldRationalAlgebra
            oldPolynomialAlgebra oldScalarTower (Polynomial.C c))
    _ = algebraMap k⟮X⟯ F (algebraMap k k⟮X⟯ c) := by
      change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (algebraMap k k⟮X⟯ c) =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (InverseAffinePlace.rationalInvolution k
            (algebraMap k k⟮X⟯ c))
      rw [(InverseAffinePlace.rationalInvolution k).commutes]

omit [Finite k] in
private theorem rationalInvolution_involutive (f : RatFunc k) :
    InverseAffinePlace.rationalInvolution k
      (InverseAffinePlace.rationalInvolution k f) = f := by
  let e := InverseAffinePlace.rationalInvolution k
  have hhom : e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
      RingHom.id (RatFunc k) := by
    apply IsFractionRing.ringHom_ext (A := k[X])
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa only [RingHom.comp_apply, RingHom.id_apply, map_add] using
          congrArg₂ (· + ·) hp hq
    | monomial n a =>
        have hC : e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) =
            (algebraMap k[X] (RatFunc k)) (Polynomial.C a) := by
          change e (e (algebraMap k (RatFunc k) a)) =
            algebraMap k (RatFunc k) a
          rw [e.commutes, e.commutes]
        have hX : e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) =
            (algebraMap k[X] (RatFunc k)) Polynomial.X := by
          change e (e RatFunc.X) = RatFunc.X
          rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
            InverseAffinePlace.rationalInvolution_X, inv_inv]
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [RingHom.comp_apply, RingHom.id_apply, map_mul, map_pow]
        change e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) *
            e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) ^ n =
          (algebraMap k[X] (RatFunc k)) (Polynomial.C a) *
            (algebraMap k[X] (RatFunc k)) Polynomial.X ^ n
        rw [hC, hX]
  change (e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom) f = f
  rw [hhom]
  rfl

omit [Finite k] in
/-- Field trace for the transported inverse-coordinate algebra is the
rational involution of the original field trace. -/
theorem transported_fieldTrace_eq_rationalInvolution (x : F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) k F
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Algebra.trace k⟮X⟯ F x =
      InverseAffinePlace.rationalInvolution k
        (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra x) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
    (oldPolynomialAlgebra := oldPolynomialAlgebra)
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) k F
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let e := InverseAffinePlace.rationalInvolution k
  have he : RingHom.comp (algebraMap k⟮X⟯ F) e.toRingEquiv.toRingHom =
      RingHom.comp (RingEquiv.refl F).toRingHom
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) := by
    ext f
    change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
        (e (e f)) =
      (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) f
    rw [rationalInvolution_involutive]
  have htrace := @Algebra.trace_eq_of_equiv_equiv
    k⟮X⟯ F k⟮X⟯ F _ _ _ _ oldRationalAlgebra inverseRationalAlgebra
      e.toRingEquiv (RingEquiv.refl F) he x
  calc
    Algebra.trace k⟮X⟯ F x =
        e (e.symm (Algebra.trace k⟮X⟯ F x)) :=
      (e.apply_symm_apply _).symm
    _ = e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra x) :=
      congrArg e htrace.symm

/-- The differential trace for the inverse-coordinate presentation is the
actual rational differential involution of the original trace. -/
theorem transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
    (omega : Differential k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) k F
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    functionFieldDifferentialTrace (k := k) (F := F) omega =
      InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
        (letI : Algebra k⟮X⟯ F := oldRationalAlgebra
         letI : IsScalarTower k k⟮X⟯ F := directConstantScalarTower
           (oldPolynomialAlgebra := oldPolynomialAlgebra)
           (oldRationalAlgebra := oldRationalAlgebra)
           (oldScalarTower := oldScalarTower) k F
         letI : _root_.FunctionField k F := oldFunctionField
         letI : Algebra.IsSeparable k⟮X⟯ F := oldSeparable
         functionFieldDifferentialTrace (k := k) (F := F) omega) := by
  let oldCoordinate := functionFieldDifferentialCoordinate (k := k) (F := F)
  let oldGenerator := functionFieldDifferentialGenerator (k := k) (F := F)
  let oldTrace := functionFieldDifferentialTrace (k := k) (F := F)
  let x : F := algebraMap k⟮X⟯ F RatFunc.X
  have homega : omega = oldCoordinate omega • oldGenerator := by
    exact functionFieldDifferential_eq_coordinate_smul_generator
      (k := k) (F := F) omega
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
    (oldPolynomialAlgebra := oldPolynomialAlgebra)
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) k F
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let e := InverseAffinePlace.rationalInvolution k
  let q : RatFunc k := -((RatFunc.X : RatFunc k)⁻¹) ^ 2
  have hnewX : algebraMap k⟮X⟯ F RatFunc.X = x⁻¹ := by
    exact InverseAffinePlace.transportedRationalMap_X
      (oldRationalAlgebra := oldRationalAlgebra) k F
  have hcoordinateGenerator :
      functionFieldDifferentialCoordinate (k := k) (F := F) oldGenerator =
        -x ^ 2 := by
    change functionFieldDifferentialCoordinate (k := k) (F := F)
      (differential k F x) = -x ^ 2
    rw [functionFieldDifferentialCoordinate_differential]
    change functionFieldDerivation (k := k) (F := F) x = -x ^ 2
    rw [show x = (algebraMap k⟮X⟯ F RatFunc.X)⁻¹ by
      rw [hnewX, inv_inv],
      functionFieldDerivation_apply_inverseCoordinate, hnewX, inv_inv]
  have hq : algebraMap k⟮X⟯ F q = -x ^ 2 := by
    change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) (e q) = -x ^ 2
    dsimp only [q, e, x]
    rw [map_neg, map_pow, map_inv₀,
      InverseAffinePlace.rationalInvolution_X, inv_inv, map_neg, map_pow]
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega =
        algebraMap k⟮X⟯ F q * oldCoordinate omega := by
    calc
      functionFieldDifferentialCoordinate (k := k) (F := F) omega =
          functionFieldDifferentialCoordinate (k := k) (F := F)
            (oldCoordinate omega • oldGenerator) :=
        congrArg (functionFieldDifferentialCoordinate (k := k) (F := F)) homega
      _ = oldCoordinate omega *
          functionFieldDifferentialCoordinate (k := k) (F := F) oldGenerator := by
        rw [map_smul, smul_eq_mul]
      _ = algebraMap k⟮X⟯ F q * oldCoordinate omega := by
        rw [hcoordinateGenerator, hq]
        ring
  have htraceCoordinate :
      Algebra.trace k⟮X⟯ F
          (functionFieldDifferentialCoordinate (k := k) (F := F) omega) =
        q * e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
          (oldCoordinate omega)) := by
    rw [hcoordinate, ← Algebra.smul_def, map_smul]
    change q * Algebra.trace k⟮X⟯ F (oldCoordinate omega) = _
    rw [transported_fieldTrace_eq_rationalInvolution
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable)]
  have hdInverse :
      differential k (RatFunc k) ((RatFunc.X : RatFunc k)⁻¹) =
        q • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    calc
      differential k (RatFunc k) ((RatFunc.X : RatFunc k)⁻¹) =
          functionFieldDifferentialCoordinate (k := k) (F := RatFunc k)
              (differential k (RatFunc k) ((RatFunc.X : RatFunc k)⁻¹)) •
            functionFieldDifferentialGenerator (k := k) (F := RatFunc k) :=
        functionFieldDifferential_eq_coordinate_smul_generator
          (k := k) (F := RatFunc k) _
      _ = q • functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) := by
        congr 1
        rw [functionFieldDifferentialCoordinate_differential]
        change functionFieldDerivation (k := k) (F := RatFunc k)
            ((algebraMap (RatFunc k) (RatFunc k) RatFunc.X)⁻¹) =
          -((algebraMap (RatFunc k) (RatFunc k) RatFunc.X)⁻¹) ^ 2
        exact functionFieldDerivation_apply_inverseCoordinate
          (k := k) (F := RatFunc k)
  change functionFieldDifferentialTrace (k := k) (F := F) omega =
    InverseRationalInfinityTransport.rationalDifferentialInvolution
      (k := k) (oldTrace omega)
  rw [functionFieldDifferentialTrace_apply, htraceCoordinate]
  change (q * e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
      (oldCoordinate omega))) •
      functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
    InverseRationalInfinityTransport.rationalDifferentialInvolution
      (k := k)
      ((@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
          (oldCoordinate omega)) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
  rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_smul]
  change (q * e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
      (oldCoordinate omega))) •
      functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
    e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
        (oldCoordinate omega)) •
      InverseRationalInfinityTransport.rationalDifferentialInvolution
        (k := k)
        (differential k (RatFunc k) RatFunc.X)
  rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_differential,
    InverseAffinePlace.rationalInvolution_X, hdInverse, smul_smul]
  congr 1
  ring

end QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
