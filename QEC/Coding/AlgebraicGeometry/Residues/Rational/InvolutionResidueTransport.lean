import QEC.Coding.AlgebraicGeometry.Residues.Inverse.RationalInfinityTransport
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueCoordinate
import QEC.Coding.AlgebraicGeometry.Residues.Local.LogarithmicResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Differential residues under rational-coordinate inversion

The rational involution `X ↦ X⁻¹` carries the normalized infinity valuation
to the normalized `(X)`-adic valuation.  This module constructs its actual
map on Kähler differentials and on the two valuation and residue fields, then
proves invariance of the traced normalized simple-pole residue.

This is a rational-base transport theorem.  It does not yet apply the direct
finite-extension trace theorem to the inverse fibre, assert a global residue
sum, or prove duality, genus, canonical degree, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport

open scoped Polynomial RatFunc WithZero
open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

private structure RationalInvolutionTarget (k : Type*) [Field k] where
  down : RatFunc k

private def rationalInvolutionTargetEquiv :
    RationalInvolutionTarget k ≃ RatFunc k where
  toFun := RationalInvolutionTarget.down
  invFun f := ⟨f⟩
  left_inv f := by cases f; rfl
  right_inv _ := rfl

private noncomputable instance rationalInvolutionTargetField :
    Field (RationalInvolutionTarget k) :=
  (rationalInvolutionTargetEquiv (k := k)).field

private noncomputable def rationalInvolutionTargetRingEquiv :
    RationalInvolutionTarget k ≃+* RatFunc k :=
  (rationalInvolutionTargetEquiv (k := k)).ringEquiv

private noncomputable instance rationalInvolutionTargetConstantAlgebra :
    Algebra k (RationalInvolutionTarget k) :=
  ((rationalInvolutionTargetRingEquiv (k := k)).symm.toRingHom.comp
    (algebraMap k (RatFunc k))).toAlgebra

private noncomputable def rationalInvolutionTargetAlgEquiv :
    RationalInvolutionTarget k ≃ₐ[k] RatFunc k where
  __ := rationalInvolutionTargetRingEquiv (k := k)
  commutes' _ := rfl

private noncomputable instance rationalInvolutionToTargetAlgebra :
    Algebra (RatFunc k) (RationalInvolutionTarget k) :=
  ((InverseAffinePlace.rationalInvolution k).trans
    (rationalInvolutionTargetAlgEquiv (k := k)).symm).toRingHom.toAlgebra

private noncomputable instance rationalInvolutionToTargetTower :
    IsScalarTower k (RatFunc k) (RationalInvolutionTarget k) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    (((InverseAffinePlace.rationalInvolution k).trans
      (rationalInvolutionTargetAlgEquiv (k := k)).symm).commutes c).symm

private noncomputable instance rationalInvolutionFromTargetAlgebra :
    Algebra (RationalInvolutionTarget k) (RatFunc k) :=
  (rationalInvolutionTargetAlgEquiv (k := k)).toRingHom.toAlgebra

private noncomputable instance rationalInvolutionFromTargetTower :
    IsScalarTower k (RationalInvolutionTarget k) (RatFunc k) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((rationalInvolutionTargetAlgEquiv (k := k)).commutes c).symm

private noncomputable def rationalDifferentialToTarget :
    Differential k (RatFunc k) →ₗ[RatFunc k]
      Differential k (RationalInvolutionTarget k) :=
  KaehlerDifferential.map k k (RatFunc k) (RationalInvolutionTarget k)

private noncomputable def rationalDifferentialFromTarget :
    Differential k (RationalInvolutionTarget k) →ₗ[RationalInvolutionTarget k]
      Differential k (RatFunc k) :=
  KaehlerDifferential.map k k (RationalInvolutionTarget k) (RatFunc k)

/-- The map on rational Kähler differentials induced by `X ↦ X⁻¹`. -/
noncomputable def rationalDifferentialInvolution
    (omega : Differential k (RatFunc k)) : Differential k (RatFunc k) :=
  rationalDifferentialFromTarget (k := k)
    (rationalDifferentialToTarget (k := k) omega)

omit [Finite k] in
/-- Coordinate inversion sends an exact differential to the differential of
the inverted rational function. -/
theorem rationalDifferentialInvolution_differential (f : RatFunc k) :
    rationalDifferentialInvolution (k := k) (differential k (RatFunc k) f) =
      differential k (RatFunc k) (InverseAffinePlace.rationalInvolution k f) := by
  change rationalDifferentialFromTarget (k := k)
      (rationalDifferentialToTarget (k := k)
        (KaehlerDifferential.D k (RatFunc k) f)) =
    KaehlerDifferential.D k (RatFunc k)
      (InverseAffinePlace.rationalInvolution k f)
  rw [show rationalDifferentialToTarget (k := k)
        (KaehlerDifferential.D k (RatFunc k) f) =
      KaehlerDifferential.D k (RationalInvolutionTarget k)
        (algebraMap (RatFunc k) (RationalInvolutionTarget k) f) by
    exact KaehlerDifferential.map_D k k (RatFunc k)
      (RationalInvolutionTarget k) f]
  rw [show rationalDifferentialFromTarget (k := k)
        (KaehlerDifferential.D k (RationalInvolutionTarget k)
          (algebraMap (RatFunc k) (RationalInvolutionTarget k) f)) =
      KaehlerDifferential.D k (RatFunc k)
        (algebraMap (RationalInvolutionTarget k) (RatFunc k)
          (algebraMap (RatFunc k) (RationalInvolutionTarget k) f)) by
    exact KaehlerDifferential.map_D k k (RationalInvolutionTarget k)
      (RatFunc k) (algebraMap (RatFunc k) (RationalInvolutionTarget k) f)]
  rfl

omit [Finite k] in
/-- The differential involution is semilinear for the rational involution. -/
theorem rationalDifferentialInvolution_smul (f : RatFunc k)
    (omega : Differential k (RatFunc k)) :
    rationalDifferentialInvolution (k := k) (f • omega) =
      InverseAffinePlace.rationalInvolution k f •
        rationalDifferentialInvolution (k := k) omega := by
  change rationalDifferentialFromTarget (k := k)
      (rationalDifferentialToTarget (k := k) (f • omega)) =
    InverseAffinePlace.rationalInvolution k f •
      rationalDifferentialFromTarget (k := k)
        (rationalDifferentialToTarget (k := k) omega)
  rw [map_smul]
  change rationalDifferentialFromTarget (k := k)
      (algebraMap (RatFunc k) (RationalInvolutionTarget k) f •
        rationalDifferentialToTarget (k := k) omega) = _
  rw [map_smul]
  rfl

omit [Finite k] in
private theorem rationalDifferentialInvolution_logarithmicDifferential
    (f : RatFunc k) :
    rationalDifferentialInvolution (k := k)
        (Differential.logarithmicDifferential (k := k) (F := RatFunc k) f) =
      Differential.logarithmicDifferential (k := k) (F := RatFunc k)
        (InverseAffinePlace.rationalInvolution k f) := by
  rw [Differential.logarithmicDifferential,
    rationalDifferentialInvolution_smul,
    rationalDifferentialInvolution_differential, map_inv₀]
  rfl

/-- The `(X)`-adic valuation after coordinate inversion is the original
rational-infinity valuation, including at zero. -/
theorem xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation
    (f : RatFunc k) :
    (xAdicPlace k).valuation (InverseAffinePlace.rationalInvolution k f) =
      (GlobalPlace.rationalInfinity k).valuation f := by
  by_cases hf : f = 0
  · subst f
    simp
  have hef : InverseAffinePlace.rationalInvolution k f ≠ 0 :=
    (map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hf
  have horder := xAdic_order_rationalInvolution_eq_rationalInfinity_order k f
  have hlog :
      WithZero.log ((xAdicPlace k).valuation
          (InverseAffinePlace.rationalInvolution k f)) =
        WithZero.log ((GlobalPlace.rationalInfinity k).valuation f) := by
    unfold GlobalPlace.order at horder
    omega
  calc
    (xAdicPlace k).valuation (InverseAffinePlace.rationalInvolution k f) =
        WithZero.exp (WithZero.log ((xAdicPlace k).valuation
          (InverseAffinePlace.rationalInvolution k f))) :=
      (WithZero.exp_log ((xAdicPlace k).valuation.ne_zero_iff.mpr hef)).symm
    _ = WithZero.exp
        (WithZero.log ((GlobalPlace.rationalInfinity k).valuation f)) := by
      rw [hlog]
    _ = (GlobalPlace.rationalInfinity k).valuation f :=
      WithZero.exp_log
        ((GlobalPlace.rationalInfinity k).valuation.ne_zero_iff.mpr hf)

/-- Coordinate inversion restricts to an equivalence from the valuation ring
at rational infinity to the `(X)`-adic valuation ring. -/
noncomputable def rationalInfinityValuationRingEquivXAdic :
    (GlobalPlace.rationalInfinity k).valuationRing ≃+* (xAdicPlace k).valuationRing where
  toFun z := ⟨InverseAffinePlace.rationalInvolution k (z : RatFunc k), by
    rw [GlobalPlace.mem_valuationRing_iff,
      xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation]
    exact z.property⟩
  invFun z := ⟨(InverseAffinePlace.rationalInvolution k).symm (z : RatFunc k), by
    rw [GlobalPlace.mem_valuationRing_iff]
    have h := xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation
      (k := k) ((InverseAffinePlace.rationalInvolution k).symm (z : RatFunc k))
    rw [(InverseAffinePlace.rationalInvolution k).apply_symm_apply] at h
    rw [← h]
    exact z.property⟩
  left_inv z := by
    apply Subtype.ext
    exact (InverseAffinePlace.rationalInvolution k).symm_apply_apply (z : RatFunc k)
  right_inv z := by
    apply Subtype.ext
    exact (InverseAffinePlace.rationalInvolution k).apply_symm_apply (z : RatFunc k)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul _ _ _
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _

private instance rationalInfinityValuationRingEquivXAdic_isLocalHom :
    IsLocalHom
      (rationalInfinityValuationRingEquivXAdic (k := k)).toRingHom :=
  ⟨fun x hx => by
    simpa using hx.map
      (rationalInfinityValuationRingEquivXAdic (k := k)).symm.toRingHom⟩

/-- The induced equivalence of the two actual residue fields. -/
noncomputable def rationalInfinityResidueEquivXAdic :
    (GlobalPlace.rationalInfinity k).residueField ≃+* (xAdicPlace k).residueField :=
  IsLocalRing.ResidueField.mapEquiv
    (rationalInfinityValuationRingEquivXAdic (k := k))

@[simp]
private theorem rationalInfinityResidueEquivXAdic_residue
    (z : (GlobalPlace.rationalInfinity k).valuationRing) :
    rationalInfinityResidueEquivXAdic (k := k)
        ((GlobalPlace.rationalInfinity k).residue z) =
      (xAdicPlace k).residue
        (rationalInfinityValuationRingEquivXAdic (k := k) z) := by
  unfold rationalInfinityResidueEquivXAdic
  exact IsLocalRing.ResidueField.map_residue
    (rationalInfinityValuationRingEquivXAdic (k := k)).toRingHom z

private theorem rationalInfinityResidueEquivXAdic_constants (c : k) :
    rationalInfinityResidueEquivXAdic (k := k)
        (GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c) =
      GlobalPlace.constantsToResidue (xAdicPlace k) c := by
  rw [show GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c =
      (GlobalPlace.rationalInfinity k).residue
        (GlobalPlace.constantsToValuationRing
          (GlobalPlace.rationalInfinity k) c) from rfl,
    rationalInfinityResidueEquivXAdic_residue]
  apply congrArg (GlobalPlace.residue (xAdicPlace k))
  apply Subtype.ext
  change InverseAffinePlace.rationalInvolution k
      (algebraMap k (RatFunc k) c) = algebraMap k (RatFunc k) c
  exact (InverseAffinePlace.rationalInvolution k).commutes c

private theorem trace_rationalInfinityResidueEquivXAdic
    (z : (GlobalPlace.rationalInfinity k).residueField) :
    letI : Algebra k (GlobalPlace.rationalInfinity k).residueField :=
      GlobalPlace.residueAlgebra (GlobalPlace.rationalInfinity k)
    letI : Algebra k (xAdicPlace k).residueField :=
      GlobalPlace.residueAlgebra (xAdicPlace k)
    Algebra.trace k (xAdicPlace k).residueField
        (rationalInfinityResidueEquivXAdic (k := k) z) =
      Algebra.trace k (GlobalPlace.rationalInfinity k).residueField z := by
  letI : Algebra k (GlobalPlace.rationalInfinity k).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalInfinity k)
  letI : Algebra k (xAdicPlace k).residueField :=
    GlobalPlace.residueAlgebra (xAdicPlace k)
  let e := rationalInfinityResidueEquivXAdic (k := k)
  have he : RingHom.comp (algebraMap k (xAdicPlace k).residueField)
      (RingEquiv.refl k) =
      RingHom.comp e.toRingHom
        (algebraMap k (GlobalPlace.rationalInfinity k).residueField) := by
    ext c
    change GlobalPlace.constantsToResidue (xAdicPlace k) c =
      e (GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c)
    exact (rationalInfinityResidueEquivXAdic_constants (k := k) c).symm
  exact (Algebra.trace_eq_of_equiv_equiv (RingEquiv.refl k) e he z).symm

/-- Traced normalized simple-pole residue is invariant under rational
coordinate inversion from infinity to the `(X)`-adic place. -/
theorem simplePoleTraceResidue_rationalDifferentialInvolution
    (omega : Differential k (RatFunc k))
    (homega : omega ∈ Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalInfinity k)) :
    ∃ htransport : rationalDifferentialInvolution (k := k) omega ∈
        Differential.simplePoleDifferentialLattice (xAdicPlace k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (xAdicPlace k) (rationalDifferentialInvolution (k := k) omega)
          htransport =
        Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k) omega homega := by
  let P := GlobalPlace.rationalInfinity k
  let Q := xAdicPlace k
  let e := InverseAffinePlace.rationalInvolution k
  let eO := rationalInfinityValuationRingEquivXAdic (k := k)
  let eκ := rationalInfinityResidueEquivXAdic (k := k)
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let r : P.valuationRing :=
    Differential.simplePoleResidueCoordinate (k := k) (F := RatFunc k) P
      ⟨omega, homega⟩
  have hpi : (pi : RatFunc k) ≠ 0 := by
    change P.uniformizer ≠ 0
    exact Differential.localParameter_ne_zero (k := k) (F := RatFunc k) P
  have hepi : e (pi : RatFunc k) ≠ 0 :=
    (map_ne_zero_iff _ e.injective).mpr hpi
  have homegaDecomposition :
      omega = (r : RatFunc k) •
        Differential.logarithmicDifferential (k := k) (F := RatFunc k)
          (pi : RatFunc k) := by
    exact
      Differential.simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
        (k := k) (F := RatFunc k) P ⟨omega, homega⟩
  have htransportDecomposition :
      rationalDifferentialInvolution (k := k) omega =
        ((eO r : Q.valuationRing) : RatFunc k) •
          Differential.logarithmicDifferential (k := k) (F := RatFunc k)
            (e (pi : RatFunc k)) := by
    calc
      rationalDifferentialInvolution (k := k) omega =
          rationalDifferentialInvolution (k := k)
            ((r : RatFunc k) •
              Differential.logarithmicDifferential (k := k) (F := RatFunc k)
                (pi : RatFunc k)) := by rw [homegaDecomposition]
      _ = e (r : RatFunc k) •
          rationalDifferentialInvolution (k := k)
            (Differential.logarithmicDifferential
              (k := k) (F := RatFunc k) (pi : RatFunc k)) := by
        rw [rationalDifferentialInvolution_smul]
      _ = ((eO r : Q.valuationRing) : RatFunc k) •
          Differential.logarithmicDifferential (k := k) (F := RatFunc k)
            (e (pi : RatFunc k)) := by
        rw [rationalDifferentialInvolution_logarithmicDifferential]
        rfl
  let logAt : Differential.simplePoleDifferentialLattice Q :=
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := RatFunc k) Q (e (pi : RatFunc k)) hepi
  have htransport : rationalDifferentialInvolution (k := k) omega ∈
      Differential.simplePoleDifferentialLattice Q := by
    rw [htransportDecomposition]
    exact (Differential.simplePoleDifferentialLattice Q).smul_mem
      (eO r) logAt.property
  refine ⟨htransport, ?_⟩
  have htransportSubtype :
      (⟨rationalDifferentialInvolution (k := k) omega, htransport⟩ :
          Differential.simplePoleDifferentialLattice Q) = eO r • logAt := by
    apply Subtype.ext
    exact htransportDecomposition
  have horder : Q.order (e (pi : RatFunc k)) = 1 := by
    change (xAdicPlace k).order
        (InverseAffinePlace.rationalInvolution k (pi : RatFunc k)) = 1
    rw [xAdic_order_rationalInvolution_eq_rationalInfinity_order]
    exact P.order_uniformizer
  have hresidue :
      Differential.simplePoleResidue (k := k) (F := RatFunc k) Q
          ⟨rationalDifferentialInvolution (k := k) omega, htransport⟩ =
        eκ (Differential.simplePoleResidue (k := k) (F := RatFunc k) P
          ⟨omega, homega⟩) := by
    rw [htransportSubtype,
      Differential.simplePoleResidue_smul,
      show logAt = Differential.logarithmicDifferentialAtSimplePole
        (k := k) (F := RatFunc k) Q (e (pi : RatFunc k)) hepi from rfl,
      Differential.simplePoleResidue_logarithmicDifferential,
      horder, Int.cast_one, mul_one,
      Differential.simplePoleResidue_eq_residueCoordinate]
    exact (rationalInfinityResidueEquivXAdic_residue (k := k) r).symm
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    GlobalPlace.residueField_finiteDimensional P
  letI : Algebra k Q.residueField := GlobalPlace.residueAlgebra Q
  letI : FiniteDimensional k Q.residueField :=
    GlobalPlace.residueField_finiteDimensional Q
  change Algebra.trace k Q.residueField
      (Differential.simplePoleResidue (k := k) (F := RatFunc k) Q
        ⟨rationalDifferentialInvolution (k := k) omega, htransport⟩) =
    Algebra.trace k P.residueField
      (Differential.simplePoleResidue (k := k) (F := RatFunc k) P
        ⟨omega, homega⟩)
  rw [hresidue]
  exact trace_rationalInfinityResidueEquivXAdic
    (k := k) (Differential.simplePoleResidue (k := k) (F := RatFunc k) P
      ⟨omega, homega⟩)

end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
