import QEC.Coding.AlgebraicGeometry.Residues.Global.SimplePoleResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Residues of logarithmic differentials

This module proves the local formula
`res_P (df / f) = ord_P(f)` for every nonzero function-field element.  The
integer order is reduced in the actual residue field of the place.  It also
proves that logarithmic differentials have at most simple poles at every
global place.

The construction is local and compositional: a nonzero function is factored
as a valuation-ring unit times the corresponding integer power of the
normalized uniformizer.  No global trace sum, higher-order residue, duality,
or Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace Differential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]

private noncomputable def logarithmicDifferentialMonoidHom :
    Fˣ →* Multiplicative (Differential k F) where
  toFun f := Multiplicative.ofAdd
    (logarithmicDifferential (k := k) (F := F) (f : F))
  map_one' := by
    simp only [logarithmicDifferential, Units.val_one, inv_one, one_smul]
    rw [← map_one (algebraMap k F), differential_algebraMap]
    rfl
  map_mul' f g := by
    exact congrArg Multiplicative.ofAdd
      (logarithmicDifferential_mul (k := k) (F := F) (f : F) (g : F)
        f.ne_zero g.ne_zero)

/-- Integer powers scale logarithmic differentials by the same integer. -/
theorem logarithmicDifferential_zpow (f : Fˣ) (n : ℤ) :
    logarithmicDifferential (k := k) (F := F) ((f ^ n : Fˣ) : F) =
      n • logarithmicDifferential (k := k) (F := F) (f : F) := by
  have h := (logarithmicDifferentialMonoidHom (k := k) (F := F)).map_zpow f n
  exact h

private theorem localParameterPower_valuation (P : GlobalPlace k F) (n : ℤ) :
    P.valuation (localParameterPower P n) = WithZero.exp (-n) := by
  rw [localParameterPower, Units.val_zpow_eq_zpow_val, map_zpow₀,
    localParameterUnit, Units.val_mk0, localParameter, P.valuation_uniformizer,
    ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem exists_unit_mul_localParameterPower_eq
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    ∃ u : P.valuationRingˣ,
      (u : F) * localParameterPower P (P.order f) = f := by
  let t : F := localParameterPower P (P.order f)
  have ht : t ≠ 0 := by
    exact Units.ne_zero _
  have hvaluation :
      P.valuation f = P.valuation t := by
    calc
      P.valuation f = WithZero.exp (WithZero.log (P.valuation f)) :=
        (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hf)).symm
      _ = WithZero.exp (-P.order f) := by simp [GlobalPlace.order]
      _ = P.valuation t :=
        (localParameterPower_valuation (k := k) (F := F) P (P.order f)).symm
  let q : Fˣ := Units.mk0 (f * t⁻¹) (mul_ne_zero hf (inv_ne_zero ht))
  have hqvaluation : P.valuation (q : F) = 1 := by
    change P.valuation (f * t⁻¹) = 1
    rw [map_mul, map_inv₀, hvaluation, mul_inv_cancel₀]
    exact (P.valuation).ne_zero_iff.mpr ht
  have hqmem : q ∈ P.valuationRing.unitGroup :=
    (Valuation.mem_unitGroup_iff F P.valuation q).mpr hqvaluation
  let u : P.valuationRingˣ := P.valuationRing.unitGroupMulEquiv ⟨q, hqmem⟩
  refine ⟨u, ?_⟩
  change (q : F) * t = f
  simp only [q, Units.val_mk0]
  field_simp [ht]

private theorem logarithmicDifferential_eq_unit_add_order_smul
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    ∃ u : P.valuationRingˣ,
      logarithmicDifferential (k := k) (F := F) f =
        logarithmicDifferential (k := k) (F := F) (u : F) +
          P.order f • logarithmicDifferential (k := k) (F := F)
            (P.uniformizerInValuationRing : F) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_localParameterPower_eq
    (k := k) (F := F) P f hf
  refine ⟨u, ?_⟩
  have hu_ne : (u : F) ≠ 0 := by
    intro hzero
    apply u.ne_zero
    apply Subtype.ext
    exact hzero
  have ht_ne : localParameterPower P (P.order f) ≠ 0 := Units.ne_zero _
  calc
    logarithmicDifferential (k := k) (F := F) f =
        logarithmicDifferential (k := k) (F := F)
          ((u : F) * localParameterPower P (P.order f)) := by rw [hu]
    _ = logarithmicDifferential (k := k) (F := F) (u : F) +
          logarithmicDifferential (k := k) (F := F)
            (localParameterPower P (P.order f)) :=
      logarithmicDifferential_mul (k := k) (F := F) _ _ hu_ne ht_ne
    _ = logarithmicDifferential (k := k) (F := F) (u : F) +
          P.order f • logarithmicDifferential (k := k) (F := F)
            (P.uniformizerInValuationRing : F) := by
      congr 1
      exact logarithmicDifferential_zpow (k := k) (F := F)
        (localParameterUnit P) (P.order f)

private theorem logarithmicDifferential_mem_simplePoleDifferentialLattice
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    logarithmicDifferential (k := k) (F := F) f ∈
      simplePoleDifferentialLattice P := by
  obtain ⟨u, hu⟩ := logarithmicDifferential_eq_unit_add_order_smul
    (k := k) (F := F) P f hf
  rw [hu]
  exact (simplePoleDifferentialLattice P).add_mem
    (localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := F) P
      (logarithmicDifferential_mem_localDifferentialLattice_of_unit
        (k := k) (F := F) P u))
    (AddSubgroup.zsmul_mem (simplePoleDifferentialLattice P).toAddSubgroup
      (uniformizerLogDifferential (k := k) (F := F) P).property (P.order f))

/-- The logarithmic differential of a nonzero function, regarded as an
actual member of the local simple-pole lattice. -/
noncomputable def logarithmicDifferentialAtSimplePole
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleDifferentialLattice P :=
  ⟨logarithmicDifferential (k := k) (F := F) f,
    logarithmicDifferential_mem_simplePoleDifferentialLattice
      (k := k) (F := F) P f hf⟩

/-- Every nonzero function's logarithmic differential has at most a simple
pole at every global place. -/
theorem logarithmicDifferential_isGlobalSimplePole (f : F) (hf : f ≠ 0) :
    IsGlobalSimplePole (k := k) (F := F)
      (logarithmicDifferential (k := k) (F := F) f) := by
  intro P
  exact (logarithmicDifferentialAtSimplePole
    (k := k) (F := F) P f hf).property

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The normalized local residue of `df / f` is the integer order of `f`,
reduced in the actual residue field. -/
theorem simplePoleResidue_logarithmicDifferential
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleResidue (k := k) (F := F) P
        (logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf) =
      (P.order f : GlobalPlace.residueField P) := by
  obtain ⟨u, hu⟩ := logarithmicDifferential_eq_unit_add_order_smul
    (k := k) (F := F) P f hf
  let unitLog : simplePoleDifferentialLattice P :=
    ⟨logarithmicDifferential (k := k) (F := F) (u : F),
      localDifferentialLattice_le_simplePoleDifferentialLattice
        (k := k) (F := F) P
        (logarithmicDifferential_mem_localDifferentialLattice_of_unit
          (k := k) (F := F) P u)⟩
  have hdecomposition :
      logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf =
        unitLog + P.order f • uniformizerLogDifferential (k := k) (F := F) P := by
    apply Subtype.ext
    exact hu
  rw [hdecomposition, map_add, map_zsmul,
    simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P unitLog,
    simplePoleResidue_uniformizerLogDifferential (k := k) (F := F) P,
    zero_add, zsmul_one]
  exact logarithmicDifferential_mem_localDifferentialLattice_of_unit
    (k := k) (F := F) P u

end Differential

end QEC.Coding.AlgebraicGeometry
