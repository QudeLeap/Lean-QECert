import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialLocal

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Local logarithmic differentials

This module constructs the logarithmic differential of the normalized local
uniformizer and its class in the already-built simple-pole quotient.  It
proves that multiplying the uniformizer by a valuation-ring unit does not
change that quotient class.

This is a parameter-independence prerequisite for the eventual local residue
map.  It does not prove that the class is nonzero, identify the quotient with
the residue field canonically, or state a global residue or Riemann--Roch law.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- The logarithmic differential `df / f` of a function-field element. -/
noncomputable def logarithmicDifferential (f : F) : Differential k F :=
  f⁻¹ • differential k F f

/-- Logarithmic differentials turn a product of nonzero functions into a sum. -/
theorem logarithmicDifferential_mul (f g : F) (hf : f ≠ 0) (hg : g ≠ 0) :
    logarithmicDifferential (k := k) (F := F) (f * g) =
      logarithmicDifferential (k := k) (F := F) f +
        logarithmicDifferential (k := k) (F := F) g := by
  rw [logarithmicDifferential, logarithmicDifferential,
    logarithmicDifferential, differential_mul, smul_add, smul_smul,
    smul_smul, add_comm]
  congr 1 <;> field_simp

/-- The logarithmic differential of a valuation-ring unit is regular. -/
theorem logarithmicDifferential_mem_localDifferentialLattice_of_unit
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    logarithmicDifferential (k := k) (F := F) (u : F) ∈
      localDifferentialLattice P := by
  have hdifferential := differential_mem_localDifferentialLattice
    (k := k) (F := F) P (u : P.valuationRing)
  have hsmul := (localDifferentialLattice P).smul_mem
    (↑(u⁻¹) : P.valuationRing) hdifferential
  rw [logarithmicDifferential]
  have hinv :
      P.valuationRing.subtype (↑(u⁻¹) : P.valuationRing) = (u : F)⁻¹ :=
    map_units_inv P.valuationRing.subtype u
  rw [← hinv]
  change (↑(u⁻¹) : P.valuationRing) • differential k F (u : F) ∈
    localDifferentialLattice P
  exact hsmul

/-- The logarithmic differential of the normalized uniformizer, as an actual
element of the simple-pole lattice. -/
noncomputable def uniformizerLogDifferential (P : GlobalPlace k F) :
    simplePoleDifferentialLattice P := by
  refine ⟨logarithmicDifferential (k := k) (F := F)
    (P.uniformizerInValuationRing : F), ?_⟩
  change P.uniformizerInValuationRing •
      logarithmicDifferential (k := k) (F := F)
        (P.uniformizerInValuationRing : F) ∈ localDifferentialLattice P
  rw [logarithmicDifferential, ← smul_assoc]
  change ((P.uniformizerInValuationRing : F) *
      (P.uniformizerInValuationRing : F)⁻¹) •
        differential k F (P.uniformizerInValuationRing : F) ∈
          localDifferentialLattice P
  rw [mul_inv_cancel₀, one_smul]
  · exact differential_mem_localDifferentialLattice
      (k := k) (F := F) P P.uniformizerInValuationRing
  · simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P

/-- Multiplying the normalized uniformizer by a valuation-ring unit gives a
second representative in the same simple-pole lattice. -/
noncomputable def unitMulUniformizerLogDifferential
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    simplePoleDifferentialLattice P := by
  have hu : (u : F) ≠ 0 := by
    intro hzero
    apply Units.ne_zero u
    apply Subtype.ext
    exact hzero
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  refine ⟨logarithmicDifferential (k := k) (F := F)
    ((u : F) * (P.uniformizerInValuationRing : F)), ?_⟩
  rw [logarithmicDifferential_mul (k := k) (F := F) _ _ hu hpi]
  exact (simplePoleDifferentialLattice P).add_mem
    (localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := F) P
      (logarithmicDifferential_mem_localDifferentialLattice_of_unit
        (k := k) (F := F) P u))
    (uniformizerLogDifferential (k := k) (F := F) P).property

/-- The quotient class represented by the logarithmic differential of the
normalized uniformizer. -/
noncomputable def uniformizerLogDifferentialClass (P : GlobalPlace k F) :
    localResidueLine P :=
  Submodule.Quotient.mk (uniformizerLogDifferential (k := k) (F := F) P)

/-- Multiplication of the uniformizer by a valuation-ring unit does not change
its logarithmic-differential class modulo regular differentials. -/
theorem unitMulUniformizerLogDifferentialClass_eq
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    Submodule.Quotient.mk
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u) =
      uniformizerLogDifferentialClass (k := k) (F := F) P := by
  apply (Submodule.Quotient.eq
    (regularDifferentialSubmoduleOfSimplePole P)).2
  change logarithmicDifferential (k := k) (F := F)
      ((u : F) * (P.uniformizerInValuationRing : F)) -
        logarithmicDifferential (k := k) (F := F)
          (P.uniformizerInValuationRing : F) ∈ localDifferentialLattice P
  have hu : (u : F) ≠ 0 := by
    intro hzero
    apply Units.ne_zero u
    apply Subtype.ext
    exact hzero
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  rw [logarithmicDifferential_mul (k := k) (F := F) _ _ hu hpi,
    add_sub_cancel_right]
  exact logarithmicDifferential_mem_localDifferentialLattice_of_unit
    (k := k) (F := F) P u

end Differential

end QEC.Coding.AlgebraicGeometry
