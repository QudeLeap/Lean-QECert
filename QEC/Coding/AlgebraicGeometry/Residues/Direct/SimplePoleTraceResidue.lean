import Mathlib.RingTheory.Ideal.Quotient.Operations
import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorResidueTransport
import QEC.Coding.AlgebraicGeometry.Residues.Direct.SemilocalDifferentialTraceRegularity
import QEC.Coding.AlgebraicGeometry.Residues.Direct.SemilocalSmithTraceResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Direct simple-pole trace--residue compatibility

For one finite rational place, a differential with at most a simple pole at
every actual upper factor has a differential trace with at most a simple pole.
Its normalized rational residue is the canonical transport of the sum of the
traced normalized residues at all upper factors.

The proof selects one integral coefficient with the prescribed upper residue
classes by the Chinese remainder theorem.  The corresponding simultaneous
order-one logarithmic differential has those same residues.  Their difference
is therefore regular at every upper factor, so the established semilocal
regularity theorem applies to its differential trace.  The Smith trace--residue
sum computes the remaining logarithmic model symbolically.

This is a direct finite-fibre result.  It does not treat the inverse chart,
assert a global residue theorem, or prove duality, genus, canonical degree, or
Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue

open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

local instance : Module.Finite (R k) (B k F) :=
  AffinePlace.finite_ringOfIntegers k F

open DirectFactorResidueTransport DirectFactorTraceResidue
open DirectIntegralDifferentialResidue
open DirectSemilocalDifferentialTraceRegularity
open DirectSemilocalSmithTraceResidue
open FunctionFieldDifferential

omit [Finite k] in
private theorem directFactors_isCoprime_of_ne
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hPQ : P ≠ Q) :
    IsCoprime (P : Ideal (B k F)) (Q : Ideal (B k F)) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.IsMaximal.coprime_of_ne
    ((Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P))
    ((Ideal.Factors.isPrime p.asIdeal Q).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal Q))
  intro hideal
  apply hPQ
  exact Subtype.ext hideal

private theorem exists_directIntegral_with_factorResidues
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (rho : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField) :
    ∃ b : B k F,
      ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        (AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b) = rho P := by
  classical
  let I := fun P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset =>
    (P : Ideal (B k F))
  have hI : Pairwise fun P Q => IsCoprime (I P) (I Q) := by
    intro P Q hPQ
    exact directFactors_isCoprime_of_ne k F p P Q hPQ
  let x : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      B k F ⧸ I P := fun P => by
    letI : (P : Ideal (B k F)).IsMaximal :=
      (Ideal.Factors.isPrime p.asIdeal P).isMaximal
        (Ideal.Factors.ne_bot p.asIdeal P)
    exact (Ideal.Factors.quotientResidueEquiv (P : Ideal (B k F))).symm
      ((directFactorResidueEquiv k F p P).symm (rho P))
  obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective hI x
  refine ⟨b, ?_⟩
  intro P
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  rw [← directFactorResidueEquiv_algebraMap]
  change directFactorResidueEquiv k F p P
      (Ideal.Factors.quotientResidueEquiv (P : Ideal (B k F))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b)) = rho P
  rw [hb P]
  simp only [x, RingEquiv.apply_symm_apply]

private theorem mem_localDifferentialLattice_of_simplePoleResidue_eq_zero
    (P : GlobalPlace k F)
    (omega : Differential.simplePoleDifferentialLattice P)
    (homega : Differential.simplePoleResidue (k := k) (F := F) P omega = 0) :
    (omega : Differential k F) ∈ Differential.localDifferentialLattice P := by
  change omega ∈ Differential.regularDifferentialSubmoduleOfSimplePole P
  apply (Submodule.Quotient.mk_eq_zero
    (p := Differential.regularDifferentialSubmoduleOfSimplePole P)
    (x := omega)).mp
  apply (Differential.simplePoleResidueEquiv (k := k) (F := F) P).injective
  simp only [map_zero]
  exact homega

/-- Differential trace is compatible with normalized simple-pole residues
over every actual factor above one direct finite rational place. -/
theorem functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (omega : Differential k F)
    (homega : ∀ P : (factors
        (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p),
      Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          ⟨functionFieldDifferentialTrace (k := k) (F := F) omega, htrace⟩ =
        DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
          (∑ P : (factors
              (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
            directFactorPlaceTrace k F p P
              (Differential.simplePoleResidue (k := k) (F := F)
                (AffinePlace.globalPlace k F (directFactorPlace k F p P))
                ⟨omega, homega P⟩)) := by
  classical
  let rho := fun P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset =>
    Differential.simplePoleResidue (k := k) (F := F)
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
      ⟨omega, homega P⟩
  obtain ⟨b, hb⟩ := exists_directIntegral_with_factorResidues k F p rho
  obtain ⟨t, ht, source, target, a, ha, hdiag, horder,
      htraceModel, hresidueModel⟩ :=
    exists_directSemilocalSmith_trace_residue_sum_compatibility k F p b
  let model : Differential k F :=
    algebraMap (B k F) F b •
      Differential.logarithmicDifferential (k := k) (F := F)
        (algebraMap (B k F) F t)
  let eta : Differential k F := omega - model
  let modelAt := fun P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset =>
    DirectFactorSemilocalLogarithmicResidue.directFactorSemilocalLogarithmicDifferentialAtSimplePole
      k F p P t ht b
  have hmodelResidue : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (modelAt P) = rho P := by
    intro P
    unfold modelAt
    unfold DirectFactorSemilocalLogarithmicResidue.directFactorSemilocalLogarithmicDifferentialAtSimplePole
    rw [Differential.simplePoleResidue_smul,
      Differential.simplePoleResidue_logarithmicDifferential,
      horder P, Int.cast_one, mul_one]
    exact hb P
  have hetaSimple : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      eta ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) := by
    intro P
    have hsub := (Differential.simplePoleDifferentialLattice
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))).sub_mem
        (homega P) (modelAt P).property
    exact hsub
  have hetaResidueZero : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          ⟨eta, hetaSimple P⟩ = 0 := by
    intro P
    have hsubtype :
        (⟨eta, hetaSimple P⟩ : Differential.simplePoleDifferentialLattice
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))) =
          ⟨omega, homega P⟩ - modelAt P := by
      apply Subtype.ext
      rfl
    rw [hsubtype, map_sub, hmodelResidue P]
    change rho P - rho P = 0
    exact sub_self _
  have hetaRegular : ∀ P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
      eta ∈ Differential.localDifferentialLattice
        (AffinePlace.globalPlace k F (directFactorPlace k F p P)) := by
    intro P
    exact mem_localDifferentialLattice_of_simplePoleResidue_eq_zero
      k F _ ⟨eta, hetaSimple P⟩ (hetaResidueZero P)
  have htraceEtaRegular :
      functionFieldDifferentialTrace (k := k) (F := F) eta ∈
        Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) :=
    functionFieldDifferentialTrace_mem_rationalAdic_of_mem_directFactorLattices
      k F p eta hetaRegular
  let smithAt : Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p) :=
    Differential.rationalAdicSmithLogarithmicDifferentialAtSimplePole p
      source target a ha (Algebra.lmul (R k) (B k F) b)
  have htraceModelSimple :
      functionFieldDifferentialTrace (k := k) (F := F) model ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p) := by
    rw [← htraceModel]
    exact smithAt.property
  have htraceEtaSimple :
      functionFieldDifferentialTrace (k := k) (F := F) eta ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p) :=
    Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p) htraceEtaRegular
  have homegaDecomposition : omega = eta + model := by
    dsimp only [eta]
    abel
  have htraceDecomposition :
      functionFieldDifferentialTrace (k := k) (F := F) omega =
        functionFieldDifferentialTrace (k := k) (F := F) eta +
          functionFieldDifferentialTrace (k := k) (F := F) model := by
    rw [homegaDecomposition, map_add]
  have htraceSimple :
      functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic p) := by
    rw [htraceDecomposition]
    exact (Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p)).add_mem htraceEtaSimple htraceModelSimple
  refine ⟨htraceSimple, ?_⟩
  let traceEtaAt : Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p) :=
    ⟨functionFieldDifferentialTrace (k := k) (F := F) eta,
      htraceEtaSimple⟩
  have htraceSubtype :
      (⟨functionFieldDifferentialTrace (k := k) (F := F) omega, htraceSimple⟩ :
          Differential.simplePoleDifferentialLattice
            (GlobalPlace.rationalAdic p)) =
        traceEtaAt + smithAt := by
    apply Subtype.ext
    change functionFieldDifferentialTrace (k := k) (F := F) omega =
      functionFieldDifferentialTrace (k := k) (F := F) eta +
        (smithAt : Differential k (RatFunc k))
    rw [htraceDecomposition, htraceModel]
  have hsum :
      (∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        Ideal.Factors.factorResidueTrace p.asIdeal P b) =
        ∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          directFactorPlaceTrace k F p P (rho P) := by
    apply Finset.sum_congr rfl
    intro P _
    rw [← hb P]
    exact (directFactorPlaceTrace_residue_integral k F p P b).symm
  calc
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        ⟨functionFieldDifferentialTrace (k := k) (F := F) omega,
          htraceSimple⟩ =
      Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p) traceEtaAt +
        Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p) smithAt := by
      rw [htraceSubtype, map_add]
    _ = Differential.simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p) smithAt := by
      rw [Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
        traceEtaAt htraceEtaRegular, zero_add]
    _ = DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          Ideal.Factors.factorResidueTrace p.asIdeal P b) := hresidueModel
    _ = DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k p
        (∑ P : (factors
            (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
          directFactorPlaceTrace k F p P (rho P)) := by rw [hsum]
    _ = _ := rfl

end QEC.Coding.AlgebraicGeometry.DirectSimplePoleTraceResidue
