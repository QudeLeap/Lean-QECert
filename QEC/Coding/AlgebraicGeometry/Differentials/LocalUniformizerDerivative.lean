import QEC.Coding.AlgebraicGeometry.Differentials.CanonicalDifferential
import QEC.Coding.AlgebraicGeometry.Differentials.LocalLogarithmicDifferential

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The derivative of a local uniformizer

For a place of a finite separable one-variable function field, this module
proves that the derivative of the normalized valuation uniformizer generates
the actual local derivative lattice.  The proof uses Frobenius in the finite
residue field and the already-established principal-cutoff theorem.

This is a local algebra statement.  It does not identify `dπ` as a basis of
the Kähler differentials of the valuation ring, choose a canonical residue
functional, or state a global residue or Riemann--Roch theorem.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

omit [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F] in
/-- The cardinality of a global place's finite residue field vanishes in the
function field. -/
private theorem residueFieldCard_cast_eq_zero (P : GlobalPlace k F)
    [Fintype P.residueField] :
    ((Fintype.card P.residueField : ℕ) : F) = 0 := by
  have hresidue : ((Fintype.card P.residueField : ℕ) : P.residueField) = 0 :=
    FiniteField.cast_card_eq_zero P.residueField
  have hconstant : ((Fintype.card P.residueField : ℕ) : k) = 0 := by
    apply (GlobalPlace.constantsToResidue P).injective
    simpa only [map_natCast, map_zero] using hresidue
  calc
    ((Fintype.card P.residueField : ℕ) : F) =
        algebraMap k F ((Fintype.card P.residueField : ℕ) : k) := by simp
    _ = algebraMap k F 0 := by rw [hconstant]
    _ = 0 := map_zero _

/-- Every actual derivative value belongs to the sum of the span of `Dπ` and
the uniformizer multiple of the full local derivative lattice. -/
private theorem functionFieldDerivation_mem_uniformizerDerivative_sup
    (P : GlobalPlace k F) (x : P.valuationRing) :
    functionFieldDerivation (k := k) (F := F) (x : F) ∈
      Submodule.span P.valuationRing
          ({functionFieldDerivation (k := k) (F := F)
            (P.uniformizerInValuationRing : F)} : Set F) ⊔
        (localDerivativeLattice (k := k) (F := F) P).map
          (LinearMap.lsmul P.valuationRing F P.uniformizerInValuationRing) := by
  classical
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Finite P.residueField := GlobalPlace.finite_residueField P
  letI : Fintype P.residueField := Fintype.ofFinite _
  let q : ℕ := Fintype.card P.residueField
  let D : Derivation k F F := functionFieldDerivation (k := k) (F := F)
  let pi : P.valuationRing := P.uniformizerInValuationRing
  have hresidue : P.residue (x ^ q - x) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hmaximal : x ^ q - x ∈ IsLocalRing.maximalIdeal P.valuationRing :=
    (GlobalPlace.residue_eq_zero_iff P _).mp hresidue
  rw [P.maximalIdeal_eq_span_uniformizer, Ideal.mem_span_singleton'] at hmaximal
  rcases hmaximal with ⟨r, hr⟩
  have hrF : (r : F) * (pi : F) = (x : F) ^ q - (x : F) := by
    exact congrArg (fun z : P.valuationRing => (z : F)) hr
  have hqF : (q : F) = 0 := by
    simpa only [q] using residueFieldCard_cast_eq_zero (k := k) (F := F) P
  have hderivative := congrArg D hrF
  have hxformula :
      D (x : F) = (-(r : F)) * D (pi : F) + (pi : F) * (-D (r : F)) := by
    rw [D.leibniz, map_sub, D.leibniz_pow] at hderivative
    simp only [nsmul_eq_mul, smul_eq_mul, hqF, zero_mul, zero_sub] at hderivative
    calc
      D (x : F) = -(-D (x : F)) := by ring
      _ = -((r : F) * D (pi : F) + (pi : F) * D (r : F)) := by
        rw [← hderivative]
      _ = (-(r : F)) * D (pi : F) + (pi : F) * (-D (r : F)) := by ring
  have hleft : (-(r : F)) * D (pi : F) ∈
      Submodule.span P.valuationRing ({D (pi : F)} : Set F) := by
    refine Submodule.mem_span_singleton.mpr ⟨-r, ?_⟩
    change (-(r : F)) * D (pi : F) = (-(r : F)) * D (pi : F)
    rfl
  have hDr : D (r : F) ∈ localDerivativeLattice (k := k) (F := F) P :=
    Submodule.subset_span ⟨r, rfl⟩
  have hright : (pi : F) * (-D (r : F)) ∈
      (localDerivativeLattice (k := k) (F := F) P).map
        (LinearMap.lsmul P.valuationRing F pi) := by
    refine ⟨-D (r : F),
      (localDerivativeLattice (k := k) (F := F) P).neg_mem hDr, ?_⟩
    change (pi : F) * (-D (r : F)) = (pi : F) * (-D (r : F))
    rfl
  exact Submodule.mem_sup.mpr
    ⟨_, hleft, _, hright, hxformula.symm⟩

/-- Relative to any actual principal-cutoff generator, `Dπ` differs from that
generator by a valuation-ring unit. -/
private theorem exists_isUnit_smul_eq_uniformizerDerivative_of_principalCutoff
    (P : GlobalPlace k F) (a : F)
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    ∃ s : P.valuationRing, IsUnit s ∧
      s • a = functionFieldDerivation (k := k) (F := F)
        (P.uniformizerInValuationRing : F) := by
  classical
  let D : Derivation k F F := functionFieldDerivation (k := k) (F := F)
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let L : Submodule P.valuationRing F :=
    localDerivativeLattice (k := k) (F := F) P
  let S : Submodule P.valuationRing F :=
    Submodule.span P.valuationRing ({D (pi : F)} : Set F)
  let piL : Submodule P.valuationRing F :=
    L.map (LinearMap.lsmul P.valuationRing F pi)
  have hL_le : L ≤ S ⊔ piL := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    exact functionFieldDerivation_mem_uniformizerDerivative_sup
      (k := k) (F := F) P x
  have ha_mem : a ∈ L := by
    change a ∈ localDerivativeLattice (k := k) (F := F) P
    rw [ha.2.1]
    exact Submodule.mem_span_singleton_self a
  have ha_sup : a ∈ S ⊔ piL := hL_le ha_mem
  rcases Submodule.mem_sup.mp ha_sup with ⟨y, hy, z, hz, hyz⟩
  rcases Submodule.mem_span_singleton.mp hy with ⟨u, hu⟩
  rcases hz with ⟨b, hb, hbz⟩
  have hb' : b ∈ Submodule.span P.valuationRing ({a} : Set F) := by
    change b ∈ localDerivativeLattice (k := k) (F := F) P at hb
    rwa [ha.2.1] at hb
  rcases Submodule.mem_span_singleton.mp hb' with ⟨t, ht⟩
  have hDpi_mem : D (pi : F) ∈ L := Submodule.subset_span ⟨pi, rfl⟩
  have hDpi' : D (pi : F) ∈ Submodule.span P.valuationRing ({a} : Set F) := by
    change D (pi : F) ∈ localDerivativeLattice (k := k) (F := F) P at hDpi_mem
    rwa [ha.2.1] at hDpi_mem
  rcases Submodule.mem_span_singleton.mp hDpi' with ⟨s, hs⟩
  have huF : (u : F) * D (pi : F) = y := by
    exact hu
  have htF : (t : F) * a = b := by
    exact ht
  have hsF : (s : F) * a = D (pi : F) := by
    exact hs
  have hbzF : (pi : F) * b = z := by
    exact hbz
  have hdecomposition : (u : F) * D (pi : F) + (pi : F) * b = a := by
    calc
      (u : F) * D (pi : F) + (pi : F) * b = y + z := by rw [huF, hbzF]
      _ = a := hyz
  have hcoefficientF : (u : F) * (s : F) + (pi : F) * (t : F) = 1 := by
    apply mul_right_cancel₀ ha.1
    calc
      ((u : F) * (s : F) + (pi : F) * (t : F)) * a =
          (u : F) * ((s : F) * a) + (pi : F) * ((t : F) * a) := by ring
      _ = (u : F) * D (pi : F) + (pi : F) * b := by rw [hsF, htF]
      _ = a := hdecomposition
      _ = 1 * a := by rw [one_mul]
  have hcoefficient : u * s + pi * t = 1 := by
    apply Subtype.ext
    exact hcoefficientF
  have hs_not_maximal : s ∉ IsLocalRing.maximalIdeal P.valuationRing := by
    intro hs_maximal
    have hpi_maximal : pi ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      rw [P.maximalIdeal_eq_span_uniformizer]
      exact Ideal.mem_span_singleton_self pi
    have hus : u * s ∈ IsLocalRing.maximalIdeal P.valuationRing :=
      (IsLocalRing.maximalIdeal P.valuationRing).mul_mem_left u hs_maximal
    have hpit : pi * t ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      simpa only [mul_comm] using
        (IsLocalRing.maximalIdeal P.valuationRing).mul_mem_left t hpi_maximal
    have hone : (1 : P.valuationRing) ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      rw [← hcoefficient]
      exact (IsLocalRing.maximalIdeal P.valuationRing).add_mem hus hpit
    simp at hone
  have hs_unit : IsUnit s := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using
      hs_not_maximal
  exact ⟨s, hs_unit, hs⟩

/-- The derivative of the normalized valuation uniformizer generates the
actual local derivative lattice. -/
theorem localDerivativeLattice_eq_span_uniformizerDerivative
    (P : GlobalPlace k F) :
    localDerivativeLattice (k := k) (F := F) P =
      Submodule.span P.valuationRing
        ({functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F)} : Set F) := by
  obtain ⟨a, ha⟩ :=
    exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P
  obtain ⟨s, hs_unit, hs⟩ :=
    exists_isUnit_smul_eq_uniformizerDerivative_of_principalCutoff
      (k := k) (F := F) P a ha
  calc
    localDerivativeLattice (k := k) (F := F) P =
        Submodule.span P.valuationRing ({a} : Set F) := ha.2.1
    _ = Submodule.span P.valuationRing ({s • a} : Set F) :=
      (Submodule.span_singleton_smul_eq hs_unit a).symm
    _ = Submodule.span P.valuationRing
        ({functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F)} : Set F) := by rw [hs]

/-- The function-field derivative of the normalized valuation uniformizer is
nonzero. -/
theorem functionFieldDerivation_uniformizer_ne_zero (P : GlobalPlace k F) :
    functionFieldDerivation (k := k) (F := F)
      (P.uniformizerInValuationRing : F) ≠ 0 := by
  obtain ⟨a, ha⟩ :=
    exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P
  have ha_mem : a ∈ localDerivativeLattice (k := k) (F := F) P := by
    rw [ha.2.1]
    exact Submodule.mem_span_singleton_self a
  rw [localDerivativeLattice_eq_span_uniformizerDerivative
    (k := k) (F := F) P] at ha_mem
  intro hzero
  rw [hzero] at ha_mem
  have ha_zero : a = 0 := by
    rcases Submodule.mem_span_singleton.mp ha_mem with ⟨r, hr⟩
    simpa using hr.symm
  exact ha.1 ha_zero

/-- The derivative of the normalized uniformizer satisfies the complete
principal-cutoff contract. -/
theorem uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (P : GlobalPlace k F) :
    IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P
      (functionFieldDerivation (k := k) (F := F)
        (P.uniformizerInValuationRing : F)) := by
  let a : F := functionFieldDerivation (k := k) (F := F)
    (P.uniformizerInValuationRing : F)
  change IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a
  have ha_ne : a ≠ 0 :=
    functionFieldDerivation_uniformizer_ne_zero (k := k) (F := F) P
  have hspan : localDerivativeLattice (k := k) (F := F) P =
      Submodule.span P.valuationRing ({a} : Set F) :=
    localDerivativeLattice_eq_span_uniformizerDerivative (k := k) (F := F) P
  refine ⟨ha_ne, hspan, ?_⟩
  intro x
  constructor
  · intro hx
    rw [hspan] at hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨r, hr⟩
    by_cases hr0 : (r : F) = 0
    · left
      rw [← hr]
      change (r : F) * a = 0
      rw [hr0, zero_mul]
    · right
      have hr_order : 0 ≤ P.order (r : F) :=
        (GlobalPlace.regularAt_iff_order_nonnegative P hr0).mp
          ((GlobalPlace.regularAt_iff_mem_valuationRing P _).mpr r.property)
      have hx_order : P.order x = P.order (r : F) + P.order a := by
        rw [← hr]
        change P.order ((r : F) * a) = P.order (r : F) + P.order a
        exact GlobalPlace.order_mul P hr0 ha_ne
      omega
  · rintro (rfl | hx_order)
    · exact Submodule.zero_mem _
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [hspan]
        refine Submodule.mem_span_singleton.mpr ⟨⟨x * a⁻¹, ?_⟩, ?_⟩
        · apply (GlobalPlace.regularAt_iff_mem_valuationRing P _).mp
          apply (GlobalPlace.regularAt_iff_order_nonnegative P
            (mul_ne_zero hx0 (inv_ne_zero ha_ne))).mpr
          rw [GlobalPlace.order_mul P hx0 (inv_ne_zero ha_ne),
            GlobalPlace.order_inv]
          omega
        · change (x * a⁻¹) * a = x
          rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]

end FunctionFieldDifferential

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The normalized uniformizer's logarithmic differential represents a
nonzero class in the simple-pole quotient. -/
theorem uniformizerLogDifferentialClass_ne_zero (P : GlobalPlace k F) :
    uniformizerLogDifferentialClass (k := k) (F := F) P ≠ 0 := by
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let a : F := functionFieldDerivation (k := k) (F := F) (pi : F)
  have hpi_ne : (pi : F) ≠ 0 := by
    change P.uniformizer ≠ 0
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have ha := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (k := k) (F := F) P
  intro hzero
  change (Submodule.Quotient.mk
      (uniformizerLogDifferential (k := k) (F := F) P) :
        localResidueLine P) = 0 at hzero
  have hquotient :
      (Submodule.Quotient.mk
          (uniformizerLogDifferential (k := k) (F := F) P) :
            localResidueLine P) = 0 := by
    exact hzero
  have hregular := (Submodule.Quotient.mk_eq_zero
    (p := regularDifferentialSubmoduleOfSimplePole P)
    (x := uniformizerLogDifferential (k := k) (F := F) P)).mp hquotient
  change (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) ∈
    localDifferentialLattice P at hregular
  have hcoordinate :=
    (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
      (k := k) (F := F) P
      (uniformizerLogDifferential (k := k) (F := F) P : Differential k F)).mp hregular
  have hcoordinate_eq :
      functionFieldDifferentialCoordinate (k := k) (F := F)
          (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) =
        (pi : F)⁻¹ * a := by
    change functionFieldDifferentialCoordinate (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) (pi : F)) =
      (pi : F)⁻¹ * a
    rw [logarithmicDifferential, map_smul,
      functionFieldDifferentialCoordinate_differential]
    rfl
  rw [hcoordinate_eq] at hcoordinate
  rcases (ha.2.2 ((pi : F)⁻¹ * a)).mp hcoordinate with hzero' | horder
  · exact (mul_ne_zero (inv_ne_zero hpi_ne) ha.1) hzero'
  · have horder_eq : P.order ((pi : F)⁻¹ * a) = -1 + P.order a := by
      rw [GlobalPlace.order_mul P (inv_ne_zero hpi_ne) ha.1,
        GlobalPlace.order_inv]
      change -P.order P.uniformizer + P.order a = -1 + P.order a
      rw [P.order_uniformizer]
    change P.order a ≤ P.order ((pi : F)⁻¹ * a) at horder
    rw [horder_eq] at horder
    omega

end Differential

end QEC.Coding.AlgebraicGeometry
