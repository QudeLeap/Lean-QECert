import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PrincipalShift

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# One-place increments of Riemann--Roch spaces

For a divisor `G` and a global place `P`, this module constructs the actual
leading-coefficient map from `L(G + P)` to the residue field at `P`.  Its
kernel is proved to be exactly the embedded copy of `L(G)`.

This is the local one-place input to the dimension argument.  It does not
prove a global residue theorem, duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The degree-one formal divisor supported at one actual global place.  Its
weighted degree is the residue degree of that place, not necessarily one. -/
noncomputable def placeDivisor (P : GlobalPlace k F) :
    Divisor (GlobalPlace k F) :=
  Finsupp.single P 1

@[simp]
theorem placeDivisor_apply (P : GlobalPlace k F) :
    placeDivisor P P = 1 := by
  classical
  simp [placeDivisor]

@[simp]
theorem placeDivisor_apply_of_ne (P Q : GlobalPlace k F) (hPQ : P ≠ Q) :
    placeDivisor P Q = 0 := by
  classical
  simp [placeDivisor, hPQ]

/-- The weighted degree of the one-place divisor is the actual residue
degree of its supporting place. -/
theorem placeDivisor_degree (P : GlobalPlace k F) :
    Divisor.degree (residueDegree (k := k) (F := F)) (placeDivisor P) =
      residueDegree (k := k) (F := F) P := by
  classical
  simp [Divisor.degree, Divisor.degreeHom, placeDivisor]

/-- Adding a nonnegative one-place divisor enlarges the corresponding
Riemann--Roch submodule. -/
theorem riemannRochSubmodule_le_add_placeDivisor
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    riemannRochSubmodule G ≤ riemannRochSubmodule (G + placeDivisor P) := by
  apply riemannRochSubmodule_mono
  intro Q
  simp only [Finsupp.add_apply]
  have hnonnegative : 0 ≤ placeDivisor P Q := by
    by_cases hPQ : P = Q
    · subst Q
      rw [placeDivisor_apply]
      norm_num
    · rw [placeDivisor_apply_of_ne P Q hPQ]
  omega

/-- The embedded copy of `L(G)` inside `L(G + P)`. -/
noncomputable def riemannRochPlaceIncrementSubmodule
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    Submodule k (riemannRochSubmodule (G + placeDivisor P)) :=
  (riemannRochSubmodule G).comap
    (riemannRochSubmodule (G + placeDivisor P)).subtype

private theorem localParameterPower_valuation
    (P : GlobalPlace k F) (n : ℤ) :
    P.valuation (Differential.localParameterPower P n) = WithZero.exp (-n) := by
  rw [Differential.localParameterPower, Units.val_zpow_eq_zpow_val, map_zpow₀,
    Differential.localParameterUnit, Units.val_mk0,
    Differential.localParameter, P.valuation_uniformizer,
    ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem localParameterPower_order
    (P : GlobalPlace k F) (n : ℤ) :
    P.order (Differential.localParameterPower P n) = n := by
  rw [order, localParameterPower_valuation]
  simp

private theorem localParameterPower_ne_zero
    (P : GlobalPlace k F) (n : ℤ) :
    Differential.localParameterPower P n ≠ 0 := by
  exact Units.ne_zero _

/-- The valuation-ring-valued leading coefficient of a member of `L(G + P)`.
The chosen normalized uniformizer is raised to `G(P)+1`, exactly cancelling
the allowed pole at `P`. -/
private noncomputable def riemannRochPlaceLeadingCoefficientValue
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : riemannRochSubmodule (G + placeDivisor P)) : P.valuationRing :=
  ⟨Differential.localParameterPower P (G P + 1) * (x : F), by
    by_cases hx : (x : F) = 0
    · simp only [hx, mul_zero]
      exact P.valuationRing.zero_mem
    · apply (regularAt_iff_mem_valuationRing P _).mp
      apply (regularAt_iff_order_nonnegative P
        (mul_ne_zero (localParameterPower_ne_zero P (G P + 1)) hx)).mpr
      rw [order_mul P (localParameterPower_ne_zero P (G P + 1)) hx,
        localParameterPower_order]
      have hxP :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative
          (G + placeDivisor P) hx).mp x.property P
      simp only [Finsupp.add_apply, placeDivisor_apply] at hxP
      omega⟩

private theorem riemannRochPlaceLeadingCoefficientValue_add
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x y : riemannRochSubmodule (G + placeDivisor P)) :
    riemannRochPlaceLeadingCoefficientValue G P (x + y) =
      riemannRochPlaceLeadingCoefficientValue G P x +
        riemannRochPlaceLeadingCoefficientValue G P y := by
  apply Subtype.ext
  change Differential.localParameterPower P (G P + 1) *
      ((x : F) + (y : F)) =
    Differential.localParameterPower P (G P + 1) * (x : F) +
      Differential.localParameterPower P (G P + 1) * (y : F)
  exact mul_add _ _ _

private theorem riemannRochPlaceLeadingCoefficientValue_smul
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (c : k)
    (x : riemannRochSubmodule (G + placeDivisor P)) :
    riemannRochPlaceLeadingCoefficientValue G P (c • x) =
      constantsToValuationRing P c *
        riemannRochPlaceLeadingCoefficientValue G P x := by
  apply Subtype.ext
  calc
    ((riemannRochPlaceLeadingCoefficientValue G P (c • x) :
        P.valuationRing) : F) =
        Differential.localParameterPower P (G P + 1) *
          (algebraMap k F c * (x : F)) := by
      simp only [riemannRochPlaceLeadingCoefficientValue,
        Submodule.coe_smul, Algebra.smul_def]
    _ = algebraMap k F c *
        (Differential.localParameterPower P (G P + 1) * (x : F)) := by
      ring
    _ = ((constantsToValuationRing P c *
        riemannRochPlaceLeadingCoefficientValue G P x :
          P.valuationRing) : F) := rfl

/-- Reduction of the actual one-place leading coefficient. -/
noncomputable def riemannRochPlaceLeadingCoefficient
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    riemannRochSubmodule (G + placeDivisor P) →ₗ[k] P.residueField := by
  letI : Algebra k P.residueField := residueAlgebra P
  refine
    { toFun := fun x => P.residue
        (riemannRochPlaceLeadingCoefficientValue G P x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    rw [riemannRochPlaceLeadingCoefficientValue_add, map_add]
  · intro c x
    rw [riemannRochPlaceLeadingCoefficientValue_smul, map_mul]
    change constantsToResidue P c *
        P.residue (riemannRochPlaceLeadingCoefficientValue G P x) =
      algebraMap k P.residueField c *
        P.residue (riemannRochPlaceLeadingCoefficientValue G P x)
    rfl

/-- The one-place leading coefficient vanishes exactly on the embedded copy
of `L(G)` inside `L(G + P)`. -/
theorem riemannRochPlaceLeadingCoefficient_ker
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    LinearMap.ker (riemannRochPlaceLeadingCoefficient G P) =
      riemannRochPlaceIncrementSubmodule G P := by
  letI : Algebra k P.residueField := residueAlgebra P
  ext x
  rw [LinearMap.mem_ker]
  change P.residue (riemannRochPlaceLeadingCoefficientValue G P x) = 0 ↔
    (x : F) ∈ riemannRochSubmodule G
  rw [P.residue_eq_zero_iff]
  constructor
  · intro hmaximal
    by_cases hx : (x : F) = 0
    · simpa only [hx] using (riemannRochSubmodule G).zero_mem
    · apply (mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mpr
      intro Q
      by_cases hQP : Q = P
      · subst Q
        rw [P.maximalIdeal_eq_span_uniformizer,
          Ideal.mem_span_singleton'] at hmaximal
        rcases hmaximal with ⟨r, hr⟩
        have hpi_ne : (P.uniformizerInValuationRing : F) ≠ 0 := by
          change P.uniformizer ≠ 0
          exact P.valuation.ne_zero_iff.mp (by
            rw [P.valuation_uniformizer]
            exact WithZero.exp_ne_zero)
        have hpi_order : P.order (P.uniformizerInValuationRing : F) = 1 := by
          change P.order P.uniformizer = 1
          exact P.order_uniformizer
        have hrF : (r : F) * (P.uniformizerInValuationRing : F) =
            Differential.localParameterPower P (G P + 1) * (x : F) := by
          exact congrArg (fun z : P.valuationRing => (z : F)) hr
        by_cases hr0 : (r : F) = 0
        · exfalso
          apply hx
          have hproduct :
              Differential.localParameterPower P (G P + 1) * (x : F) = 0 := by
            rw [← hrF, hr0, zero_mul]
          exact (mul_eq_zero.mp hproduct).resolve_left
            (localParameterPower_ne_zero P (G P + 1))
        · have hrOrder : 0 ≤ P.order (r : F) :=
            (regularAt_iff_order_nonnegative P hr0).mp
              ((regularAt_iff_mem_valuationRing P _).mpr r.property)
          have horder := congrArg P.order hrF
          rw [order_mul P hr0 hpi_ne,
            order_mul P (localParameterPower_ne_zero P (G P + 1)) hx,
            hpi_order, localParameterPower_order] at horder
          omega
      · have hxQ :=
          (mem_riemannRochSubmodule_iff_order_add_nonnegative
            (G + placeDivisor P) hx).mp x.property Q
        rw [Finsupp.add_apply,
          placeDivisor_apply_of_ne P Q (Ne.symm hQP), add_zero] at hxQ
        exact hxQ
  · intro hxG
    by_cases hx : (x : F) = 0
    · have hvalue : riemannRochPlaceLeadingCoefficientValue G P x = 0 := by
        apply Subtype.ext
        change Differential.localParameterPower P (G P + 1) * (x : F) = 0
        rw [hx, mul_zero]
      rw [hvalue]
      exact (IsLocalRing.maximalIdeal P.valuationRing).zero_mem
    · have hxOrder :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp hxG P
      let pi : P.valuationRing := P.uniformizerInValuationRing
      let t : F := Differential.localParameterPower P (G P + 1)
      let q : F := t * (x : F) * (pi : F)⁻¹
      have ht_ne : t ≠ 0 := localParameterPower_ne_zero P (G P + 1)
      have hpi_ne : (pi : F) ≠ 0 := by
        change P.uniformizer ≠ 0
        exact P.valuation.ne_zero_iff.mp (by
          rw [P.valuation_uniformizer]
          exact WithZero.exp_ne_zero)
      have hq_ne : q ≠ 0 :=
        mul_ne_zero (mul_ne_zero ht_ne hx) (inv_ne_zero hpi_ne)
      have hqOrder : 0 ≤ P.order q := by
        dsimp only [q]
        rw [order_mul P (mul_ne_zero ht_ne hx) (inv_ne_zero hpi_ne),
          order_mul P ht_ne hx, order_inv,
          show P.order (pi : F) = 1 by
            change P.order P.uniformizer = 1
            exact P.order_uniformizer,
          show P.order t = G P + 1 by
            exact localParameterPower_order P (G P + 1)]
        omega
      have hqmem : q ∈ P.valuationRing :=
        (regularAt_iff_mem_valuationRing P _).mp
          ((regularAt_iff_order_nonnegative P hq_ne).mpr hqOrder)
      rw [P.maximalIdeal_eq_span_uniformizer]
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨⟨q, hqmem⟩, ?_⟩
      apply Subtype.ext
      change q * (pi : F) = t * (x : F)
      simp only [q]
      field_simp [hpi_ne]

end GlobalPlace

end QEC.Coding.AlgebraicGeometry
