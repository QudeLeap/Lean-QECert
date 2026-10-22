import QEC.Coding.AlgebraicGeometry.Residues.Global.FunctionFieldGlobalResidue
import QEC.Coding.AlgebraicGeometry.Adeles.AdeleWeilDifferential
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Residues of intrinsic adeles against a differential

For a fixed nonzero function-field differential `omega`, this file considers
the intrinsic adeles `a` for which every local product `a_P omega` has at most
a simple pole.  The traced local residues have finite support and sum to a
constant-field linear functional on that submodule.  It vanishes both on the
divisor filtration `A((omega))` and on every diagonal element which belongs to
the simple-pole submodule.

This is the compatibility datum needed to extend the residue sum to an
adelic Weil differential.  The extension, maximal vanishing, canonical
duality, canonical degree, and Riemann--Roch are not asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Filter
open scoped BigOperators Polynomial RatFunc WithZero

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance globalAdeleDifferentialResidueAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance globalAdeleDifferentialResidueScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

variable [IsFullConstantField k F]

/-- Intrinsic adeles whose local product with `omega` has at most a simple
pole at every actual global place. -/
def globalAdeleSimplePoleSubmodule (omega : Differential k F) :
    Submodule k (GlobalAdele (k := k) (F := F)) where
  carrier := {a | ∀ P : GlobalPlace k F,
    a.val P • omega ∈ Differential.simplePoleDifferentialLattice P}
  zero_mem' := by
    intro P
    change (0 : F) • omega ∈ Differential.simplePoleDifferentialLattice P
    rw [zero_smul]
    exact (Differential.simplePoleDifferentialLattice P).zero_mem
  add_mem' {a b} ha hb := by
    intro P
    change (a.val P + b.val P) • omega ∈
      Differential.simplePoleDifferentialLattice P
    rw [add_smul]
    exact (Differential.simplePoleDifferentialLattice P).add_mem (ha P) (hb P)
  smul_mem' c a ha := by
    intro P
    let cP : P.valuationRing := constantsToValuationRing P c
    have h := (Differential.simplePoleDifferentialLattice P).smul_mem cP (ha P)
    have h' : (algebraMap k F c * a.val P) • omega ∈
        Differential.simplePoleDifferentialLattice P := by
      rw [mul_smul]
      exact h
    change (c • a.val P) • omega ∈ Differential.simplePoleDifferentialLattice P
    simpa only [Algebra.smul_def] using h'

private theorem globalAdeleExceptionalFinite
    (a : GlobalAdele (k := k) (F := F)) :
    {P : GlobalPlace k F | ¬P.valuation (a.val P) ≤ 1}.Finite :=
  (Filter.eventually_cofinite.mp a.property).subset (by
    intro P hP
    change a.val P ∉ P.valuationRing
    rw [mem_valuationRing_iff]
    exact hP)

private noncomputable def globalAdeleSimplePoleResidueCoefficient
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega)
    (P : GlobalPlace k F) : k :=
  Differential.simplePoleTraceResidue (k := k) (F := F) P
    (((a : GlobalAdele (k := k) (F := F)).val P) • omega) (a.property P)

private theorem globalAdeleSimplePoleResidueCoefficient_support_finite
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    (Function.support fun P : GlobalPlace k F =>
      globalAdeleSimplePoleResidueCoefficient
        (k := k) (F := F) omega homega a P).Finite := by
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  refine ((globalAdeleExceptionalFinite
    (k := k) (F := F) (a : GlobalAdele (k := k) (F := F))).union
      K.support.finite_toSet).subset ?_
  intro P hcoefficient
  by_contra houtside
  have haIntegral :
      P.valuation ((a : GlobalAdele (k := k) (F := F)).val P) ≤ 1 := by
    by_contra hnot
    exact houtside (Set.mem_union_left _ hnot)
  have hKnot : P ∉ K.support := by
    intro hP
    exact houtside (Set.mem_union_right _ hP)
  have hKzero : K P = 0 := by
    by_contra hne
    exact hKnot (Finsupp.mem_support_iff.mpr hne)
  have homegaRegular :
      omega ∈ Differential.localDifferentialLattice P := by
    apply (Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := F) P omega homega).mpr
    have horder : FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) P omega homega = 0 := by
      simpa only [K,
        FunctionFieldDifferential.differentialDivisor_apply] using hKzero
    rw [horder]
  let aP : P.valuationRing :=
    ⟨(a : GlobalAdele (k := k) (F := F)).val P,
      (mem_valuationRing_iff P _).mpr haIntegral⟩
  have hproductRegular :
      ((a : GlobalAdele (k := k) (F := F)).val P) • omega ∈
        Differential.localDifferentialLattice P := by
    have h := (Differential.localDifferentialLattice P).smul_mem
      aP homegaRegular
    exact h
  apply hcoefficient
  exact Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) P _ (a.property P) hproductRegular

private noncomputable def globalAdeleSimplePoleResidue
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    GlobalPlace k F →₀ k :=
  Finsupp.ofSupportFinite
    (globalAdeleSimplePoleResidueCoefficient
      (k := k) (F := F) omega homega a)
    (globalAdeleSimplePoleResidueCoefficient_support_finite
      (k := k) (F := F) omega homega a)

private theorem simplePoleTraceResidue_algebraMap_smul
    (P : GlobalPlace k F) (c : k) (eta : Differential k F)
    (heta : eta ∈ Differential.simplePoleDifferentialLattice P)
    (hscaled : (algebraMap k F c) • eta ∈
      Differential.simplePoleDifferentialLattice P) :
    Differential.simplePoleTraceResidue (k := k) (F := F) P
        ((algebraMap k F c) • eta) hscaled =
      c • Differential.simplePoleTraceResidue
        (k := k) (F := F) P eta heta := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional P
  let cP : P.valuationRing := constantsToValuationRing P c
  have hsubtype :
      (⟨(algebraMap k F c) • eta, hscaled⟩ :
          Differential.simplePoleDifferentialLattice P) =
        cP • ⟨eta, heta⟩ := by
    apply Subtype.ext
    rfl
  change Algebra.trace k P.residueField
      (Differential.simplePoleResidue (k := k) (F := F) P
        ⟨(algebraMap k F c) • eta, hscaled⟩) = _
  rw [hsubtype,
    Differential.simplePoleResidue_smul (k := k) (F := F)]
  change Algebra.trace k P.residueField
      (algebraMap k P.residueField c *
        Differential.simplePoleResidue (k := k) (F := F) P ⟨eta, heta⟩) = _
  rw [← Algebra.smul_def, map_smul]
  rfl

private theorem simplePoleTraceResidue_congr
    (P : GlobalPlace k F) {eta theta : Differential k F}
    (heta : eta ∈ Differential.simplePoleDifferentialLattice P)
    (htheta : theta ∈ Differential.simplePoleDifferentialLattice P)
    (h : eta = theta) :
    Differential.simplePoleTraceResidue (k := k) (F := F) P eta heta =
      Differential.simplePoleTraceResidue (k := k) (F := F) P theta htheta := by
  subst theta
  rfl

private theorem globalAdeleSimplePoleResidue_add
    (omega : Differential k F) (homega : omega ≠ 0)
    (a b : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidue (k := k) (F := F) omega homega (a + b) =
      globalAdeleSimplePoleResidue (k := k) (F := F) omega homega a +
        globalAdeleSimplePoleResidue (k := k) (F := F) omega homega b := by
  ext P
  change Differential.simplePoleTraceResidue (k := k) (F := F) P
      ((((a : GlobalAdele (k := k) (F := F)).val P +
        (b : GlobalAdele (k := k) (F := F)).val P) • omega)) _ =
    Differential.simplePoleTraceResidue (k := k) (F := F) P
        (((a : GlobalAdele (k := k) (F := F)).val P) • omega) (a.property P) +
      Differential.simplePoleTraceResidue (k := k) (F := F) P
        (((b : GlobalAdele (k := k) (F := F)).val P) • omega) (b.property P)
  calc
    _ = Differential.simplePoleTraceResidue (k := k) (F := F) P
        ((((a : GlobalAdele (k := k) (F := F)).val P) • omega) +
          (((b : GlobalAdele (k := k) (F := F)).val P) • omega))
        ((Differential.simplePoleDifferentialLattice P).add_mem
          (a.property P) (b.property P)) := by
      apply simplePoleTraceResidue_congr (k := k) (F := F) P
      exact add_smul _ _ _
    _ = _ := Differential.simplePoleTraceResidue_add
      (k := k) (F := F) P _ _ (a.property P) (b.property P)

private theorem globalAdeleSimplePoleResidue_smul
    (omega : Differential k F) (homega : omega ≠ 0) (c : k)
    (a : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidue (k := k) (F := F) omega homega (c • a) =
      c • globalAdeleSimplePoleResidue
        (k := k) (F := F) omega homega a := by
  ext P
  let eta : Differential k F :=
    ((a : GlobalAdele (k := k) (F := F)).val P) • omega
  have heta : eta ∈ Differential.simplePoleDifferentialLattice P := by
    simpa only [eta] using a.property P
  have hraw :
      ((algebraMap k F c *
        (a : GlobalAdele (k := k) (F := F)).val P) • omega) ∈
        Differential.simplePoleDifferentialLattice P := by
    have hmem := (c • a).property P
    change (c • (a : GlobalAdele (k := k) (F := F)).val P) • omega ∈
      Differential.simplePoleDifferentialLattice P at hmem
    simpa only [Algebra.smul_def] using hmem
  have hscaled :
      (algebraMap k F c) • eta ∈
        Differential.simplePoleDifferentialLattice P := by
    change (algebraMap k F c) •
      (((a : GlobalAdele (k := k) (F := F)).val P) • omega) ∈
        Differential.simplePoleDifferentialLattice P
    rw [← mul_smul]
    exact hraw
  have heq :
      (algebraMap k F c *
        (a : GlobalAdele (k := k) (F := F)).val P) • omega =
        (algebraMap k F c) • eta := by
    change (algebraMap k F c *
      (a : GlobalAdele (k := k) (F := F)).val P) • omega =
        (algebraMap k F c) •
          ((a : GlobalAdele (k := k) (F := F)).val P) • omega
    exact mul_smul _ _ _
  change Differential.simplePoleTraceResidue (k := k) (F := F) P
      ((algebraMap k F c *
        (a : GlobalAdele (k := k) (F := F)).val P) • omega) hraw =
    c • Differential.simplePoleTraceResidue (k := k) (F := F) P
      eta heta
  calc
    _ = Differential.simplePoleTraceResidue (k := k) (F := F) P
        ((algebraMap k F c) • eta) hscaled :=
      simplePoleTraceResidue_congr (k := k) (F := F) P hraw hscaled heq
    _ = _ := simplePoleTraceResidue_algebraMap_smul
      (k := k) (F := F) P c eta heta hscaled

/-- The finite sum of traced local residues is a constant-field linear
functional on the simple-pole adele submodule. -/
noncomputable def globalAdeleSimplePoleResidueSum
    (omega : Differential k F) (homega : omega ≠ 0) :
    globalAdeleSimplePoleSubmodule (k := k) (F := F) omega →ₗ[k] k where
  toFun a := (globalAdeleSimplePoleResidue
    (k := k) (F := F) omega homega a).sum (fun _ residue => residue)
  map_add' a b := by
    rw [globalAdeleSimplePoleResidue_add]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  map_smul' c a := by
    rw [globalAdeleSimplePoleResidue_smul,
      Finsupp.sum_smul_index (fun _ => rfl),
      ← Finsupp.mul_sum]
    rfl

private theorem globalAdeleFilter_product_mem_localDifferentialLattice
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega))
    (P : GlobalPlace k F) :
    ((a : GlobalAdele (k := k) (F := F)).val P) • omega ∈
      Differential.localDifferentialLattice P := by
  by_cases haP : (a : GlobalAdele (k := k) (F := F)).val P = 0
  · rw [haP, zero_smul]
    exact (Differential.localDifferentialLattice P).zero_mem
  · apply (Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
      (k := k) (F := F) P _ haP omega homega).mpr
    have hlog : WithZero.log
        (P.valuation ((a : GlobalAdele (k := k) (F := F)).val P)) ≤
      FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega P :=
      (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr haP)).mpr
        (a.property P)
    rw [FunctionFieldDifferential.differentialDivisor_apply] at hlog
    change 0 ≤ -WithZero.log
      (P.valuation ((a : GlobalAdele (k := k) (F := F)).val P)) +
        FunctionFieldDifferential.differentialOrder
          (k := k) (F := F) P omega homega
    omega

/-- The divisor filtration of a nonzero differential consists of adeles whose
local products with that differential are regular, hence in particular have
at most simple poles. -/
theorem globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
    (omega : Differential k F) (homega : omega ≠ 0) :
    globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega) ≤
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega := by
  intro a ha P
  exact Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
    P (globalAdeleFilter_product_mem_localDifferentialLattice
      (k := k) (F := F) omega homega ⟨a, ha⟩ P)

/-- Enlarging the differential divisor at one place still gives at most a
simple pole after local multiplication. -/
theorem globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
    (omega : Differential k F) (homega : omega ≠ 0)
    (P : GlobalPlace k F) :
    globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) ≤
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega := by
  intro a ha Q
  by_cases haQ : a.val Q = 0
  · rw [haQ, zero_smul]
    exact (Differential.simplePoleDifferentialLattice Q).zero_mem
  · apply (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
      (k := k) (F := F) Q _ haQ omega homega).mpr
    have hlog : WithZero.log (Q.valuation (a.val Q)) ≤
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) Q :=
      (WithZero.log_le_iff_le_exp ((Q.valuation).ne_zero_iff.mpr haQ)).mpr
        (ha Q)
    rw [Finsupp.add_apply,
      FunctionFieldDifferential.differentialDivisor_apply] at hlog
    change -1 ≤ -WithZero.log (Q.valuation (a.val Q)) +
      FunctionFieldDifferential.differentialOrder
        (k := k) (F := F) Q omega homega
    by_cases hQP : Q = P
    · subst Q
      rw [placeDivisor_apply] at hlog
      omega
    · rw [placeDivisor_apply_of_ne P Q (Ne.symm hQP)] at hlog
      omega

/-- The traced residue sum vanishes on `A((omega))`, because every local
product is regular. -/
theorem globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega)) :
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
          (k := k) (F := F) omega homega a.property⟩ = 0 := by
  change (globalAdeleSimplePoleResidue (k := k) (F := F) omega homega
    ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
      (k := k) (F := F) omega homega a.property⟩).sum
      (fun _ residue => residue) = 0
  have hfamily : globalAdeleSimplePoleResidue
      (k := k) (F := F) omega homega
      ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega a.property⟩ = 0 := by
    ext P
    exact Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P _ _
        (globalAdeleFilter_product_mem_localDifferentialLattice
          (k := k) (F := F) omega homega a P)
  rw [hfamily]
  exact Finsupp.sum_zero_index

/-- A diagonal element in the simple-pole adele submodule has residue sum
zero by the global residue theorem for the corresponding global
differential. -/
theorem globalAdeleSimplePoleResidueSum_diagonal_eq_zero
    (omega : Differential k F) (homega : omega ≠ 0) (f : F)
    (hf : diagonalAdele (k := k) (F := F) f ∈
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨diagonalAdele (k := k) (F := F) f, hf⟩ = 0 := by
  let hglobal : Differential.IsGlobalSimplePole
      (k := k) (F := F) (f • omega) := fun P => by
    exact hf P
  have hfamily : globalAdeleSimplePoleResidue
      (k := k) (F := F) omega homega
      ⟨diagonalAdele (k := k) (F := F) f, hf⟩ =
        Differential.globalSimplePoleResidue
          (k := k) (F := F) (f • omega) hglobal := by
    ext P
    rfl
  change (globalAdeleSimplePoleResidue (k := k) (F := F) omega homega
    ⟨diagonalAdele (k := k) (F := F) f, hf⟩).sum
      (fun _ residue => residue) = 0
  rw [hfamily]
  exact Differential.globalSimplePoleResidueSum_eq_zero
    (k := k) (F := F) (f • omega) hglobal

/-- On the one-place enlargement of the divisor of a nonzero differential,
the traced residue sum assumes every constant-field value. -/
theorem globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
    (omega : Differential k F) (homega : omega ≠ 0)
    (P : GlobalPlace k F) :
    Function.Surjective fun a : globalAdeleFilter (k := k) (F := F)
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega + placeDivisor P) =>
      globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨(a : GlobalAdele (k := k) (F := F)),
          globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
            (k := k) (F := F) omega homega P a.property⟩ := by
  classical
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  intro c
  by_cases hc : c = 0
  · subst c
    refine ⟨(0 : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega + placeDivisor P)), ?_⟩
    exact (globalAdeleSimplePoleResidueSum
      (k := k) (F := F) omega homega).map_zero
  · letI : Algebra k P.residueField := residueAlgebra P
    letI : FiniteDimensional k P.residueField :=
      residueField_finiteDimensional P
    obtain ⟨z, hz⟩ := (Algebra.trace_surjective k P.residueField) c
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective z
    let eta : Differential.simplePoleDifferentialLattice P :=
      r • Differential.uniformizerLogDifferential (k := k) (F := F) P
    have hetaResidue :
        Differential.simplePoleResidue (k := k) (F := F) P eta = z := by
      change Differential.simplePoleResidue (k := k) (F := F) P
        (r • Differential.uniformizerLogDifferential (k := k) (F := F) P) = z
      rw [Differential.simplePoleResidue_smul,
        Differential.simplePoleResidue_uniformizerLogDifferential, mul_one]
      change IsLocalRing.residue P.valuationRing r = z
      exact hr
    have hetaTrace :
        Differential.simplePoleTraceResidue (k := k) (F := F) P
          (eta : Differential k F) eta.property = c := by
      change Algebra.trace k P.residueField
        (Differential.simplePoleResidue (k := k) (F := F) P eta) = c
      rw [hetaResidue, hz]
    have hetaNe : (eta : Differential k F) ≠ 0 := by
      intro hetaZero
      have htraceZero := simplePoleTraceResidue_congr
        (k := k) (F := F) P eta.property
          (Differential.simplePoleDifferentialLattice P).zero_mem hetaZero
      rw [hetaTrace,
        Differential.simplePoleTraceResidue_zero (k := k) (F := F) P] at htraceZero
      exact hc htraceZero
    let C : Differential k F →ₗ[F] F :=
      FunctionFieldDifferential.functionFieldDifferentialCoordinate
        (k := k) (F := F)
    have hComega : C omega ≠ 0 :=
      (FunctionFieldDifferential.functionFieldDifferentialCoordinate_ne_zero_iff
        (k := k) (F := F) omega).mpr homega
    have hCeta : C (eta : Differential k F) ≠ 0 :=
      (FunctionFieldDifferential.functionFieldDifferentialCoordinate_ne_zero_iff
        (k := k) (F := F) (eta : Differential k F)).mpr hetaNe
    let f : F := C (eta : Differential k F) / C omega
    have hf : f ≠ 0 := div_ne_zero hCeta hComega
    have hfomega : f • omega = (eta : Differential k F) := by
      apply (FunctionFieldDifferential.functionFieldDifferentialEquiv
        (k := k) (F := F)).injective
      change C (f • omega) = C (eta : Differential k F)
      rw [map_smul]
      change (C (eta : Differential k F) / C omega) * C omega =
        C (eta : Differential k F)
      exact div_mul_cancel₀ _ hComega
    have hfSimple : f • omega ∈
        Differential.simplePoleDifferentialLattice P := by
      rw [hfomega]
      exact eta.property
    have horder :=
      (Differential.smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
        (k := k) (F := F) P f hf omega homega).mp hfSimple
    let a₀ : GlobalAdele (k := k) (F := F) :=
      globalAdeleUpdate (k := k) (F := F)
        (zeroGlobalAdele (k := k) (F := F)) P f
    have ha₀ : a₀ ∈ globalAdeleFilter (k := k) (F := F)
        (K + placeDivisor P) := by
      intro Q
      by_cases hQP : Q = P
      · subst Q
        have hlog : WithZero.log (P.valuation f) ≤
            FunctionFieldDifferential.differentialOrder
              (k := k) (F := F) P omega homega + 1 := by
          change -1 ≤ -WithZero.log (P.valuation f) +
            FunctionFieldDifferential.differentialOrder
              (k := k) (F := F) P omega homega at horder
          omega
        have hvaluation : P.valuation f ≤ WithZero.exp
            (FunctionFieldDifferential.differentialOrder
              (k := k) (F := F) P omega homega + 1) :=
          (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf)).mp hlog
        simpa only [a₀, globalAdeleUpdate, Function.update_self, K,
          Finsupp.add_apply,
          FunctionFieldDifferential.differentialDivisor_apply,
          placeDivisor_apply] using hvaluation
      · have hzero : a₀.val Q = 0 := by
          simp only [a₀, globalAdeleUpdate, zeroGlobalAdele,
            Function.update_of_ne hQP, Pi.zero_apply]
        rw [hzero, map_zero]
        exact zero_le
    refine ⟨⟨a₀, ha₀⟩, ?_⟩
    let aSimple : globalAdeleSimplePoleSubmodule (k := k) (F := F) omega :=
      ⟨a₀,
        globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
          (k := k) (F := F) omega homega P ha₀⟩
    have hfamily : globalAdeleSimplePoleResidue
        (k := k) (F := F) omega homega aSimple = Finsupp.single P c := by
      ext Q
      by_cases hQP : Q = P
      · subst Q
        change Differential.simplePoleTraceResidue (k := k) (F := F) P
            (a₀.val P • omega) (aSimple.property P) =
          (Finsupp.single P c) P
        have haP : a₀.val P = f := by
          simp only [a₀, globalAdeleUpdate, Function.update_self]
        calc
          _ = Differential.simplePoleTraceResidue (k := k) (F := F) P
              (eta : Differential k F) eta.property := by
            apply simplePoleTraceResidue_congr (k := k) (F := F) P
            rw [haP]
            exact hfomega
          _ = c := hetaTrace
          _ = (Finsupp.single P c) P := by simp
      · change Differential.simplePoleTraceResidue (k := k) (F := F) Q
            (a₀.val Q • omega) (aSimple.property Q) =
          (Finsupp.single P c) Q
        have haQ : a₀.val Q = 0 := by
          simp only [a₀, globalAdeleUpdate, zeroGlobalAdele,
            Function.update_of_ne hQP, Pi.zero_apply]
        calc
          _ = Differential.simplePoleTraceResidue (k := k) (F := F) Q 0
              (Differential.simplePoleDifferentialLattice Q).zero_mem := by
            apply simplePoleTraceResidue_congr (k := k) (F := F) Q
            rw [haQ, zero_smul]
          _ = 0 := Differential.simplePoleTraceResidue_zero
            (k := k) (F := F) Q
          _ = (Finsupp.single P c) Q := by simp [hQP]
    change (globalAdeleSimplePoleResidue
      (k := k) (F := F) omega homega aSimple).sum
        (fun _ residue => residue) = c
    rw [hfamily]
    exact Finsupp.sum_single_index rfl

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry
