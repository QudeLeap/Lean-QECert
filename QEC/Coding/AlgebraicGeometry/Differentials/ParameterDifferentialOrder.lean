import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.Residues.Local.LogarithmicResidue

/-!
# Differential orders at simple zeros and poles

The actual logarithmic residue detects the nonzero differential and its
order -1. This gives the local differential-coordinate calculation needed
when transporting the source's simple-pole quadratic equations.
-/

namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

noncomputable section

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]

theorem logarithmicDifferential_ne_zero_of_order_one_or_neg_one
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    Differential.logarithmicDifferential (k := k) f ≠ 0 := by
  intro hz
  have h := Differential.simplePoleResidue_logarithmicDifferential P f hf
  have hzero : Differential.logarithmicDifferentialAtSimplePole P f hf = 0 := Subtype.ext hz
  rw [hzero, map_zero] at h
  rcases horder with horder | horder <;> rw [horder] at h <;> norm_num at h

theorem logarithmicDifferential_order_of_order_one_or_neg_one
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    differentialOrder P (Differential.logarithmicDifferential (k := k) f)
      (logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder) = -1 := by
  let omega := Differential.logarithmicDifferential (k := k) f
  let homega := logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder
  have hsimple : omega ∈ Differential.simplePoleDifferentialLattice P :=
    Differential.logarithmicDifferential_isGlobalSimplePole f hf P
  have hres : Differential.simplePoleResidue P
      (Differential.logarithmicDifferentialAtSimplePole P f hf) ≠ 0 := by
    rw [Differential.simplePoleResidue_logarithmicDifferential]
    rcases horder with horder | horder <;> rw [horder] <;> norm_num
  have hnot : omega ∉ Differential.localDifferentialLattice P := by
    intro hreg
    exact hres (Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice P
      (Differential.logarithmicDifferentialAtSimplePole P f hf) hreg)
  have hge := (Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
    P omega homega).mp hsimple
  have hlt : ¬ 0 ≤ differentialOrder P omega homega := by
    intro hn
    exact hnot ((Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      P omega homega).mpr hn)
  change differentialOrder P omega homega = -1
  omega

/-- At a simple zero or pole, the order of the actual global differential
generator is determined by the derivative of that local parameter. -/
theorem differentialGenerator_order_of_order_one_or_neg_one
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    ∃ _hdf : functionFieldDerivation (k := k) f ≠ 0,
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero =
          P.order f - 1 - P.order (functionFieldDerivation (k := k) f) := by
  let omega := Differential.logarithmicDifferential (k := k) f
  let homega := logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder
  have hlog := logarithmicDifferential_order_of_order_one_or_neg_one P f hf horder
  have hc : functionFieldDifferentialCoordinate (k := k) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff omega).mpr homega
  have hcoord : functionFieldDifferentialCoordinate (k := k) omega =
      f⁻¹ * functionFieldDerivation (k := k) f := by
    dsimp only [omega]
    rw [Differential.logarithmicDifferential, map_smul,
      functionFieldDifferentialCoordinate_differential]
    rfl
  have hdf : functionFieldDerivation (k := k) f ≠ 0 := by
    intro hz
    exact hc (by rw [hcoord, hz, mul_zero])
  refine ⟨hdf, ?_⟩
  have hcutoff := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff (k := k) P
  change differentialOrder P omega homega = -1 at hlog
  rw [differentialOrder_eq_coordinate_sub_generatorOrder P omega homega hcutoff,
    hcoord, P.order_mul (inv_ne_zero hf) hdf, P.order_inv] at hlog
  have hone : P.order (1 : K) = 0 := by
    simpa using P.order_algebraMap (1 : k) one_ne_zero
  rw [differentialOrder_eq_coordinate_sub_generatorOrder P
    (functionFieldDifferentialGenerator (k := k) (F := K))
    functionFieldDifferentialGenerator_ne_zero hcutoff,
    functionFieldDifferentialCoordinate_generator, hone]
  omega

variable {L : Type*} [Field L] [Algebra k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower (RatFunc k) K L]

omit [Finite k] in
/-- Uniqueness of separable derivation extension makes the ordinary
function-field derivations commute with any compatible field inclusion. -/
theorem functionFieldDerivation_algebraMap (x : K) :
    functionFieldDerivation (k := k) (F := L) (algebraMap K L x) =
      algebraMap K L (functionFieldDerivation (k := k) (F := K) x) := by
  let Du := functionFieldDerivation (k := k) (F := L)
  let Dl := functionFieldDerivation (k := k) (F := K)
  let Dr : Derivation k K L := Du.compAlgebraMap K
  let Dt : Derivation k K L := (Algebra.ofId K L).toLinearMap.compDer Dl
  have h : Dr = Dt := by
    apply SeparableDerivationExtension.extension_unique
    apply (RatFuncDerivation.rationalDerivationEquiv (k := k) (M := L)).injective
    change Du (algebraMap K L (algebraMap (RatFunc k) K RatFunc.X)) =
      algebraMap K L (Dl (algebraMap (RatFunc k) K RatFunc.X))
    rw [← IsScalarTower.algebraMap_apply (RatFunc k) K L]
    rw [functionFieldDerivation_apply_X, functionFieldDerivation_apply_X, map_one]
  exact Derivation.congr_fun h x

end

end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
