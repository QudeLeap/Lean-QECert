import QEC.Semantics.Channels.Core
import QEC.Semantics.Entropy.Purification
import QEC.Semantics.Channels.Kraus
import QEC.Semantics.Core.Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Thermal one-qubit encoding and decoding

This module formalizes the algebraic first part of the CLBT thermal-memory
argument.  A Pauli-like pair determines its logical qubit factor; the
factorization is derived from the two eigenspaces and is not supplied by the
caller.  The resulting tensor coordinates are then used to construct the
thermal encoding and decoding channels.
-/

noncomputable section

namespace QEC
namespace Semantics
namespace ThermalEncoding

open Classical
open scoped BigOperators ComplexOrder TensorProduct

variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

namespace DensityOperator

/-- Every spectral weight of a finite density operator is at most one. -/
theorem spectralEigenvalues_le_one (rho : DensityOperator H)
    (i : Fin (Module.finrank Complex H)) :
    rho.spectralEigenvalues i ≤ 1 := by
  rw [← rho.spectralEigenvalues_sum_eq_one]
  exact Finset.single_le_sum
    (fun j _ => rho.spectralEigenvalues_nonnegative j) (Finset.mem_univ i)

/-- A density operator lies below the identity in the positive-operator order. -/
theorem one_sub_toOperator_positive (rho : DensityOperator H) :
    LinearMap.IsPositive (1 - rho.toOperator) := by
  let b := rho.spectralEigenbasis
  have hid :
      (1 : Operator H) =
        ∑ i : Fin (Module.finrank Complex H),
          (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by
    change (LinearMap.id : Operator H) = _
    simpa using congrArg ContinuousLinearMap.toLinearMap
      (OrthonormalBasis.sum_rankOne_eq_id b).symm
  have hrho :
      rho.toOperator =
        ∑ i : Fin (Module.finrank Complex H),
          (rho.spectralEigenvalues i : Complex) •
            (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap := by
    ext x
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, b]
    apply Finset.sum_congr rfl
    intro i _
    change inner Complex (rho.positive.isSymmetric.eigenvectorBasis rfl i) x •
        rho.toOperator (rho.positive.isSymmetric.eigenvectorBasis rfl i) =
      (rho.positive.isSymmetric.eigenvalues rfl i : Complex) •
        (InnerProductSpace.rankOne Complex
          (rho.positive.isSymmetric.eigenvectorBasis rfl i)
          (rho.positive.isSymmetric.eigenvectorBasis rfl i)) x
    rw [rho.positive.isSymmetric.apply_eigenvectorBasis]
    simp only [InnerProductSpace.rankOne_apply, smul_smul]
    congr 1
    exact mul_comm _ _
  rw [hid, hrho, ← Finset.sum_sub_distrib]
  apply LinearMap.isPositive_sum Finset.univ
  intro i _
  have hcoeff : 0 ≤ (1 - rho.spectralEigenvalues i : Complex) := by
    exact_mod_cast sub_nonneg.mpr (spectralEigenvalues_le_one rho i)
  convert
    (InnerProductSpace.isPositive_rankOne_self (b i)).toLinearMap.smul_of_nonneg
      hcoeff using 1
  · simp [sub_smul]

end DensityOperator

/-- Tensoring finite positive operators preserves positivity. -/
theorem tensorMap_positive {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : Operator K)
    (hA : LinearMap.IsPositive A) (hB : LinearMap.IsPositive B) :
    LinearMap.IsPositive (TensorProduct.map A B) := by
  have hAc : (LinearMap.toContinuousLinearMap A).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  have hBc : (LinearMap.toContinuousLinearMap B).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff B).mpr hB
  obtain ⟨m, a, ha⟩ :=
    ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hAc
  obtain ⟨n, b, hb⟩ :=
    ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hBc
  have ha' : A = ∑ i : Fin m,
      (InnerProductSpace.rankOne Complex (a i) (a i)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap ha
  have hb' : B = ∑ j : Fin n,
      (InnerProductSpace.rankOne Complex (b j) (b j)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hb
  rw [ha', hb', DensityOperator.tensorMap_sum_sum]
  apply LinearMap.isPositive_sum Finset.univ
  intro i _
  apply LinearMap.isPositive_sum Finset.univ
  intro j _
  rw [DensityOperator.tensorMap_rankOne]
  exact (InnerProductSpace.isPositive_rankOne_self
    (a i ⊗ₜ[Complex] b j)).toLinearMap

/-- A positive operator below the identity has operator norm at most one. -/
theorem operatorNorm_le_one_of_positive_one_sub
    (A : Operator H) (hA : LinearMap.IsPositive A)
    (hIA : LinearMap.IsPositive (1 - A)) :
    ‖LinearMap.toContinuousLinearMap A‖ ≤ 1 := by
  let T := LinearMap.toContinuousLinearMap A
  have hTc : T.IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  calc
    ‖LinearMap.toContinuousLinearMap A‖ =
        ⨆ x : H, |T.rayleighQuotient x| := by
          exact T.norm_eq_iSup_rayleighQuotient hTc.isSymmetric
    _ ≤ 1 := by
      apply ciSup_le
      intro x
      by_cases hx : x = 0
      · simp [hx]
      have hdenom : 0 < ‖x‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hlower : 0 ≤ T.reApplyInnerSelf x :=
        hTc.re_inner_nonneg_left x
      have hupper : T.reApplyInnerSelf x ≤ ‖x‖ ^ 2 := by
        have h := hIA.re_inner_nonneg_left x
        change 0 ≤
          Complex.re (inner Complex (((1 - A) : Operator H) x) x) at h
        have happly : (((1 - A) : Operator H) x) = x - A x := by
          rfl
        rw [happly, inner_sub_left, Complex.sub_re] at h
        have hnorm : (inner Complex x x).re = ‖x‖ ^ 2 := by
          exact inner_self_eq_norm_sq (𝕜 := Complex) x
        rw [hnorm] at h
        change (inner Complex (A x) x).re ≤ ‖x‖ ^ 2
        exact sub_nonneg.mp h
      have hquotient :
          T.rayleighQuotient x =
            T.reApplyInnerSelf x / ‖x‖ ^ 2 := rfl
      have hq_nonneg : 0 ≤ T.rayleighQuotient x := by
        rw [hquotient]
        exact div_nonneg hlower hdenom.le
      have hq_le : T.rayleighQuotient x ≤ (1 : Real) := by
        rw [hquotient]
        exact (div_le_one hdenom).mpr hupper
      simpa [abs_of_nonneg hq_nonneg] using hq_le

/-- A density operator tensored with an identity remains a contraction. -/
theorem tensorDensityLeft_operatorNorm_le_one {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) :
    ‖LinearMap.toContinuousLinearMap
      (TensorProduct.map rho.toOperator (1 : Operator K))‖ ≤ 1 := by
  apply operatorNorm_le_one_of_positive_one_sub
  · exact tensorMap_positive rho.toOperator 1 rho.positive
      LinearMap.isPositive_one
  · have hpos := tensorMap_positive (1 - rho.toOperator) (1 : Operator K)
        (QEC.Semantics.ThermalEncoding.DensityOperator.one_sub_toOperator_positive rho)
        LinearMap.isPositive_one
    have heq :
        (1 : Operator (CompositeSystem H K)) -
            TensorProduct.map rho.toOperator (1 : Operator K) =
          TensorProduct.map (1 - rho.toOperator) (1 : Operator K) := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          simpa [TensorProduct.map_tmul] using
            (TensorProduct.sub_tmul x (rho.toOperator x) y).symm
      | add x y hx hy => simp [map_add, hx, hy]
    rw [heq]
    exact hpos

/-- Unitary conjugation does not increase the finite operator norm. -/
theorem conjOperator_operatorNorm_le {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (A : Operator H) :
    ‖LinearMap.toContinuousLinearMap (U.conjOperator A)‖ ≤
      ‖LinearMap.toContinuousLinearMap A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖U.conjOperator A x‖ ≤
    ‖LinearMap.toContinuousLinearMap A‖ * ‖x‖
  rw [UnitaryTransport.conjOperator_apply]
  calc
    ‖U (A (U.toLinearEquiv.symm x))‖ =
        ‖A (U.toLinearEquiv.symm x)‖ := by
          exact U.toLinearIsometryEquiv.norm_map _
    _ ≤ ‖LinearMap.toContinuousLinearMap A‖ *
        ‖U.toLinearEquiv.symm x‖ :=
      (LinearMap.toContinuousLinearMap A).le_opNorm _
    _ = ‖LinearMap.toContinuousLinearMap A‖ * ‖x‖ := by
      congr 1
      exact U.symm.toLinearIsometryEquiv.norm_map x

/-- Twice a density operator, tensored with an identity, has norm at most two. -/
theorem scaledTensorDensity_operatorNorm_le_two {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) :
    ‖LinearMap.toContinuousLinearMap
      (TensorProduct.map ((2 : Complex) • rho.toOperator)
        (1 : Operator K))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖TensorProduct.map ((2 : Complex) • rho.toOperator)
      (1 : Operator K) x‖ ≤ 2 * ‖x‖
  rw [TensorProduct.map_smul_left]
  change ‖(2 : Complex) •
      TensorProduct.map rho.toOperator (1 : Operator K) x‖ ≤ 2 * ‖x‖
  rw [norm_smul]
  norm_num
  calc
    ‖TensorProduct.map rho.toOperator (1 : Operator K) x‖ ≤
        ‖LinearMap.toContinuousLinearMap
          (TensorProduct.map rho.toOperator (1 : Operator K))‖ * ‖x‖ :=
      (LinearMap.toContinuousLinearMap
        (TensorProduct.map rho.toOperator (1 : Operator K))).le_opNorm x
    _ ≤ 1 * ‖x‖ := by
      gcongr
      exact tensorDensityLeft_operatorNorm_le_one rho
    _ = ‖x‖ := one_mul _

/-- The finite Boltzmann partition function for an explicitly enumerated spectrum. -/
def gibbsPartitionFunction {ι : Type} [Fintype ι]
    (beta : Real) (energy : ι → Real) : Real :=
  ∑ i, Real.exp (-beta * energy i)

theorem gibbsPartitionFunction_pos {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) :
    0 < gibbsPartitionFunction beta energy := by
  exact Finset.sum_pos' (fun i _ => (Real.exp_pos _).le)
    (by exact ⟨Classical.choice ‹Nonempty ι›, Finset.mem_univ _,
      Real.exp_pos _⟩)

/-- The normalized Boltzmann weight of one spectral label. -/
def gibbsProbability {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) (i : ι) : Real :=
  Real.exp (-beta * energy i) / gibbsPartitionFunction beta energy

theorem gibbsProbability_nonnegative {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) (i : ι) :
    0 ≤ gibbsProbability beta energy i :=
  div_nonneg (Real.exp_pos _).le (gibbsPartitionFunction_pos beta energy).le

theorem gibbsProbability_sum_eq_one {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) :
    (∑ i, gibbsProbability beta energy i) = 1 := by
  rw [show (∑ i, gibbsProbability beta energy i) =
      (∑ i, Real.exp (-beta * energy i)) /
        gibbsPartitionFunction beta energy by
    simp [gibbsProbability, Finset.sum_div]]
  exact div_self (gibbsPartitionFunction_pos beta energy).ne'

/-- The Gibbs density associated with a finite orthonormal eigenbasis and its energies. -/
def spectralGibbsDensity {ι : Type} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) :
    DensityOperator H where
  toOperator :=
    ∑ i, (gibbsProbability beta energy i : Complex) •
      (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap
  positive := by
    apply LinearMap.isPositive_sum Finset.univ
    intro i _
    exact (InnerProductSpace.isPositive_rankOne_self (b i)).toLinearMap.smul_of_nonneg
      (by exact_mod_cast gibbsProbability_nonnegative beta energy i)
  trace_one := by
    rw [map_sum]
    simp only [map_smul, InnerProductSpace.trace_rankOne]
    have hnorm (i : ι) : inner Complex (b i) (b i) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      norm_num
    simp_rw [hnorm]
    simp only [smul_eq_mul, mul_one]
    rw [← Complex.ofReal_sum]
    exact_mod_cast gibbsProbability_sum_eq_one beta energy

@[simp]
theorem spectralGibbsDensity_apply_basis {ι : Type} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) (i : ι) :
    (spectralGibbsDensity b energy beta).toOperator (b i) =
      (gibbsProbability beta energy i : Complex) • b i := by
  classical
  simp [spectralGibbsDensity, LinearMap.sum_apply,
    InnerProductSpace.rankOne_apply, b.inner_eq_ite]

theorem gibbsPartitionFunction_qubit_product {ι : Type} [Fintype ι]
    (beta : Real) (energy : ι → Real) :
    gibbsPartitionFunction beta (fun qi : Fin 2 × ι => energy qi.2) =
      2 * gibbsPartitionFunction beta energy := by
  unfold gibbsPartitionFunction
  rw [Fintype.sum_prod_type]
  simp

theorem gibbsProbability_qubit_product {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) (q : Fin 2) (i : ι) :
    gibbsProbability beta (fun qi : Fin 2 × ι => energy qi.2) (q, i) =
      (2 : Real)⁻¹ * gibbsProbability beta energy i := by
  rw [gibbsProbability, gibbsProbability,
    gibbsPartitionFunction_qubit_product]
  field_simp [gibbsPartitionFunction_pos beta energy |>.ne']

/-- Spectral Gibbs densities commute with a unitary change of eigenbasis. -/
theorem spectralGibbsDensity_map {ι K : Type}
    [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K)
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) :
    spectralGibbsDensity (b.map U.toLinearIsometryEquiv) energy beta =
      U.conjDensity (spectralGibbsDensity b energy beta) := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator]
  change
    (∑ i, (gibbsProbability beta energy i : Complex) •
      (InnerProductSpace.rankOne Complex
        ((b.map U.toLinearIsometryEquiv) i)
        ((b.map U.toLinearIsometryEquiv) i)).toLinearMap) =
      U.conjOperator
        (∑ i, (gibbsProbability beta energy i : Complex) •
          (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap)
  change _ = U.conjOperatorLinearMap
    (∑ i, (gibbsProbability beta energy i : Complex) •
      (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, UnitaryTransport.conjOperatorLinearMap_apply,
    QuditSubsystem.conjOperator_rankOne, OrthonormalBasis.map_apply]
  congr 1

/--
The input data for a Pauli-like logical pair.

Only the observable relations are fields.  In particular, no tensor
factorization, Hamiltonian product form, Gibbs product form, or channel is
stored here.
-/
structure PauliLikePair (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H] where
  x : Operator H
  z : Operator H
  x_symmetric : x.IsSymmetric
  z_symmetric : z.IsSymmetric
  x_sq : x * x = 1
  z_sq : z * z = 1
  anticommute : x * z = -(z * x)

namespace PauliLikePair

variable (P : PauliLikePair H)

/-- The auxiliary Hilbert space is the `+1` eigenspace of the derived `Z`. -/
abbrev AuxiliarySpace : Type :=
  Module.End.eigenspace P.z (1 : Complex)

/-- The complementary `-1` eigenspace of the derived `Z`. -/
abbrev NegativeSpace : Type :=
  Module.End.eigenspace P.z (-1 : Complex)

theorem x_apply_x (v : H) : P.x (P.x v) = v := by
  have h := congrArg (fun A : Operator H => A v) P.x_sq
  simpa [Module.End.mul_apply] using h

theorem z_apply_z (v : H) : P.z (P.z v) = v := by
  have h := congrArg (fun A : Operator H => A v) P.z_sq
  simpa [Module.End.mul_apply] using h

theorem z_x_anticommute : P.z * P.x = -(P.x * P.z) := by
  calc
    P.z * P.x = -(-(P.z * P.x)) := by simp
    _ = -(P.x * P.z) := by rw [P.anticommute]

theorem x_preserves_inner (v w : H) :
    inner Complex (P.x v) (P.x w) = inner Complex v w := by
  rw [P.x_symmetric v (P.x w), P.x_apply_x]

theorem auxiliary_mem_iff (v : H) :
    v ∈ Module.End.eigenspace P.z (1 : Complex) ↔ P.z v = v := by
  rw [Module.End.mem_eigenspace_iff]
  simp

theorem negative_mem_iff (v : H) :
    v ∈ Module.End.eigenspace P.z (-1 : Complex) ↔ P.z v = -v := by
  rw [Module.End.mem_eigenspace_iff]
  simp

/-- `X` exchanges the positive and negative `Z` eigenspaces. -/
noncomputable def xAuxToNegative : P.AuxiliarySpace →ₗ[Complex] P.NegativeSpace where
  toFun v := ⟨P.x v, by
    rw [P.negative_mem_iff]
    have hzx : P.z (P.x (v : H)) = -P.x (P.z (v : H)) := by
      simpa [Module.End.mul_apply] using
        congrArg (fun A : Operator H => A (v : H)) P.z_x_anticommute
    have hvz : P.z (v : H) = v :=
      (P.auxiliary_mem_iff (v : H)).1 v.property
    rw [hzx, hvz]⟩
  map_add' v w := by
    ext
    simp
  map_smul' c v := by
    ext
    simp

/-- `X`, restricted in the other direction, is the inverse exchange map. -/
noncomputable def xNegativeToAux : P.NegativeSpace →ₗ[Complex] P.AuxiliarySpace where
  toFun v := ⟨P.x v, by
    rw [P.auxiliary_mem_iff]
    have hzx : P.z (P.x (v : H)) = -P.x (P.z (v : H)) := by
      simpa [Module.End.mul_apply] using
        congrArg (fun A : Operator H => A (v : H)) P.z_x_anticommute
    have hvz : P.z (v : H) = -v :=
      (P.negative_mem_iff (v : H)).1 v.property
    rw [hzx, hvz]
    simp⟩
  map_add' v w := by
    ext
    simp
  map_smul' c v := by
    ext
    simp

/-- The eigenspace exchange induced by `X` is a linear equivalence. -/
noncomputable def xEigenspaceEquiv : P.AuxiliarySpace ≃ₗ[Complex] P.NegativeSpace where
  toLinearMap := P.xAuxToNegative
  invFun := P.xNegativeToAux
  left_inv v := by
    ext
    exact P.x_apply_x v
  right_inv v := by
    ext
    exact P.x_apply_x v

theorem positive_negative_disjoint :
    Disjoint (Module.End.eigenspace P.z (1 : Complex))
      (Module.End.eigenspace P.z (-1 : Complex)) := by
  rw [Submodule.disjoint_def]
  intro v hvpos hvneg
  have hpos : P.z v = v := P.auxiliary_mem_iff v |>.1 hvpos
  have hneg : P.z v = -v := P.negative_mem_iff v |>.1 hvneg
  have hvnegself : v = -v := hpos.symm.trans hneg
  have htwo : (2 : Complex) • v = 0 := by
    rw [two_smul]
    exact (congrArg (fun w : H => w + v) hvnegself).trans (neg_add_cancel v)
  have hv : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [hv]

theorem positive_negative_codisjoint :
    Codisjoint (Module.End.eigenspace P.z (1 : Complex))
      (Module.End.eigenspace P.z (-1 : Complex)) := by
  rw [codisjoint_iff_le_sup]
  intro v _
  let vp : H := (2 : Complex)⁻¹ • (v + P.z v)
  let vn : H := (2 : Complex)⁻¹ • (v - P.z v)
  have hvp : vp ∈ Module.End.eigenspace P.z (1 : Complex) := by
    rw [P.auxiliary_mem_iff]
    simp only [vp, map_smul, map_add, P.z_apply_z]
    module
  have hvn : vn ∈ Module.End.eigenspace P.z (-1 : Complex) := by
    rw [P.negative_mem_iff]
    simp only [vn, map_smul, map_sub, P.z_apply_z]
    module
  rw [Submodule.mem_sup']
  refine ⟨⟨vp, hvp⟩, ⟨vn, hvn⟩, ?_⟩
  dsimp [vp, vn]
  module

/-- The `±1` eigenspaces of a Pauli-like `Z` decompose the physical space. -/
theorem positive_negative_isCompl :
    IsCompl (Module.End.eigenspace P.z (1 : Complex))
      (Module.End.eigenspace P.z (-1 : Complex)) :=
  ⟨P.positive_negative_disjoint, P.positive_negative_codisjoint⟩

/-- Algebraic coordinates of a qubit tensor the positive `Z` eigenspace. -/
noncomputable def qubitAuxCoordinates :
    CompositeSystem Qubit.QubitSpace P.AuxiliarySpace ≃ₗ[Complex]
      P.AuxiliarySpace × P.AuxiliarySpace :=
  (TensorProduct.comm Complex Qubit.QubitSpace P.AuxiliarySpace).trans
    (((WithLp.linearEquiv 2 Complex (Fin 2 → Complex)).lTensor P.AuxiliarySpace).trans
      ((TensorProduct.piScalarRight Complex Complex P.AuxiliarySpace (Fin 2)).trans
        (LinearEquiv.finTwoArrow Complex P.AuxiliarySpace)))

/--
The derived logical-qubit factorization.

The first coordinate occupies the positive `Z` eigenspace and the second is
moved to the negative eigenspace by `X`.
-/
noncomputable def factorizationLinearEquiv :
    CompositeSystem Qubit.QubitSpace P.AuxiliarySpace ≃ₗ[Complex] H :=
  P.qubitAuxCoordinates |>.trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl Complex P.AuxiliarySpace)
      P.xEigenspaceEquiv).trans
        (Submodule.prodEquivOfIsCompl
          (Module.End.eigenspace P.z (1 : Complex))
          (Module.End.eigenspace P.z (-1 : Complex))
          P.positive_negative_isCompl))

theorem factorizationLinearEquiv_tmul
    (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.factorizationLinearEquiv (q ⊗ₜ[Complex] a) =
      q 0 • (a : H) + q 1 • P.x (a : H) := by
  simp [factorizationLinearEquiv, qubitAuxCoordinates,
    LinearEquiv.trans_apply, xEigenspaceEquiv, xAuxToNegative]

theorem inner_aux_x_aux_eq_zero (a b : P.AuxiliarySpace) :
    inner Complex (a : H) (P.x (b : H)) = 0 := by
  have ha : P.z (a : H) = a :=
    (P.auxiliary_mem_iff (a : H)).1 a.property
  have hxb : P.z (P.x (b : H)) = -P.x (b : H) := by
    exact (P.negative_mem_iff (P.x (b : H))).1
      (P.xAuxToNegative b).property
  have hneg :
      inner Complex (a : H) (P.x (b : H)) =
        -inner Complex (a : H) (P.x (b : H)) := by
    calc
      inner Complex (a : H) (P.x (b : H)) =
          inner Complex (P.z (a : H)) (P.x (b : H)) := by rw [ha]
      _ = inner Complex (a : H) (P.z (P.x (b : H))) :=
        P.z_symmetric (a : H) (P.x (b : H))
      _ = -inner Complex (a : H) (P.x (b : H)) := by
        rw [hxb, inner_neg_right]
  exact CharZero.eq_neg_self_iff.mp hneg

theorem inner_x_aux_aux_eq_zero (a b : P.AuxiliarySpace) :
    inner Complex (P.x (a : H)) (b : H) = 0 := by
  rw [← inner_conj_symm]
  simp [P.inner_aux_x_aux_eq_zero]

theorem factorizationLinearEquiv_tmul_inner
    (q r : Qubit.QubitSpace) (a b : P.AuxiliarySpace) :
    inner Complex
        (P.factorizationLinearEquiv (q ⊗ₜ[Complex] a))
        (P.factorizationLinearEquiv (r ⊗ₜ[Complex] b)) =
      inner Complex (q ⊗ₜ[Complex] a) (r ⊗ₜ[Complex] b) := by
  rw [P.factorizationLinearEquiv_tmul, P.factorizationLinearEquiv_tmul,
    TensorProduct.inner_tmul]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    P.inner_aux_x_aux_eq_zero, P.inner_x_aux_aux_eq_zero, mul_zero,
    add_zero, zero_add, P.x_preserves_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- The derived logical-qubit factorization preserves the Hilbert inner product. -/
theorem factorizationLinearEquiv_map_inner
    (v w : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    inner Complex (P.factorizationLinearEquiv v) (P.factorizationLinearEquiv w) =
      inner Complex v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => exact P.factorizationLinearEquiv_tmul_inner q r a b
      | add first second hfirst hsecond =>
          simp only [map_add, inner_add_right, hfirst, hsecond]
  | add first second hfirst hsecond =>
      simp only [map_add, inner_add_left, hfirst, hsecond]

/-- The Pauli-like pair canonically supplies the unitary qubit factorization. -/
noncomputable def factorization :
    UnitaryTransport
      (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) H where
  toLinearEquiv := P.factorizationLinearEquiv
  map_inner := P.factorizationLinearEquiv_map_inner

/-- Standard logical `X` on the derived qubit factor. -/
noncomputable def tensorPauliX :
    Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  TensorProduct.map Qubit.pauliX (1 : Operator P.AuxiliarySpace)

/-- Standard logical `Z` on the derived qubit factor. -/
noncomputable def tensorPauliZ :
    Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  TensorProduct.map Qubit.pauliZ (1 : Operator P.AuxiliarySpace)

@[simp]
theorem tensorPauliX_tmul (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.tensorPauliX (q ⊗ₜ[Complex] a) = Qubit.pauliX q ⊗ₜ[Complex] a := by
  simp [tensorPauliX]

@[simp]
theorem tensorPauliZ_tmul (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.tensorPauliZ (q ⊗ₜ[Complex] a) = Qubit.pauliZ q ⊗ₜ[Complex] a := by
  simp [tensorPauliZ]

theorem factorization_intertwines_x
    (v : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    P.factorization (P.tensorPauliX v) = P.x (P.factorization v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
      change P.factorizationLinearEquiv (P.tensorPauliX (q ⊗ₜ[Complex] a)) =
        P.x (P.factorizationLinearEquiv (q ⊗ₜ[Complex] a))
      rw [P.tensorPauliX_tmul, P.factorizationLinearEquiv_tmul,
        P.factorizationLinearEquiv_tmul]
      simp [Qubit.pauliX_apply, P.x_apply_x]
      module
  | add first second hfirst hsecond =>
      simp only [map_add, hfirst, hsecond]

theorem factorization_intertwines_z
    (v : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    P.factorization (P.tensorPauliZ v) = P.z (P.factorization v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
      change P.factorizationLinearEquiv (P.tensorPauliZ (q ⊗ₜ[Complex] a)) =
        P.z (P.factorizationLinearEquiv (q ⊗ₜ[Complex] a))
      rw [P.tensorPauliZ_tmul, P.factorizationLinearEquiv_tmul,
        P.factorizationLinearEquiv_tmul]
      have ha : P.z (a : H) = a :=
        (P.auxiliary_mem_iff (a : H)).1 a.property
      have hxa : P.z (P.x (a : H)) = -P.x (a : H) :=
        (P.negative_mem_iff (P.x (a : H))).1 (P.xAuxToNegative a).property
      simp [Qubit.pauliZ_apply, Qubit.zPhase, ha, hxa]
  | add first second hfirst hsecond =>
      simp only [map_add, hfirst, hsecond]

theorem conj_tensorPauliX :
    P.factorization.conjOperator P.tensorPauliX = P.x := by
  apply LinearMap.ext
  intro h
  rw [UnitaryTransport.conjOperator_apply]
  exact (P.factorization_intertwines_x
    (P.factorization.toLinearEquiv.symm h)).trans
      (congrArg P.x (P.factorization.toLinearEquiv.apply_symm_apply h))

theorem conj_tensorPauliZ :
    P.factorization.conjOperator P.tensorPauliZ = P.z := by
  apply LinearMap.ext
  intro h
  rw [UnitaryTransport.conjOperator_apply]
  exact (P.factorization_intertwines_z
    (P.factorization.toLinearEquiv.symm h)).trans
      (congrArg P.z (P.factorization.toLinearEquiv.apply_symm_apply h))

/--
The auxiliary action of an operator commuting with the Pauli-like `Z`.

Preservation of the `+1` eigenspace is proved from commutation rather than
accepted as data.
-/
noncomputable def auxiliaryOperator (A : Operator H) (hZ : Commute A P.z) :
    Operator P.AuxiliarySpace where
  toFun a := ⟨A a, by
    rw [P.auxiliary_mem_iff]
    have hcomm : P.z (A (a : H)) = A (P.z (a : H)) := by
      simpa [Module.End.mul_apply] using
        congrArg (fun T : Operator H => T (a : H)) hZ.eq.symm
    rw [hcomm, (P.auxiliary_mem_iff (a : H)).1 a.property]⟩
  map_add' a b := by
    ext
    simp
  map_smul' c a := by
    ext
    simp

/-- Identity on the derived qubit tensor the restricted auxiliary operator. -/
noncomputable def tensorAuxiliaryOperator (A : Operator H) (hZ : Commute A P.z) :
    Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  TensorProduct.map (1 : Operator Qubit.QubitSpace) (P.auxiliaryOperator A hZ)

@[simp]
theorem tensorAuxiliaryOperator_tmul
    (A : Operator H) (hZ : Commute A P.z)
    (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.tensorAuxiliaryOperator A hZ (q ⊗ₜ[Complex] a) =
      q ⊗ₜ[Complex] P.auxiliaryOperator A hZ a := by
  simp [tensorAuxiliaryOperator]

theorem factorization_intertwines_auxiliaryOperator
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z)
    (v : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    P.factorization (P.tensorAuxiliaryOperator A hZ v) =
      A (P.factorization v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
      change P.factorizationLinearEquiv
          (P.tensorAuxiliaryOperator A hZ (q ⊗ₜ[Complex] a)) =
        A (P.factorizationLinearEquiv (q ⊗ₜ[Complex] a))
      rw [P.tensorAuxiliaryOperator_tmul, P.factorizationLinearEquiv_tmul,
        P.factorizationLinearEquiv_tmul]
      have hcomm : A (P.x (a : H)) = P.x (A (a : H)) := by
        simpa [Module.End.mul_apply] using
          congrArg (fun T : Operator H => T (a : H)) hX.eq
      simp only [map_add, map_smul]
      rw [hcomm]
      rfl
  | add first second hfirst hsecond =>
      simp only [map_add, hfirst, hsecond]

/--
An operator commuting with both Pauli observables is `I_Q tensor A_aux` in
the factorization derived from those observables.
-/
theorem conj_tensorAuxiliaryOperator
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z) :
    P.factorization.conjOperator (P.tensorAuxiliaryOperator A hZ) = A := by
  apply LinearMap.ext
  intro h
  rw [UnitaryTransport.conjOperator_apply]
  exact (P.factorization_intertwines_auxiliaryOperator A hX hZ
    (P.factorization.toLinearEquiv.symm h)).trans
      (congrArg A (P.factorization.toLinearEquiv.apply_symm_apply h))

/-- Equivalent pulled-back Hamiltonian form used by the Gibbs calculation. -/
theorem symm_conjOperator_eq_tensorAuxiliaryOperator
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z) :
    P.factorization.symm.conjOperator A = P.tensorAuxiliaryOperator A hZ := by
  rw [← P.factorization.symm_conjOperator_conjOperator
    (P.tensorAuxiliaryOperator A hZ), P.conj_tensorAuxiliaryOperator A hX hZ]

end PauliLikePair

section Preparation

variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- Insert a fixed vector on the right tensor factor. -/
noncomputable def prepareRightBranch (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : K) : H →ₗ[Complex] CompositeSystem H K :=
  TensorProduct.mk Complex H K |>.flip v

@[simp]
theorem prepareRightBranch_apply (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : K) (h : H) :
    prepareRightBranch H K v h = h ⊗ₜ[Complex] v :=
  rfl

theorem adjoint_prepareRightBranch_comp (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : K) :
    (LinearMap.adjoint (prepareRightBranch H K v)).comp (prepareRightBranch H K v) =
      (inner Complex v v) • (1 : Operator H) := by
  apply LinearMap.ext
  intro h
  apply (ext_iff_inner_left Complex).mpr
  intro g
  change inner Complex g
      (LinearMap.adjoint (prepareRightBranch H K v)
        (prepareRightBranch H K v h)) =
    inner Complex g (((inner Complex v v) • (1 : Operator H)) h)
  rw [LinearMap.adjoint_inner_right]
  simp [prepareRightBranch, TensorProduct.inner_tmul, mul_comm]

/-- Spectral rank-one vectors of a density operator. -/
noncomputable def spectralEnsembleVector (sigma : DensityOperator K)
    (i : Fin (Module.finrank Complex K)) : K :=
  (Real.sqrt (sigma.spectralEigenvalues i) : Complex) • sigma.spectralEigenbasis i

theorem spectralEnsembleVector_sum_inner (sigma : DensityOperator K) :
    ∑ i, inner Complex (spectralEnsembleVector sigma i)
      (spectralEnsembleVector sigma i) = 1 := by
  have htrace := sigma.trace_one
  rw [sigma.spectralDecomposition] at htrace
  change (∑ i, inner Complex
    ((Real.sqrt (sigma.spectralEigenvalues i) : Complex) • sigma.spectralEigenbasis i)
    ((Real.sqrt (sigma.spectralEigenvalues i) : Complex) • sigma.spectralEigenbasis i)) = 1
  simpa only [map_sum, InnerProductSpace.trace_rankOne] using htrace

/-- Kraus family for tensoring an input with a fixed right-factor state. -/
noncomputable def prepareRightKraus (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) :
    FiniteKrausFamily (Fin (Module.finrank Complex K)) H (CompositeSystem H K) where
  operator i := prepareRightBranch H K (spectralEnsembleVector sigma i)

theorem prepareRightKraus_complete (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) :
    (prepareRightKraus H K sigma).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [prepareRightKraus, adjoint_prepareRightBranch_comp]
  apply LinearMap.ext
  intro h
  calc
    (∑ i, inner Complex (spectralEnsembleVector sigma i)
        (spectralEnsembleVector sigma i) • (1 : Operator H)) h =
      (∑ i, inner Complex (spectralEnsembleVector sigma i)
        (spectralEnsembleVector sigma i)) • h := by
          simp [Finset.sum_smul]
    _ = h := by rw [spectralEnsembleVector_sum_inner]; simp

/-- CPTP channel which tensors its input with a fixed right-factor state. -/
noncomputable def prepareRight (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) : QuantumChannel H (CompositeSystem H K) :=
  (prepareRightKraus H K sigma).toQuantumChannel
    (prepareRightKraus_complete H K sigma)

theorem prepareRight_apply_rankOne (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (h g : H) :
    prepareRight H K sigma (InnerProductSpace.rankOne Complex h g).toLinearMap =
      ∑ i, (InnerProductSpace.rankOne Complex
        (h ⊗ₜ[Complex] spectralEnsembleVector sigma i)
        (g ⊗ₜ[Complex] spectralEnsembleVector sigma i)).toLinearMap := by
  unfold prepareRight
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply LinearMap.ext
  intro x
  simp [prepareRightKraus, prepareRightBranch, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply, LinearMap.adjoint_inner_right]

private theorem tensorMap_sum_left {H K : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type} [Fintype ι] (A : ι → Operator H) (B : Operator K) :
    TensorProduct.map (∑ i, A i) B = ∑ i, TensorProduct.map (A i) B := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]

private theorem tensorMap_sum_right {H K : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type} [Fintype ι] (A : Operator H) (B : ι → Operator K) :
    TensorProduct.map A (∑ i, B i) = ∑ i, TensorProduct.map A (B i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_right, ih]

/-- The preparation channel is exactly right tensoring on operators. -/
theorem prepareRight_apply (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    prepareRight H K sigma A = TensorProduct.map A sigma.toOperator := by
  let basis := stdOrthonormalBasis Complex H
  rw [QuditSubsystem.operator_eq_sum_rankOne_basis H basis A, map_sum,
    tensorMap_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [prepareRight_apply_rankOne]
  calc
    (∑ j, (InnerProductSpace.rankOne Complex
      (A (basis i) ⊗ₜ[Complex] spectralEnsembleVector sigma j)
      (basis i ⊗ₜ[Complex] spectralEnsembleVector sigma j)).toLinearMap) =
        ∑ j, TensorProduct.map
          (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap
          (InnerProductSpace.rankOne Complex
            (spectralEnsembleVector sigma j)
            (spectralEnsembleVector sigma j)).toLinearMap := by
              apply Finset.sum_congr rfl
              intro j _
              rw [DensityOperator.tensorMap_rankOne]
    _ = TensorProduct.map
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap
        (∑ j, (InnerProductSpace.rankOne Complex
          (spectralEnsembleVector sigma j)
          (spectralEnsembleVector sigma j)).toLinearMap) := by
            rw [tensorMap_sum_right]
    _ = TensorProduct.map
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap
        sigma.toOperator := by
          rw [show (∑ j, (InnerProductSpace.rankOne Complex
            (spectralEnsembleVector sigma j)
            (spectralEnsembleVector sigma j)).toLinearMap) = sigma.toOperator by
              simpa only [spectralEnsembleVector] using sigma.spectralDecomposition.symm]

/-- Tracing out the prepared factor returns the original operator. -/
theorem partialTraceRightRaw_prepareRight (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    partialTraceRightRaw H K (prepareRight H K sigma A) = A := by
  let basis := stdOrthonormalBasis Complex H
  rw [QuditSubsystem.operator_eq_sum_rankOne_basis H basis A, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [prepareRight_apply_rankOne, map_sum]
  calc
    (∑ j, partialTraceRightRaw H K
      (InnerProductSpace.rankOne Complex
        (A (basis i) ⊗ₜ[Complex] spectralEnsembleVector sigma j)
        (basis i ⊗ₜ[Complex] spectralEnsembleVector sigma j)).toLinearMap) =
        ∑ j, inner Complex (spectralEnsembleVector sigma j)
          (spectralEnsembleVector sigma j) •
            (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
              apply Finset.sum_congr rfl
              intro j _
              rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    _ = (∑ j, inner Complex (spectralEnsembleVector sigma j)
          (spectralEnsembleVector sigma j)) •
            (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
              rw [Finset.sum_smul]
    _ = (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
          rw [spectralEnsembleVector_sum_inner]
          simp

end Preparation

namespace PauliLikePair

variable (P : PauliLikePair H)

/-- The maximally mixed state on the concrete one-qubit factor. -/
noncomputable def maximallyMixedQubit : DensityOperator Qubit.QubitSpace where
  toOperator := (2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace)
  positive := by
    have htwo : 0 ≤ (2 : Complex) := by
      exact_mod_cast (show (0 : Nat) ≤ 2 by norm_num)
    exact LinearMap.isPositive_one.smul_of_nonneg ((inv_nonneg).2 htwo)
  trace_one := by
    rw [map_smul, LinearMap.trace_one, finrank_euclideanSpace]
    norm_num

/-- A duplicated qubit spectrum produces the maximally mixed qubit tensor its Gibbs state. -/
theorem spectralGibbsDensity_qubit_product {ι : Type}
    [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex P.AuxiliarySpace)
    (energy : ι → Real) (beta : Real) :
    spectralGibbsDensity
        ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct b)
        (fun qi : Fin 2 × ι => energy qi.2) beta =
      DensityOperator.tensorDensity maximallyMixedQubit
        (spectralGibbsDensity b energy beta) := by
  apply DensityOperator.ext_toOperator
  apply LinearMap.ext
  intro x
  let tb := (EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct b
  conv_lhs => rw [← tb.sum_repr' x]
  conv_rhs => rw [← tb.sum_repr' x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  rintro ⟨q, i⟩ _
  rw [spectralGibbsDensity_apply_basis]
  congr 1
  simp only [tb, OrthonormalBasis.tensorProduct_apply]
  change
    (gibbsProbability beta (fun qi : Fin 2 × ι => energy qi.2) (q, i) :
      Complex) •
        ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i) =
    (DensityOperator.tensorDensity maximallyMixedQubit
      (spectralGibbsDensity b energy beta)).toOperator
      ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i)
  rw [DensityOperator.tensorDensity_toOperator, TensorProduct.map_tmul,
    spectralGibbsDensity_apply_basis]
  change _ =
    (((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
      (EuclideanSpace.basisFun (Fin 2) Complex q)) ⊗ₜ[Complex]
        ((gibbsProbability beta energy i : Complex) • b i)
  rw [LinearMap.smul_apply, Module.End.one_apply]
  have hprob := gibbsProbability_qubit_product beta energy q i
  have hprobC :
      (gibbsProbability beta
        (fun qi : Fin 2 × ι => energy qi.2) (q, i) : Complex) =
        (2 : Complex)⁻¹ * (gibbsProbability beta energy i : Complex) := by
    calc
      (gibbsProbability beta
          (fun qi : Fin 2 × ι => energy qi.2) (q, i) : Complex) =
          ((2 : Real)⁻¹ * gibbsProbability beta energy i : Real) := by
            exact congrArg (fun r : Real => (r : Complex)) hprob
      _ = (2 : Complex)⁻¹ *
          (gibbsProbability beta energy i : Complex) := by norm_num
  rw [hprobC]
  calc
    ((2 : Complex)⁻¹ * (gibbsProbability beta energy i : Complex)) •
          ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i) =
        (2 : Complex)⁻¹ •
          ((gibbsProbability beta energy i : Complex) •
            ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex] b i)) := by
          rw [smul_smul]
    _ = (2 : Complex)⁻¹ •
          ((EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex]
            ((gibbsProbability beta energy i : Complex) • b i)) := by
          rw [TensorProduct.tmul_smul]
    _ = (((2 : Complex)⁻¹ •
            EuclideanSpace.basisFun (Fin 2) Complex q) ⊗ₜ[Complex]
          ((gibbsProbability beta energy i : Complex) • b i)) := by
          rfl

/-- Restricting a symmetric Hamiltonian to the invariant auxiliary space is symmetric. -/
theorem auxiliaryOperator_symmetric
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    (P.auxiliaryOperator A hZ).IsSymmetric := by
  intro a b
  change inner Complex (A (a : H)) (b : H) =
    inner Complex (a : H) (A (b : H))
  exact hA (a : H) (b : H)

section Gibbs

variable [Nontrivial P.AuxiliarySpace]

local instance : Nonempty (Fin (Module.finrank Complex P.AuxiliarySpace)) :=
  Fin.pos_iff_nonempty.mp Module.finrank_pos

/-- Canonical eigenbasis of the Hamiltonian restricted to the auxiliary factor. -/
noncomputable def auxiliaryHamiltonianEigenbasis
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank Complex P.AuxiliarySpace))
      Complex P.AuxiliarySpace :=
  (P.auxiliaryOperator_symmetric A hZ hA).eigenvectorBasis rfl

/-- The real auxiliary energies paired with the canonical eigenbasis. -/
noncomputable def auxiliaryHamiltonianEnergies
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    Fin (Module.finrank Complex P.AuxiliarySpace) → Real :=
  (P.auxiliaryOperator_symmetric A hZ hA).eigenvalues rfl

/-- The normalized finite-temperature Gibbs density of the auxiliary Hamiltonian. -/
noncomputable def auxiliaryGibbsState
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) (beta : Real) :
    DensityOperator P.AuxiliarySpace :=
  spectralGibbsDensity
    (P.auxiliaryHamiltonianEigenbasis A hZ hA)
    (P.auxiliaryHamiltonianEnergies A hZ hA) beta

/-- Product eigenbasis for the pulled-back Hamiltonian `I_Q tensor H_A`. -/
noncomputable def tensorHamiltonianEigenbasis
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    OrthonormalBasis
      (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace))
      Complex (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  (EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
    (P.auxiliaryHamiltonianEigenbasis A hZ hA)

/-- Physical eigenbasis obtained from the derived qubit factorization. -/
noncomputable def physicalHamiltonianEigenbasis
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    OrthonormalBasis
      (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) Complex H :=
  (P.tensorHamiltonianEigenbasis A hZ hA).map
    P.factorization.toLinearIsometryEquiv

/-- The physical spectrum repeats each auxiliary energy twice. -/
noncomputable def physicalHamiltonianEnergies
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) → Real :=
  fun qi => P.auxiliaryHamiltonianEnergies A hZ hA qi.2

/-- Gibbs density defined spectrally from the physical Hamiltonian eigenbasis. -/
noncomputable def physicalGibbsState
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) (beta : Real) :
    DensityOperator H :=
  spectralGibbsDensity
    (P.physicalHamiltonianEigenbasis A hZ hA)
    (P.physicalHamiltonianEnergies A hZ hA) beta

omit [Nontrivial P.AuxiliarySpace] in
/--
The transported product basis is genuinely an eigenbasis of the physical
Hamiltonian; this connects the spectral Gibbs construction to `A`.
-/
theorem physicalHamiltonianEigenbasis_apply
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z)
    (hA : A.IsSymmetric)
    (qi : Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) :
    A (P.physicalHamiltonianEigenbasis A hZ hA qi) =
      (P.physicalHamiltonianEnergies A hZ hA qi : Complex) •
        P.physicalHamiltonianEigenbasis A hZ hA qi := by
  rcases qi with ⟨q, i⟩
  simp only [physicalHamiltonianEigenbasis, OrthonormalBasis.map_apply,
    tensorHamiltonianEigenbasis, OrthonormalBasis.tensorProduct_apply,
    physicalHamiltonianEnergies]
  calc
    A (P.factorization
        (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
          P.auxiliaryHamiltonianEigenbasis A hZ hA i)) =
      P.factorization
        (P.tensorAuxiliaryOperator A hZ
          (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
            P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        exact (P.factorization_intertwines_auxiliaryOperator A hX hZ _).symm
    _ = P.factorization
        (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
          P.auxiliaryOperator A hZ
            (P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        rw [P.tensorAuxiliaryOperator_tmul]
    _ = P.factorization
        (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
          ((P.auxiliaryHamiltonianEnergies A hZ hA i : Complex) •
            P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        rw [auxiliaryHamiltonianEigenbasis, auxiliaryHamiltonianEnergies,
          LinearMap.IsSymmetric.apply_eigenvectorBasis]
        rfl
    _ = P.factorization
        ((P.auxiliaryHamiltonianEnergies A hZ hA i : Complex) •
          (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
            P.auxiliaryHamiltonianEigenbasis A hZ hA i)) := by
        rw [TensorProduct.tmul_smul]
    _ = (P.auxiliaryHamiltonianEnergies A hZ hA i : Complex) •
        P.factorization
          (EuclideanSpace.basisFun (Fin 2) Complex q ⊗ₜ[Complex]
            P.auxiliaryHamiltonianEigenbasis A hZ hA i) := by
        exact map_smul P.factorization.toLinearEquiv _ _

end Gibbs

/-- Concrete thermal encoder: prepare the auxiliary state, then return to physical coordinates. -/
noncomputable def thermalEncoding (sigma : DensityOperator P.AuxiliarySpace) :
    QuantumChannel Qubit.QubitSpace H :=
  QuantumChannel.comp (QuantumChannel.unitaryConj P.factorization)
    (prepareRight Qubit.QubitSpace P.AuxiliarySpace sigma)

/-- Concrete thermal decoder: enter tensor coordinates, then trace out the auxiliary factor. -/
noncomputable def thermalDecoding :
    QuantumChannel H Qubit.QubitSpace :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp Qubit.QubitSpace P.AuxiliarySpace)
    (QuantumChannel.unitaryConj P.factorization.symm)

set_option maxRecDepth 4096 in
theorem thermalDecoding_thermalEncoding
    (sigma : DensityOperator P.AuxiliarySpace) (A : Operator Qubit.QubitSpace) :
    P.thermalDecoding (P.thermalEncoding sigma A) = A := by
  change partialTraceRightRaw Qubit.QubitSpace P.AuxiliarySpace
    (P.factorization.symm.conjOperator
      (P.factorization.conjOperator
        (prepareRight Qubit.QubitSpace P.AuxiliarySpace sigma A))) = A
  rw [P.factorization.symm_conjOperator_conjOperator,
    partialTraceRightRaw_prepareRight]

theorem thermalDecoding_thermalEncoding_density
    (sigma : DensityOperator P.AuxiliarySpace) (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalDecoding.mapDensity (P.thermalEncoding sigma |>.mapDensity eta) = eta := by
  apply DensityOperator.ext_toOperator
  exact P.thermalDecoding_thermalEncoding sigma eta.toOperator

/--
The physical thermal reference state associated with an auxiliary density.

For the auxiliary Gibbs density proved below, this is the normalized Gibbs
state of the commuting physical Hamiltonian.
-/
noncomputable def thermalReferenceState (sigma : DensityOperator P.AuxiliarySpace) :
    DensityOperator H :=
  P.factorization.conjDensity (DensityOperator.tensorDensity maximallyMixedQubit sigma)

/--
The Gibbs density of a Hamiltonian commuting with the derived Pauli pair
factors as the maximally mixed logical qubit tensor the auxiliary Gibbs
density.  Both the factorization and the auxiliary Hamiltonian are derived.
-/
theorem physicalGibbsState_eq_thermalReferenceState
    [Nontrivial P.AuxiliarySpace]
    (A : Operator H) (hZ : Commute A P.z)
    (hA : A.IsSymmetric) (beta : Real) :
    P.physicalGibbsState A hZ hA beta =
      P.thermalReferenceState (P.auxiliaryGibbsState A hZ hA beta) := by
  letI : Nonempty (Fin (Module.finrank Complex P.AuxiliarySpace)) :=
    Fin.pos_iff_nonempty.mp Module.finrank_pos
  letI : Nonempty
      (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) :=
    inferInstance
  change
    spectralGibbsDensity
        ((P.tensorHamiltonianEigenbasis A hZ hA).map
          P.factorization.toLinearIsometryEquiv)
        (fun qi : Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace) =>
          P.auxiliaryHamiltonianEnergies A hZ hA qi.2) beta =
      P.factorization.conjDensity
        (DensityOperator.tensorDensity maximallyMixedQubit
          (spectralGibbsDensity
            (P.auxiliaryHamiltonianEigenbasis A hZ hA)
            (P.auxiliaryHamiltonianEnergies A hZ hA) beta))
  rw [spectralGibbsDensity_map]
  congr 1
  simpa [tensorHamiltonianEigenbasis] using
    (P.spectralGibbsDensity_qubit_product
      (P.auxiliaryHamiltonianEigenbasis A hZ hA)
      (P.auxiliaryHamiltonianEnergies A hZ hA) beta)

/-- The lifted logical density used as CLBT's bounded operator `O`. -/
noncomputable def encodedObservable (eta : DensityOperator Qubit.QubitSpace) :
    Operator H :=
  P.factorization.conjOperator
    (TensorProduct.map ((2 : Complex) • eta.toOperator)
      (1 : Operator P.AuxiliarySpace))

/-- CLBT's encoded observable has the required uniform operator-norm bound. -/
theorem encodedObservable_operatorNorm_le_two
    (eta : DensityOperator Qubit.QubitSpace) :
    ‖LinearMap.toContinuousLinearMap (P.encodedObservable eta)‖ ≤ 2 := by
  exact
    (conjOperator_operatorNorm_le P.factorization
      (TensorProduct.map ((2 : Complex) • eta.toOperator)
        (1 : Operator P.AuxiliarySpace))).trans
      (scaledTensorDensity_operatorNorm_le_two eta)

theorem thermalEncoding_apply
    (sigma : DensityOperator P.AuxiliarySpace) (A : Operator Qubit.QubitSpace) :
    P.thermalEncoding sigma A =
      P.factorization.conjOperator (TensorProduct.map A sigma.toOperator) := by
  change P.factorization.conjOperator
    (prepareRight Qubit.QubitSpace P.AuxiliarySpace sigma A) = _
  rw [prepareRight_apply]

theorem thermalReferenceState_toOperator
    (sigma : DensityOperator P.AuxiliarySpace) :
    (P.thermalReferenceState sigma).toOperator =
      P.factorization.conjOperator
        (TensorProduct.map ((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
          sigma.toOperator) := by
  rfl

private theorem encoded_tensor_mul_reference
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    TensorProduct.map ((2 : Complex) • eta.toOperator)
        (1 : Operator P.AuxiliarySpace) *
      TensorProduct.map ((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
        sigma.toOperator =
      TensorProduct.map eta.toOperator sigma.toOperator := by
  rw [← TensorProduct.map_mul]
  congr 1
  · apply LinearMap.ext
    intro q
    simp

private theorem reference_tensor_mul_encoded
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    TensorProduct.map ((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
        sigma.toOperator *
      TensorProduct.map ((2 : Complex) • eta.toOperator)
        (1 : Operator P.AuxiliarySpace) =
      TensorProduct.map eta.toOperator sigma.toOperator := by
  rw [← TensorProduct.map_mul]
  congr 1
  · apply LinearMap.ext
    intro q
    simp

theorem thermalEncoding_eq_encodedObservable_mul
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalEncoding sigma eta.toOperator =
      P.encodedObservable eta * (P.thermalReferenceState sigma).toOperator := by
  rw [P.thermalEncoding_apply, encodedObservable,
    P.thermalReferenceState_toOperator, ← P.factorization.conjOperator_mul,
    encoded_tensor_mul_reference]

theorem thermalEncoding_eq_mul_encodedObservable
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalEncoding sigma eta.toOperator =
      (P.thermalReferenceState sigma).toOperator * P.encodedObservable eta := by
  rw [P.thermalEncoding_apply, encodedObservable,
    P.thermalReferenceState_toOperator, ← P.factorization.conjOperator_mul,
    reference_tensor_mul_encoded]

end PauliLikePair

end ThermalEncoding
end Semantics
end QEC
