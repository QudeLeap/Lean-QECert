import QEC.Coding.ExpanderCodes.LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Congruence Sturm and genuine finite-dimensional Hecke spaces

Internal proof closure for the original PK22 theta route. Fourier width, actual
coset norm and level-one Sturm give a finite coefficient injection at Gamma0(N).
The finite basis and matrices describe the already proved weight-two operators.
The arithmetic spectral bound and public theorem pk-good-qldpc remain unproved;
parent #449 remains open. No spectral or finite-dimensional conclusion is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

/-- The number of Fourier coefficients sufficient for the proved congruence Sturm criterion. -/
noncomputable def lpsGamma0CoefficientCount (N : ℕ) (k : ℤ) : ℕ :=
  (k * Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)).toNat / 12 + 1

/-- The actual first-B Fourier coefficients as a complex-linear map to a finite coordinate space. -/
noncomputable def lpsGamma0FiniteCoefficients (N : ℕ) (k : ℤ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      (Fin (lpsGamma0CoefficientCount N k) → ℂ) where
  toFun f j := PowerSeries.coeff j.val (UpperHalfPlane.qExpansion 1 f)
  map_add' f g := by
    ext j
    simp only [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num : (0:ℝ)<1)
      (by simp) f g, map_add, Pi.add_apply]
  map_smul' a f := by
    ext j
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1)
      (by simp) a f, PowerSeries.coeff_smul, Pi.smul_apply, RingHom.id_apply]

/-- Vanishing of the first-B actual Fourier coefficients forces the genuine modular form to vanish. -/
lemma lpsGamma0FiniteCoefficients_eq_zero (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (h : lpsGamma0FiniteCoefficients N k f = 0) : f=0 := by
  have ho := PowerSeries.nat_le_order (UpperHalfPlane.qExpansion 1 f)
    (lpsGamma0CoefficientCount N k) (fun i hi => congrFun h ⟨i,hi⟩)
  apply lpsGamma0_sturm N k f
  apply lt_of_lt_of_le _ ho
  change ((_ : ℕ) : ℕ∞) < ((lpsGamma0CoefficientCount N k : ℕ) : ℕ∞)
  exact_mod_cast Nat.lt_succ_self _

/-- The actual finite Fourier coefficient map is injective at every positive level. -/
lemma lpsGamma0FiniteCoefficients_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (lpsGamma0FiniteCoefficients N k) := by
  apply LinearMap.ker_eq_bot.mp
  exact LinearMap.ker_eq_bot'.mpr (lpsGamma0FiniteCoefficients_eq_zero N k)

/-- The proved finite coefficient injection gives finite-dimensionality of Gamma0(N) modular forms. -/
lemma lpsGamma0FiniteDimensional (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :=
  FiniteDimensional.of_injective (lpsGamma0FiniteCoefficients N k)
    (lpsGamma0FiniteCoefficients_injective N k)

/-- The actual cusp-to-modular inclusion gives finite-dimensionality of Gamma0(N) cusp forms. -/
lemma lpsGamma0CuspFiniteDimensional (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) := by
  let := lpsGamma0FiniteDimensional N k
  exact FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

/-- The finite Fourier coefficient injection bounds the actual modular-form dimension. -/
lemma lpsGamma0_finrank_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) ≤
      lpsGamma0CoefficientCount N k := by
  simpa using LinearMap.finrank_le_finrank_of_injective (lpsGamma0FiniteCoefficients_injective N k)

/-- The genuine cusp inclusion and finite coefficient injection bound the cusp-space dimension. -/
lemma lpsGamma0Cusp_finrank_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) ≤
      lpsGamma0CoefficientCount N k := by
  let := lpsGamma0FiniteDimensional N k
  exact (LinearMap.finrank_le_finrank_of_injective CuspForm.toModularFormₗ_injective).trans
    (lpsGamma0_finrank_le N k)

/-- A finite basis of the genuine cusp space derived from the proved finite-dimensionality. -/
noncomputable def lpsGamma0CuspBasis (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Basis (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N :
      Subgroup (GL (Fin 2) ℝ)) k))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) := by
  letI := lpsGamma0CuspFiniteDimensional N k
  exact Module.finBasis ℂ _

/-- The matrix of the actual weight-two Hecke endomorphism in the derived cusp basis. -/
noncomputable def lpsGamma0HeckeMatrix (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : Matrix
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ :=
  LinearMap.toMatrix (lpsGamma0CuspBasis N 2) (lpsGamma0CuspBasis N 2)
    (lpsCuspHeckeLinearMap N p hNp)

/-- The genuine Hecke matrix acts on coordinates exactly as the actual cusp endomorphism. -/
lemma lpsGamma0HeckeMatrix_action (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (lpsGamma0HeckeMatrix N p hNp).mulVec ((lpsGamma0CuspBasis N 2).repr f) =
      (lpsGamma0CuspBasis N 2).repr (lpsCuspHeckeLinearMap N p hNp f) :=
  LinearMap.toMatrix_mulVec_repr _ _ _ _

/-- The finite matrix of the genuine recursively composed prime-power Hecke operator. -/
noncomputable def lpsGamma0HeckePrimePowerMatrix (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) : Matrix
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ :=
  LinearMap.toMatrix (lpsGamma0CuspBasis N 2) (lpsGamma0CuspBasis N 2)
    (lpsHeckePrimePowerLinearMap N p hNp r)

/-- Reconstruct the actual prime-power Hecke image from its finite matrix and input coordinates. -/
lemma lpsGamma0HeckePrimePowerMatrix_recover (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (lpsGamma0CuspBasis N 2).equivFun.symm
      ((lpsGamma0HeckePrimePowerMatrix N p hNp r).mulVec
        ((lpsGamma0CuspBasis N 2).repr f)) = lpsHeckePrimePowerLinearMap N p hNp r f := by
  rw [lpsGamma0HeckePrimePowerMatrix, LinearMap.toMatrix_mulVec_repr]
  exact (lpsGamma0CuspBasis N 2).equivFun.symm_apply_apply _

/-- The reconstructed finite matrix image recovers the original prime-power Fourier coefficient. -/
lemma lpsGamma0HeckePrimePowerMatrix_coefficient (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1
      ((lpsGamma0CuspBasis N 2).equivFun.symm
        ((lpsGamma0HeckePrimePowerMatrix N p hNp r).mulVec
          ((lpsGamma0CuspBasis N 2).repr f)))) =
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 f) := by
  rw [lpsGamma0HeckePrimePowerMatrix_recover]
  exact coeff_one_lpsHeckePrimePowerLinearMap N p hNp r f

/-- The genuine zeroth prime-power Hecke matrix is the identity, including a zero-dimensional space. -/
lemma lpsGamma0HeckePrimePowerMatrix_zero (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : lpsGamma0HeckePrimePowerMatrix N p hNp 0 = 1 := by
  simp [lpsGamma0HeckePrimePowerMatrix, lpsHeckePrimePowerLinearMap]

/-- The first prime-power Hecke matrix is the matrix of the genuine Hecke operator. -/
lemma lpsGamma0HeckePrimePowerMatrix_one (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : lpsGamma0HeckePrimePowerMatrix N p hNp 1 =
      lpsGamma0HeckeMatrix N p hNp := rfl

/-- The actual finite Hecke matrices obey the exact prime-power recurrence. -/
lemma lpsGamma0HeckePrimePowerMatrix_add_two (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) : lpsGamma0HeckePrimePowerMatrix N p hNp (r+2) =
      lpsGamma0HeckePrimePowerMatrix N p hNp (r+1) * lpsGamma0HeckeMatrix N p hNp -
        (p:ℂ) • lpsGamma0HeckePrimePowerMatrix N p hNp r := by
  simp only [lpsGamma0HeckePrimePowerMatrix, lpsHeckePrimePowerLinearMap,
    map_sub, map_smul, lpsGamma0HeckeMatrix]
  rw [LinearMap.toMatrix_comp (lpsGamma0CuspBasis N 2)
    (lpsGamma0CuspBasis N 2) (lpsGamma0CuspBasis N 2)]

end QEC.Coding.TannerLiftedProduct
