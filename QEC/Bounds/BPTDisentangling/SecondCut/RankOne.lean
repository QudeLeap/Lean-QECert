import QEC.Bounds.BPTDisentangling.Sectors.Compression

/-!
# BPT second-cut rank-one projection algebra

Internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/--
A nonzero finite orthogonal projection with at most one-dimensional range is
the rank-one projector onto a normalized vector.  This is the final
projection-level conversion used first for the source `Pi_AB'` factor and
again for the residual `Theta_{B''C'}` no-cloning factor.
-/
theorem isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hdim : Module.finrank Complex (LinearMap.range P) ≤ 1) :
    ∃ phi : H, ‖phi‖ = 1 ∧
      P = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hP0
  let v : H := P x
  have hv : v ≠ 0 := by
    simpa [v] using hx
  let vRange : LinearMap.range P := ⟨v, x, rfl⟩
  have hvRange : vRange ≠ 0 := by
    intro hzero
    apply hv
    have hcoerce := congrArg (fun z : LinearMap.range P => (z : H)) hzero
    simpa [vRange] using hcoerce
  have hpositive : 0 < Module.finrank Complex (LinearMap.range P) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨vRange, hvRange⟩
  have hdimEq : Module.finrank Complex (LinearMap.range P) = 1 := by
    apply Nat.le_antisymm hdim
    exact Nat.succ_le_iff.mpr hpositive
  let phi : H := (‖v‖ : Complex)⁻¹ • v
  have hnormv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hphi : ‖phi‖ = 1 := by
    dsimp [phi]
    rw [norm_smul, norm_inv]
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)] using
      inv_mul_cancel₀ hnormv
  have hscale : (‖v‖ : Complex) • phi = v := by
    calc
      (‖v‖ : Complex) • phi =
          (‖v‖ : Complex) • ((‖v‖ : Complex)⁻¹ • v) := by rfl
      _ = ((‖v‖ : Complex) * (‖v‖ : Complex)⁻¹) • v :=
        (mul_smul (‖v‖ : Complex) (‖v‖ : Complex)⁻¹ v).symm
      _ = v := by
        rw [mul_inv_cancel₀]
        · exact one_smul Complex v
        · exact_mod_cast hnormv
  have hrange : LinearMap.range P = Submodule.span Complex {phi} := by
    apply le_antisymm
    · intro y hy
      let yRange : LinearMap.range P := ⟨y, hy⟩
      rcases exists_smul_eq_of_finrank_eq_one hdimEq hvRange yRange with
        ⟨scalar, hscalar⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨scalar * (‖v‖ : Complex), ?_⟩
      change (scalar * (‖v‖ : Complex)) • phi = y
      calc
        (scalar * (‖v‖ : Complex)) • phi = scalar • ((‖v‖ : Complex) • phi) := by
          exact mul_smul scalar (‖v‖ : Complex) phi
        _ = scalar • v := by rw [hscale]
        _ = y := congrArg Subtype.val hscalar
    · refine Submodule.span_le.2 ?_
      intro z hz
      have hzphi : z = phi := by simpa using hz
      subst z
      dsimp [phi]
      exact (LinearMap.range P).smul_mem _ ⟨x, rfl⟩
  let R : Semantics.Operator H := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  have hR : R.IsSymmetricProjection := by
    simpa [R] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hphi)
  have hrangeR : LinearMap.range R = Submodule.span Complex {phi} := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      change (inner Complex phi z) • phi ∈ Submodule.span Complex {phi}
      exact (Submodule.span Complex {phi}).smul_mem _
        (Submodule.mem_span_singleton_self phi)
    · refine Submodule.span_le.2 ?_
      intro z hz
      have hzphi : z = phi := by simpa using hz
      subst z
      refine ⟨phi, ?_⟩
      change (inner Complex phi phi) • phi = phi
      rw [inner_self_eq_norm_sq_to_K]
      simpa [hphi]
  have hrangePR : LinearMap.range P = LinearMap.range R :=
    hrange.trans hrangeR.symm
  letI : (LinearMap.range P).HasOrthogonalProjection :=
    hP.hasOrthogonalProjection_range
  have projection_residual_orthogonal
      (T : Semantics.Operator H) (hT : T.IsSymmetricProjection)
      {z : H} : z - T z ∈ (LinearMap.range T)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    rcases hy with ⟨w, rfl⟩
    have hidem : T (T w) = T w := by
      change (T * T) w = T w
      rw [hT.isIdempotentElem]
    rw [inner_sub_left]
    calc
      inner Complex z (T w) - inner Complex (T z) (T w) =
          inner Complex z (T w) - inner Complex z (LinearMap.adjoint T (T w)) := by
            rw [LinearMap.adjoint_inner_right]
      _ = inner Complex z (T w) - inner Complex z (T w) := by
            rw [hT.isSymmetric.adjoint_eq, hidem]
      _ = 0 := sub_self _
  refine ⟨phi, hphi, ?_⟩
  apply LinearMap.ext
  intro z
  have hPmem : P z ∈ LinearMap.range P := ⟨z, rfl⟩
  have hPperp : z - P z ∈ (LinearMap.range P)ᗮ :=
    projection_residual_orthogonal P hP
  have hPstar : P z = (LinearMap.range P).starProjection z :=
    (Submodule.eq_starProjection_of_mem_orthogonal hPmem hPperp).symm
  have hRmem : R z ∈ LinearMap.range P := by
    rw [hrangePR]
    exact ⟨z, rfl⟩
  have hRperp : z - R z ∈ (LinearMap.range P)ᗮ := by
    rw [hrangePR]
    exact projection_residual_orthogonal R hR
  have hRstar : R z = (LinearMap.range P).starProjection z :=
    (Submodule.eq_starProjection_of_mem_orthogonal hRmem hRperp).symm
  rw [hPstar, hRstar]

end BPTCommutingProjectorModel

end Bounds
end QEC
