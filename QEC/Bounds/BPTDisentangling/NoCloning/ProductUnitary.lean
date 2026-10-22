import QEC.Bounds.BPTDisentangling.NoCloning.PartialTrace

/-!
# BPT normalized product unitaries

Cacheable internal proof layer for the finite-dimensional BPT Disentangling Lemma.
-/

noncomputable section

namespace QEC
namespace Bounds

open Classical
open scoped BigOperators ComplexOrder TensorProduct

universe u v

namespace BPTCommutingProjectorModel

variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

/-- Equal-norm unit vectors in a finite quantum system are connected by a global unitary. -/
theorem exists_unitaryTransport_map_eq_of_norm_eq
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ U : Semantics.UnitaryTransport H H, U x = y := by
  classical
  have hx0 : x ≠ 0 := by
    intro hzero
    have hzero_one : (0 : ℝ) = 1 := by simpa [hzero] using hx
    norm_num at hzero_one
  letI : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
  have hdimpos : 0 < Module.finrank Complex H := Module.finrank_pos_iff.mpr inferInstance
  let i0 : Fin (Module.finrank Complex H) := ⟨0, hdimpos⟩
  let s : Set (Fin (Module.finrank Complex H)) := {i0}
  let vx : Fin (Module.finrank Complex H) → H := fun _ => x
  let vy : Fin (Module.finrank Complex H) → H := fun _ => y
  letI : Subsingleton s := ⟨fun a b => by
    apply Subtype.ext
    have ha_mem : (a : Fin (Module.finrank Complex H)) ∈ ({i0} : Set _) := by
      change (a : Fin (Module.finrank Complex H)) ∈ s
      exact a.property
    have hb_mem : (b : Fin (Module.finrank Complex H)) ∈ ({i0} : Set _) := by
      change (b : Fin (Module.finrank Complex H)) ∈ s
      exact b.property
    have ha : (a : Fin (Module.finrank Complex H)) = i0 := Set.mem_singleton_iff.mp ha_mem
    have hb : (b : Fin (Module.finrank Complex H)) = i0 := Set.mem_singleton_iff.mp hb_mem
    exact ha.trans hb.symm⟩
  have hvx : Orthonormal Complex (s.restrict vx) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hx
  have hvy : Orthonormal Complex (s.restrict vy) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hy
  obtain ⟨bx, hbx⟩ := hvx.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin (Module.finrank Complex H)) (by simp)
  obtain ⟨bY, hbY⟩ := hvy.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin (Module.finrank Complex H)) (by simp)
  have hbx0 : bx i0 = x := by
    simpa [vx] using hbx i0 (by simp [s])
  have hbY0 : bY i0 = y := by
    simpa [vy] using hbY i0 (by simp [s])
  let E : H ≃ₗᵢ[Complex] H := bx.equiv bY (Equiv.refl _)
  let U : Semantics.UnitaryTransport H H :=
    { toLinearEquiv := E.toLinearEquiv
      map_inner := fun a b => E.inner_map_map a b }
  have hU : U x = y := by
    change E x = y
    calc
      E x = E (bx i0) := by rw [hbx0]
      _ = bY i0 := by
        simpa [E] using bx.equiv_apply_basis bY (Equiv.refl _) i0
      _ = y := hbY0
  exact ⟨U, hU⟩

/-- A normalized two-factor vector can be sent to a normalized product vector by a global unitary. -/
theorem exists_unitaryTransport_map_eq_normalized_product
    {N C : Type u} [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (psi : Semantics.CompositeSystem N C) (hpsi : ‖psi‖ = 1) :
    ∃ n0 : N, ∃ c0 : C, ‖n0‖ = 1 ∧ ‖c0‖ = 1 ∧
      ∃ U : Semantics.UnitaryTransport (Semantics.CompositeSystem N C)
        (Semantics.CompositeSystem N C), U psi = n0 ⊗ₜ[Complex] c0 := by
  classical
  have hN : ∃ n : N, n ≠ 0 := by
    by_contra hN
    have hzeroN : ∀ n : N, n = 0 := by
      intro n
      by_contra hn
      exact hN ⟨n, hn⟩
    letI : Subsingleton N := ⟨fun a b => by rw [hzeroN a, hzeroN b]⟩
    have hpsi0 : psi = 0 := Subsingleton.elim _ _
    rw [hpsi0] at hpsi
    norm_num at hpsi
  have hC : ∃ c : C, c ≠ 0 := by
    by_contra hC
    have hzeroC : ∀ c : C, c = 0 := by
      intro c
      by_contra hc
      exact hC ⟨c, hc⟩
    letI : Subsingleton C := ⟨fun a b => by rw [hzeroC a, hzeroC b]⟩
    have hpsi0 : psi = 0 := Subsingleton.elim _ _
    rw [hpsi0] at hpsi
    norm_num at hpsi
  rcases hN with ⟨n, hn⟩
  rcases hC with ⟨c, hc⟩
  let n0 : N := (‖n‖⁻¹ : Complex) • n
  let c0 : C := (‖c‖⁻¹ : Complex) • c
  have hn0 : ‖n0‖ = 1 := by
    exact norm_smul_inv_norm (𝕜 := Complex) hn
  have hc0 : ‖c0‖ = 1 := by
    exact norm_smul_inv_norm (𝕜 := Complex) hc
  have hproduct : ‖n0 ⊗ₜ[Complex] c0‖ = 1 := by
    simp [hn0, hc0]
  rcases exists_unitaryTransport_map_eq_of_norm_eq psi
    (n0 ⊗ₜ[Complex] c0) hpsi hproduct with ⟨U, hU⟩
  exact ⟨n0, c0, hn0, hc0, U, hU⟩

/-- The D1 global unitary sends the corresponding pure rank-one operator to a product rank one. -/
theorem exists_unitaryTransport_conj_rankOne_eq_normalized_product
    {N C : Type u} [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (psi : Semantics.CompositeSystem N C) (hpsi : ‖psi‖ = 1) :
    ∃ n0 : N, ∃ c0 : C, ‖n0‖ = 1 ∧ ‖c0‖ = 1 ∧
      ∃ U : Semantics.UnitaryTransport (Semantics.CompositeSystem N C)
        (Semantics.CompositeSystem N C), U psi = n0 ⊗ₜ[Complex] c0 ∧
        U.conjOperator (InnerProductSpace.rankOne Complex psi psi).toLinearMap =
          (InnerProductSpace.rankOne Complex (n0 ⊗ₜ[Complex] c0)
            (n0 ⊗ₜ[Complex] c0)).toLinearMap := by
  rcases exists_unitaryTransport_map_eq_normalized_product psi hpsi with
    ⟨n0, c0, hn0, hc0, U, hU⟩
  refine ⟨n0, c0, hn0, hc0, U, hU, ?_⟩
  rw [Semantics.QuditSubsystem.conjOperator_rankOne, hU]

end BPTCommutingProjectorModel

end Bounds
end QEC
