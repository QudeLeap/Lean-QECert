import QEC.Coding.FiniteAlternatingConstruction.RZCohomology.Representatives

/-! # Both quotient inverses for the selected actual RZ map -/

namespace QEC.Coding.BDL26RZCohomology

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance BDL26RZLocalReplacement

/-- The actual parity left inverse already holds on cocycle representatives. -/
theorem backward_forward_cocycle (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (v : Cocycle P) :
    backwardCocycle P A4 S (forwardCocycle P A4 S v) = v := by
  apply Subtype.ext
  exact rzQParity_map1Coord P A4 S v.1

theorem backward_forward (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (v : H1 P) :
    backward P A4 S (forward P A4 S v) = v := by
  obtain ⟨representative, rfl⟩ := (complex P).middleCoboundaryInCocycles.mkQ_surjective v
  rw [forward_mk, backward_mk, backward_forward_cocycle]

/-- The actual discrepancy from lifting parity is a constructed coboundary. -/
theorem forward_backward_residual_boundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : Cocycle (successor P A4 S)) :
    forwardCocycle P A4 S (backwardCocycle P A4 S w) - w ∈
      (complex (successor P A4 S)).middleCoboundaryInCocycles := by
  let word : Word Field (RZQ P S) := w.1
  let residual : Word Field (RZQ P S) := map1Coord P A4 S (rzQParity P S word) - word
  change (residual : Word Field (successor P A4 S).Q) ∈
    (complex (successor P A4 S)).firstCoboundaryCheckCode.carrier
  apply (mem_boundary_iff _ _).mpr
  have hsemantic := (mem_cocycle_iff _ _).mp
    (forwardCocycle P A4 S (backwardCocycle P A4 S w) - w).2
  have hc : rzCoboundary1 P A4 S residual = 0 := by
    funext z
    exact congrFun hsemantic z
  have hp : rzQParity P S residual = 0 := by
    dsimp only [residual]
    rw [map_sub, rzQParity_map1Coord, sub_self]
  obtain ⟨potential, heq⟩ := rzCocycle_qParity_zero_is_coboundary P A4 R S residual hc hp
  refine ⟨potential, ?_⟩
  funext q
  exact congrFun heq q

theorem forward_backward (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : H1 (successor P A4 S)) :
    forward P A4 S (backward P A4 S w) = w := by
  obtain ⟨representative, rfl⟩ :=
    (complex (successor P A4 S)).middleCoboundaryInCocycles.mkQ_surjective w
  rw [backward_mk, forward_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (forward_backward_residual_boundary P A4 R S representative)

/-- Actual RZ first-cohomology equivalence, with the selected map as its forward
map and the finite Q-cylinder parity as its inverse. -/
noncomputable def equiv (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    H1 P ≃ₗ[Field] H1 (successor P A4 S) where
  toLinearMap := forward P A4 S
  invFun := backward P A4 S
  left_inv := backward_forward P A4 S
  right_inv := forward_backward P A4 R S

@[simp] theorem equiv_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    equiv P A4 R S (classOf P v) =
      classOf (successor P A4 S) (forwardCocycle P A4 S v) := forward_mk P A4 S v

@[simp] theorem equiv_symm_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : Cocycle (successor P A4 S)) :
    (equiv P A4 R S).symm (classOf (successor P A4 S) w) =
      classOf P (backwardCocycle P A4 S w) := backward_mk P A4 S w

end QEC.Coding.BDL26RZCohomology
