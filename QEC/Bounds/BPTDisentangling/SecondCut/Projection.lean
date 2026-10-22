import QEC.Bounds.BPTDisentangling.SecondCut.Transport

/-!
# BPT second-cut sector projection algebra

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
Compressing an orthogonal projection to an invariant isometric subspace again
gives an orthogonal projection.  The second-cut use takes `J` to be the
chosen isotypic-sector inclusion; this is the projection input needed for
the source `Pi_AB'` rank-one step.
-/
theorem isSymmetricProjection_of_isometric_compression_commuting
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (P : Semantics.Operator K)
    (hJadj : Jadj.comp J = (1 : Semantics.Operator H))
    (hJadj_eq : LinearMap.adjoint J = Jadj)
    (hP : P.IsSymmetricProjection)
    (hcommute : Commute P (J.comp Jadj)) :
    (Jadj.comp (P.comp J)).IsSymmetricProjection := by
  let S : Semantics.Operator K := J.comp Jadj
  have hSP : S.comp P = P.comp S := by
    simpa [S, Module.End.mul_eq_comp] using hcommute.eq.symm
  have hSJ : S.comp J = J := by
    calc
      S.comp J = (J.comp Jadj).comp J := by rfl
      _ = J.comp (Jadj.comp J) := by rw [LinearMap.comp_assoc]
      _ = J.comp (1 : Semantics.Operator H) := by rw [hJadj]
      _ = J := by
        apply LinearMap.ext
        intro vector
        rfl
  constructor
  · apply LinearMap.ext
    intro x
    have hSPx : S (P (J x)) = P (S (J x)) := by
      have h := congrArg (fun T : Semantics.Operator K => T (J x)) hSP
      simpa only [LinearMap.comp_apply] using h
    have hPP : P.comp P = P := by
      exact hP.isIdempotentElem
    have hPPx : P (P (S (J x))) = P (S (J x)) := by
      have h := congrArg (fun T : Semantics.Operator K => T (S (J x))) hPP
      simpa only [LinearMap.comp_apply] using h
    have hSJx : S (J x) = J x := by
      have h := congrArg (fun T : H →ₗ[Complex] K => T x) hSJ
      simpa only [LinearMap.comp_apply] using h
    change Jadj (P (S (P (J x)))) = Jadj (P (J x))
    calc
      Jadj (P (S (P (J x)))) = Jadj (P (P (S (J x)))) :=
        congrArg (fun y => Jadj (P y)) hSPx
      _ = Jadj (P (S (J x))) := congrArg Jadj hPPx
      _ = Jadj (P (J x)) := congrArg (fun y => Jadj (P y)) hSJx
  · apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
    apply LinearMap.isSelfAdjoint_iff'.mpr
    have hadjJadj : LinearMap.adjoint Jadj = J := by
      calc
        LinearMap.adjoint Jadj = LinearMap.adjoint (LinearMap.adjoint J) := by
          rw [hJadj_eq]
        _ = J := LinearMap.adjoint_adjoint J
    calc
      LinearMap.adjoint (Jadj.comp (P.comp J)) =
          (LinearMap.adjoint J).comp
            ((LinearMap.adjoint P).comp (LinearMap.adjoint Jadj)) := by
        simp only [LinearMap.adjoint_comp, LinearMap.comp_assoc]
      _ = Jadj.comp (P.comp J) := by
        simp only [hJadj_eq, hP.isSymmetric.adjoint_eq, hadjJadj]

/--
The left projector restricted to an isotypic sector remains an orthogonal
projection.  Its invariance is obtained from the actual interaction algebra,
so the resulting statement applies directly to the second-cut `Pleft` block.
-/
theorem overlapProjectorOnIsotypicComponent_isSymmetricProjection
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (hP : P.IsSymmetricProjection)
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    (overlapProjectorOnIsotypicComponent P component).IsSymmetricProjection := by
  let p : Submodule Complex B := component.1.restrictScalars Complex
  let J : (Semantics.CompositeSystem A p) →ₗ[Complex]
      Semantics.CompositeSystem A B :=
    TensorProduct.map (1 : Semantics.Operator A) p.subtype
  let Jadj : (Semantics.CompositeSystem A B) →ₗ[Complex]
      Semantics.CompositeSystem A p :=
    TensorProduct.map (1 : Semantics.Operator A) (LinearMap.adjoint p.subtype)
  have hJadj : Jadj.comp J = (1 : Semantics.Operator (Semantics.CompositeSystem A p)) := by
    dsimp [J, Jadj]
    rw [← TensorProduct.map_comp]
    rw [adjoint_submoduleSubtype_comp_subtype_eq_one p]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id) LinearMap.id = LinearMap.id
    rw [LinearMap.id_comp]
    exact TensorProduct.map_one
  have hJadj_eq : LinearMap.adjoint J = Jadj := by
    dsimp [J, Jadj]
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  have hJJ : J.comp Jadj =
      TensorProduct.map (1 : Semantics.Operator A)
        (leftIsotypicSectorProjector P component) := by
    dsimp [J, Jadj]
    rw [← TensorProduct.map_comp]
    rw [submoduleSubtype_comp_adjoint_eq_starProjection p]
    change TensorProduct.map (LinearMap.id.comp LinearMap.id) p.starProjection.toLinearMap =
      TensorProduct.map LinearMap.id (leftIsotypicSectorProjector P component)
    rw [LinearMap.id_comp]
    rfl
  have hsectorCommutes : Commute P
      (TensorProduct.map (1 : Semantics.Operator A)
        (leftIsotypicSectorProjector P component)) := by
    apply commute_leftOverlap_of_commute_leftInteractionCoefficients
    intro a a'
    exact leftIsotypicSectorProjector_commute_leftInteractionCoefficient P component a a'
  have hcommute : Commute P (J.comp Jadj) := by
    rw [hJJ]
    exact hsectorCommutes
  change (Jadj.comp (P.comp J)).IsSymmetricProjection
  exact isSymmetricProjection_of_isometric_compression_commuting
    J Jadj P hJadj hJadj_eq hP hcommute

end BPTCommutingProjectorModel

end Bounds
end QEC
