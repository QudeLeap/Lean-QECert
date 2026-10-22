import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic

/-!
# Volume-preserving axial coordinates

Splitting the first Euclidean coordinate from the remaining two preserves
Lebesgue measure. A reflection can align any chosen unit axis with the first
coordinate, without selecting a family of rotations measurably.
-/

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap

open MeasureTheory

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Transverse := EuclideanSpace ℝ (Fin 2)

noncomputable def axialEquiv : Ambient ≃ᵐ ℝ × Transverse :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))

theorem axialEquiv_measurePreserving :
    MeasurePreserving axialEquiv volume (volume.prod volume) := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

@[simp] theorem axialEquiv_fst (x : Ambient) : (axialEquiv x).1 = x 0 := rfl

@[simp] theorem axialEquiv_snd_apply (x : Ambient) (i : Fin 2) :
    (axialEquiv x).2 i = x i.succ := rfl

theorem norm_sq_axial (x : Ambient) :
    ‖x‖ ^ 2 = (axialEquiv x).1 ^ 2 + ‖(axialEquiv x).2‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    axialEquiv_fst, axialEquiv_snd_apply]

/-- Reflection in the bisecting hyperplane sends either unit axis to the other. -/
noncomputable def axisReflection (u v : Ambient) : Ambient ≃ₗᵢ[ℝ] Ambient :=
  (ℝ ∙ (u - v))ᗮ.reflection

theorem axisReflection_apply (u v : Ambient) (h : ‖u‖ = ‖v‖) :
    axisReflection u v u = v := Submodule.reflection_sub h

theorem axisReflection_measurePreserving (u v : Ambient) :
    MeasurePreserving (axisReflection u v) volume volume :=
  (axisReflection u v).measurePreserving

end QEC.Coding.ProbabilisticConstruction.SphericalCap
