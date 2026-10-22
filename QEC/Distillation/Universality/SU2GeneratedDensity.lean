import QEC.Distillation.Universality.SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Projective density from irrational special-unitary axis words

This internal module turns two literal determinant-one generated words at a
common irrational axis-circle angle into projective one-qubit density. It
works through the topological closure of the supplied ambient generated
subgroup and never asserts raw density in `U(2)`.
-/

noncomputable section

namespace QEC
namespace Distillation

open GeneratedUniversality

/-- The determinant-one part of the ambient generated topological closure. -/
def specialUnitaryGeneratedClosure (generators : Set SingleQubitGate) :
    Subgroup SingleQubitSpecialUnitary :=
  (generatedUnitarySubgroup generators).topologicalClosure.comap
    determinantOneSubgroup.subtype

/-- Membership in the special-unitary pullback is ambient generated-closure membership. -/
theorem mem_specialUnitaryGeneratedClosure_iff
    (generators : Set SingleQubitGate) (U : SingleQubitSpecialUnitary) :
    U ∈ specialUnitaryGeneratedClosure generators ↔
      (U : SingleQubitGate) ∈ generatedUnitaryTopologicalClosure generators :=
  Iff.rfl

/-- The special-unitary pullback of the ambient generated closure is closed. -/
theorem isClosed_specialUnitaryGeneratedClosure
    (generators : Set SingleQubitGate) :
    IsClosed (specialUnitaryGeneratedClosure generators : Set SingleQubitSpecialUnitary) := by
  change IsClosed
    ((determinantOneSubgroup.subtype :
      SingleQubitSpecialUnitary → SingleQubitGate) ⁻¹'
      ((generatedUnitarySubgroup generators).topologicalClosure : Set SingleQubitGate))
  exact (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val

/-- The axis circle regarded as an additive-to-multiplicative group homomorphism. -/
noncomputable def axisCircleAddHom (axis : UnitBlochAxis) :
    AddMonoidHom (AddCircle (2 * Real.pi)) (Additive SingleQubitGate) where
  toFun t := Additive.ofMul (axisCircle axis t)
  map_zero' := by
    change Additive.ofMul (axisCircle axis 0) = Additive.ofMul 1
    rw [axisCircle_zero]
  map_add' t u := by
    change Additive.ofMul (axisCircle axis (t + u)) =
      Additive.ofMul (axisCircle axis t * axisCircle axis u)
    rw [axisCircle_add]

/-- Integer circle multiples give integer powers of the corresponding gate. -/
theorem axisCircle_zsmul (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (z : Int) :
    axisCircle axis (z • t) = (axisCircle axis t) ^ z := by
  exact map_zsmul (axisCircleAddHom axis) z t

/-- Integer circle multiples give integer powers in the special-unitary circle. -/
theorem axisCircleSU_zsmul (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (z : Int) :
    axisCircleSU axis (z • t) = (axisCircleSU axis t) ^ z := by
  apply Subtype.ext
  exact axisCircle_zsmul axis t z

/-- The special-unitary axis circle is continuous. -/
theorem continuous_axisCircleSU (axis : UnitBlochAxis) :
    Continuous (axisCircleSU axis) := by
  apply continuous_induced_rng.2
  exact axisCircle_continuous axis

/-- An irrational generated axis word puts the whole special-unitary axis circle in closure. -/
theorem axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
    (generators : Set SingleQubitGate) (axis : UnitBlochAxis) (theta : ℝ)
    (word : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi))) :
    ∀ t : AddCircle (2 * Real.pi),
      axisCircleSU axis t ∈ specialUnitaryGeneratedClosure generators := by
  let K := specialUnitaryGeneratedClosure generators
  have hbase : axisCircleSU axis (theta : AddCircle (2 * Real.pi)) ∈ K := by
    change axisCircle axis (theta : AddCircle (2 * Real.pi)) ∈
      (generatedUnitarySubgroup generators).topologicalClosure
    rw [← hword_eq]
    exact Subgroup.le_topologicalClosure _ hword
  have hclosed : IsClosed (K : Set SingleQubitSpecialUnitary) := by
    exact isClosed_specialUnitaryGeneratedClosure generators
  have horbit : Set.range (fun z : Int => z • (theta : AddCircle (2 * Real.pi))) ⊆
      (axisCircleSU axis) ⁻¹' (K : Set SingleQubitSpecialUnitary) := by
    rintro _ ⟨z, rfl⟩
    change axisCircleSU axis (z • (theta : AddCircle (2 * Real.pi))) ∈ K
    rw [axisCircleSU_zsmul]
    exact K.zpow_mem hbase z
  have hpreimage : IsClosed ((axisCircleSU axis) ⁻¹' (K : Set SingleQubitSpecialUnitary)) :=
    hclosed.preimage (continuous_axisCircleSU axis)
  have hclosure : closure (Set.range (fun z : Int =>
      z • (theta : AddCircle (2 * Real.pi)))) ⊆
      (axisCircleSU axis) ⁻¹' (K : Set SingleQubitSpecialUnitary) :=
    closure_minimal horbit hpreimage
  have hdense : DenseRange (fun z : Int => z • (theta : AddCircle (2 * Real.pi))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr htheta
  intro t
  apply hclosure
  rw [dense_iff_closure_eq.mp hdense]
  trivial

/-- Two nonparallel irrational generated axis words are projectively dense. -/
theorem projectivelyGeneratedDense_of_irrational_axis_words
    (generators : Set SingleQubitGate) (axis axis' : UnitBlochAxis) (theta : ℝ)
    (word word' : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (hword' : word' ∈ generatedUnitarySubgroup generators)
    (hword'_eq : word' = axisCircle axis' (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi)))
    (hnonparallel : axis.Nonparallel axis') :
    ProjectivelyGeneratedDense generators := by
  let K := specialUnitaryGeneratedClosure generators
  have haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K := by
    exact axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
      generators axis theta word hword hword_eq htheta
  have haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K := by
    exact axisCircleSU_mem_specialUnitaryGeneratedClosure_of_irrational_word
      generators axis' theta word' hword' hword'_eq htheta
  have htop : K = ⊤ :=
    closedSubgroup_eq_top_of_contains_nonparallel_axisCircles K
      (isClosed_specialUnitaryGeneratedClosure generators) axis axis' hnonparallel haxis haxis'
  intro target
  refine ⟨phaseNormalize target, ?_, ?_⟩
  · change (⟨phaseNormalize target, phaseNormalize_det target⟩ :
      SingleQubitSpecialUnitary) ∈ K
    rw [htop]
    trivial
  · exact globalPhaseEquivalent_symm (phaseNormalize_globalPhaseEquivalent target)

/-- The projective-density criterion yields finite-precision one-qubit universality. -/
theorem finitePrecisionOneQubitUniversal_of_irrational_axis_words
    (generators : Set SingleQubitGate) (axis axis' : UnitBlochAxis) (theta : ℝ)
    (word word' : SingleQubitGate)
    (hword : word ∈ generatedUnitarySubgroup generators)
    (hword_eq : word = axisCircle axis (theta : AddCircle (2 * Real.pi)))
    (hword' : word' ∈ generatedUnitarySubgroup generators)
    (hword'_eq : word' = axisCircle axis' (theta : AddCircle (2 * Real.pi)))
    (htheta : Irrational (theta / (2 * Real.pi)))
    (hnonparallel : axis.Nonparallel axis') :
    FinitePrecisionOneQubitUniversal generators :=
  finitePrecisionOneQubitUniversal_of_projectivelyGeneratedDense
    (projectivelyGeneratedDense_of_irrational_axis_words generators axis axis' theta word word'
      hword hword_eq hword' hword'_eq htheta hnonparallel)

end Distillation
end QEC
