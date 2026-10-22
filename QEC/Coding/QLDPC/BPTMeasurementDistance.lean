import QEC.Coding.QLDPC.FiniteQuditCheckPresentation
import QEC.Semantics.ErrorCorrection.FiniteMeasurementDistance

/-!
# BPT measurement distance and semantic qLDPC distance

This bridge is kept separate from the foundational finite-qudit check
presentation so that the latter remains independent of the BPT measurement
distance formalism.
-/

noncomputable section

namespace QEC
namespace QLDPC

universe u

/-- BPT detectability bounds the least failed local-operator region for nontrivial codes. -/
theorem le_semanticQuditDistance_of_bptMeasurementDistance
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (d : Nat)
    (hd : Semantics.QuditSubsystem.BPTMeasurementDistance code d)
    (hfull : ¬ Semantics.QuditSubsystem.NoInformationOn code
      (Semantics.QuditSubsystem.fullRegion q)) :
    d ≤ semanticQuditDistance q code := by
  have hnotAll : ¬ Semantics.QuditSubsystem.AllLocalScalarCompression code
      (Semantics.QuditSubsystem.fullRegion q) := by
    intro hAll
    exact hfull (((Semantics.QuditSubsystem.fullRegion q).noInformationOn_iff_allLocalScalarCompression
      code).2 hAll)
  simp only [Semantics.QuditSubsystem.AllLocalScalarCompression, not_forall] at hnotAll
  obtain ⟨E, hE⟩ := hnotAll
  apply le_semanticQuditDistance_of_detectable_and_exists_nondetectable code d
  · intro region hcard localOperator
    have hscalar := (region.noInformationOn_iff_allLocalScalarCompression code).1
      (hd region hcard) localOperator
    exact (Semantics.QuditSubsystem.scalarCompression_iff_detectableOn code _).1 hscalar
  · refine ⟨Semantics.QuditSubsystem.fullRegion q, E, ?_⟩
    intro hdetect
    exact hE ((Semantics.QuditSubsystem.scalarCompression_iff_detectableOn code _).2
      hdetect)

end QLDPC
end QEC
