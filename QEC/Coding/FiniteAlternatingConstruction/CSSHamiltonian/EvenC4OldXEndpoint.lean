import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXPrimitiveC2QEndpoint
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.EvenC4SingleCoordinateLift

/-!
# One physical C4 logical-defect witness at every admissible odd scale

The background is a genuine actual RZ syndrome image. The single old-Q root
coordinate is constructed internally from the original all-scale C3 witness.
The complete residual is closed and nonboundary. The stopped-history index
is N=2 and the physical carrier is Physical S 4.
-/

noncomputable section
namespace QEC.Coding.BDL26EvenC4OldXEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open scoped Classical

/-- A full original chi-one residual is closed and is not an actual full
boundary. This elementary consequence retains the whole physical word. -/
private theorem actual_C4_full_residual_of_chi_one (S : OddScale)
    (u : XSyndromeDomain S 2) (q : Physical S 4)
    (hchi : BDL26LogicalDefectProtection.chiX S 2 u q=1) :
    zSyndrome S 4 (BDL26LogicalDefectProtection.deltaX S 2 u q)=0 ∧
      BDL26LogicalDefectProtection.deltaX S 2 u q ∉
        LinearMap.range (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0
          (state S 4).presentation) := by
  let w : BDL26FiniteCohomology.Cocycle S 4 :=
    BDL26HistoryLogicalResidual.topCocycle S 2 (BDL26ActualFailureReadout.input S 2 u)
      (BDL26ActualFailureReadout.flip S 2 q)
  have hw : w.val=BDL26LogicalDefectProtection.deltaX S 2 u q :=
    BDL26ActualFailureReadout.full_residual S 2 u q
  have hclosed : QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1
      (state S 4).presentation w.val=0 :=
    (BDL26RZCohomology.mem_cocycle_iff _ _).mp w.property
  have hcoef : BDL26FiniteCohomology.finiteH1Equiv S 4
      (BDL26FiniteCohomology.classOf S 4 w)=1 :=
    (BDL26ActualFailureReadout.chiX_top_coefficient S 2 u q).symm.trans hchi
  refine ⟨?_,?_⟩
  · have hz : zSyndrome S 4 w.val=0 := hclosed
    exact (congrArg (zSyndrome S 4) hw).symm.trans hz
  · rintro ⟨a,ha⟩
    have hzero := (BDL26HistoryLogicalResidual.coefficient_zero_iff_boundary S 4 w).mpr
      ⟨a,ha.trans hw.symm⟩
    exact one_ne_zero (hcoef.symm.trans hzero)

/-- At every admissible odd scale, the SAME legal original N=2 background and
ONE actual Physical S4 coordinate have original FIRST zero and original chiX
one. Their complete original deltaX is closed and is not an actual full
boundary. The genuine RZ cylinder root is chosen internally; callers provide
no geometry, coherence, H1 section or failure premise. -/
theorem exists_original_even_C4_single_physical_first_zero_chi_one (S : OddScale) :
    ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 2,
      ∃ q : BDL26CSSHamiltonian.Physical S 4,
        BDL26ActualFailureReadout.firstReadout S 2 u=0 ∧
        BDL26LogicalDefectProtection.chiX S 2 u q=1 ∧
        BDL26CSSHamiltonian.zSyndrome S 4
          (BDL26LogicalDefectProtection.deltaX S 2 u q)=0 ∧
        BDL26LogicalDefectProtection.deltaX S 2 u q ∉ LinearMap.range
          (QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary0
            (BDL26DecodingGraph.state S 4).presentation) := by
  obtain ⟨x,outer,u3,edge,_hparse,hfirst,hchi⟩ :=
    BDL26RXPrimitiveC2QEndpoint.exists_original_oldX_all_odd_first_zero_chi_one S
  let q3 : BDL26CSSHamiltonian.Physical S 3 :=
    BDL26RXPhysicalCoordinateTrace.oldXPhysical S 1 (by decide) x outer edge
  let v : BDL26TannerLocalRegularity.QDoubleCylinderVertex
      (BDL26FiniteTannerSquare.transposePresentation (state S 3).presentation) q3 S :=
    BDL26RZMap1CoordinateBridge.rzMap1QRoot (state S 3).presentation q3 S
  let u4 : XSyndromeDomain S 2 := BDL26EvenC4SingleCoordinateLift.embedC3Input S u3
  let q4 : Physical S 4 := BDL26EvenC4SingleCoordinateLift.rzOldQCoordinate S q3 v
  have hf : BDL26ActualFailureReadout.firstReadout S 2 u4=0 :=
    (BDL26EvenC4SingleCoordinateLift.firstReadout_embedC3Input S u3).trans hfirst
  have hc : BDL26LogicalDefectProtection.chiX S 2 u4 q4=1 :=
    (BDL26EvenC4SingleCoordinateLift.chiX_embedC3Input S u3 q3 v).trans hchi
  obtain ⟨hclosed,hnb⟩ := actual_C4_full_residual_of_chi_one S u4 q4 hc
  exact ⟨u4,q4,hf,hc,hclosed,hnb⟩

end QEC.Coding.BDL26EvenC4OldXEndpoint
end
