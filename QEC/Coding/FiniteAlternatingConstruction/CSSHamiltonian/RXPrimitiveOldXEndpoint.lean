import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.RXPrimitiveC2QEndpoint

/-!
# A finite physical old-X obstruction for the original selector

The admissible scale is ell=3. The legal original background, exact primitive
parser class, FIRST-zero readout and nonzero actual logical defect all use
the same single physical old-X edge. The underlying construction retains the
full original accumulated potential and both original level-two decoder calls.
This internal result does not refute a sufficiently-large-scale theorem or
establish a paper-level stability or lifetime statement.
-/
namespace QEC.Coding.BDL26RXPrimitiveOldXEndpoint
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ActualFailureReadout BDL26RXPhysicalCoordinateTrace
open scoped Classical

/-- A legal ell-three original single-physical-old-X witness with exact parser
identity, FIRST readout zero and actual logical defect one. No selector output,
NONE branch, defect value or closed non-boundary witness is an assumption. -/
theorem exists_ell_three_single_physical_first_zero_chi_one :
    ∃ S : OddScale,S.ell=3 ∧
      ∃ x : (state S 1).presentation.X,
      ∃ outer : BDL26FiniteTannerSquare.Two,
      ∃ u : BDL26TransposedStoppedDecoder.XSyndromeDomain S 1,
      ∃ edge : DoubleCylinderEdge (state S 2).presentation
          (oldXOwner S 1 (by decide) x outer) S,
        parse S 1 (oldXPhysical S 1 (by decide) x outer edge)=
          Leaf.primitive (Primitive.oldX 1 (by decide) x outer edge) ∧
        firstReadout S 1 u=0 ∧
          BDL26LogicalDefectProtection.chiX S 1 u
            (oldXPhysical S 1 (by decide) x outer edge)=1 := by
  let S : OddScale := ⟨3,by decide,by decide⟩
  have hh : S.half=1 := by decide
  obtain ⟨x,outer,u,edge,hparse,hfirst,hchi⟩ :=
    BDL26RXPrimitiveC2QEndpoint.exists_original_oldX_first_zero_chi_one S hh
  exact ⟨S,rfl,x,outer,u,edge,hparse,hfirst,hchi⟩

end QEC.Coding.BDL26RXPrimitiveOldXEndpoint
