import QEC.Coding.CodeReduction.DistanceBalancing.Locality
import QEC.Coding.FiberBundle.ExplicitFamily.DistanceBalancing

/-!
# Constant locality of the final HHO20 code

This module instantiates the finite EKZ locality theorem on the dual of the
HHO20 weight-reduced fiber-bundle complex and the construction-owned reduced
classical code.  The two exact constants are `5` and `3`, hence the final
binary CSS chain complex has check weight and qubit participation at most `8`.

The named coordinate types below keep Lean from eagerly unfolding the full
random Tanner/fiber index expressions while checking theorem signatures.
They are definitionally the construction-owned types used by
`HHO20DistanceBalancing.balancedData`.
-/

namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing

open QEC.Coding

def LocalityMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Type :=
  MainCZero baseSample twistSample

def LocalityMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Type :=
  MainQubit baseSample twistSample

def LocalityMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Type :=
  MainCTwo baseSample twistSample

noncomputable instance instFintypeLocalityMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Fintype (LocalityMainCZero baseSample twistSample) := by
  unfold LocalityMainCZero
  infer_instance

noncomputable instance instFintypeLocalityMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Fintype (LocalityMainQubit baseSample twistSample) := by
  unfold LocalityMainQubit
  infer_instance

noncomputable instance instFintypeLocalityMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Fintype (LocalityMainCTwo baseSample twistSample) := by
  unfold LocalityMainCTwo
  infer_instance

noncomputable instance instDecidableEqLocalityMainCZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (LocalityMainCZero baseSample twistSample) := Classical.decEq _

noncomputable instance instDecidableEqLocalityMainQubit
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (LocalityMainQubit baseSample twistSample) := Classical.decEq _

noncomputable instance instDecidableEqLocalityMainCTwo
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    DecidableEq (LocalityMainCTwo baseSample twistSample) := Classical.decEq _

/-- The HHO20 weight-reduced complex with non-eager coordinate names. -/
noncomputable def mainLocalityComplex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (LocalityMainCZero baseSample twistSample))
      (Word (ZMod 2) (LocalityMainQubit baseSample twistSample))
      (Word (ZMod 2) (LocalityMainCTwo baseSample twistSample)) :=
  mainComplex baseSample twistSample

/-- HHO20 weight reduction makes every main-complex check and physical-qubit
incidence have size at most five. -/
theorem mainLocalityComplex_bounded_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (mainLocalityComplex baseSample twistSample)).localityProfile 5 := by
  rw [← max_self 5]
  apply DistanceBalancing.boundedLocality_of_canonical_boundary_bounds
    (mainLocalityComplex baseSample twistSample)
      (checkBound := 5) (variableBound := 5)
  · intro c0
    change MainCZero baseSample twistSample at c0
    change HammingWeight
      (wordLinearMapTranspose
        (boundary1 (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample)))
        (canonicalBasisWord (F := ZMod 2) c0)) ≤ 5
    rcases c0 with ⟨q, i⟩
    exact
      RandomBase.HammingWeight_transpose_boundary1_weightReduced_randomFiberBundleData_canonical_le_five
        baseSample twistSample q i
  · intro c2
    change MainCTwo baseSample twistSample at c2
    change HammingWeight
      (boundary2 (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
        (canonicalBasisWord (F := ZMod 2) c2)) ≤ 5
    rcases c2 with ⟨b, j⟩
    exact
      RandomBase.HammingWeight_boundary2_weightReduced_randomFiberBundleData_canonical_le_five
        baseSample twistSample b j
  · intro q
    change MainQubit baseSample twistSample at q
    change ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample)))).variableSupport q).card ≤ 5
    exact
      RandomBase.chainComplexBoundaryIncidence_weightReduced_randomFiberBundleData_variableSupport_le_five
        baseSample twistSample q

/-- The final construction-owned distance-balanced complex, with named
coordinates used to keep its public locality statement lightweight. -/
noncomputable def balancedLocalityComplex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :=
  DistanceBalancing.chainComplex
    (DistanceBalancing.Data.ofComplexes
      (dualChainComplex (mainLocalityComplex baseSample twistSample))
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (RandomBase.incidenceRelation balanceSample)))

/-- The named final complex is definitionally the same EKZ product used by
the distance, dimension, and blocklength theorems. -/
theorem balancedLocalityComplex_eq
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    balancedLocalityComplex baseSample twistSample balanceSample =
      DistanceBalancing.chainComplex
        (balancedData baseSample twistSample balanceSample) := by
  classical
  rfl

/-- Exact constant qLDPC locality for the final HHO20--EKZ construction:
weight reduction contributes `5`, the classical balancing factor contributes
`3`, and the product bound adds them. -/
theorem balancedLocalityComplex_bounded_eight
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (balancedLocalityComplex
          baseSample twistSample balanceSample)).localityProfile 8 := by
  have hMain := mainLocalityComplex_bounded_five baseSample twistSample
  have hDual := DistanceBalancing.boundedLocality_dual
    (mainLocalityComplex baseSample twistSample) hMain
  have hProduct :=
    DistanceBalancing.boundedLocality_add_ofComplexes_of_source_bounded
      (dualChainComplex (mainLocalityComplex baseSample twistSample))
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (RandomBase.incidenceRelation balanceSample))
      hDual
      (RandomBase.weightReducedClassical_rowWeight_le_three balanceSample)
      (RandomBase.weightReducedClassical_columnWeight_le_three balanceSample)
  simpa [balancedLocalityComplex] using hProduct

end QEC.Coding.FiberBundle.HHO20DistanceBalancing
