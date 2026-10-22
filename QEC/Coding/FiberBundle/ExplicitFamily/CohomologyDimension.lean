import QEC.Coding.FiberBundle.ExplicitFamily.HomologyDimension

/-!
# Cohomological dimension of the initial HHO20 bundle

This module identifies the missing upper bound on the number of logical
qubits.  Base one-cochains lift to bundle cocycles, base coboundaries lift to
bundle coboundaries, and the representative theorem makes the induced map on
cohomology surjective.
-/

namespace QEC.Coding.FiberBundle

universe u

/-- Every all-one horizontal lift is a bundle cocycle. -/
theorem horizontalBaseLift_mem_middleCocycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier := by
  rw [mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero]
  funext bj
  rcases bj with ⟨b, j⟩
  rw [bundleCocoboundary_apply_eq_horizontal_add_vertical]
  simp only [horizontalBaseLift, zero_mul, Finset.sum_const_zero, add_zero,
    RandomTwist.fiberBundleData, multipleRotationCycleData, cycleData]
  rw [← Finset.mul_sum]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  let f : Word (ZMod 2) (ZMod (ell * ell)) := fun _ => 1
  change x b * (∑ i : ZMod (ell * ell), cycleBoundary (ell * ell) i j) = 0
  have hParity :
      (∑ i : ZMod (ell * ell), cycleBoundary (ell * ell) i j) = 0 := by
    calc
      (∑ i : ZMod (ell * ell), cycleBoundary (ell * ell) i j) =
          cycleFiberCoboundary (ell * ell) f j := by
        simp [cycleFiberCoboundary, f]
      _ = 0 := by
        rw [cycleFiberCoboundary_apply (ell * ell) (by nlinarith)]
        change (1 + 1 : ZMod 2) = 0
        rw [one_add_one_eq_two]
        exact ZMod.natCast_self 2
  rw [hParity, mul_zero]

/-- The project transpose of the sampled base boundary is the ordinary base
coboundary used in the HHO20 representative argument. -/
theorem wordLinearMapTranspose_randomBase_boundary
    {r : Nat} (baseSample : RandomBase.Sample r)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample)) t =
      baseCoboundary baseSample t := by
  classical
  funext b
  have htranspose {ι κ : Type} [Fintype ι] [Fintype κ]
      (A : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
      (y : Word (ZMod 2) κ) (i : ι) :
      wordLinearMapTranspose A y i = ∑ k : κ, y k * A (Pi.single i 1) k := by
    rw [wordLinearMapTranspose]
    rfl
  rw [htranspose]
  unfold baseCoboundary
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single b]
  · simp
  · intro b' hne
    simp [hne]

/-- Full row rank of the base boundary makes its transpose injective. -/
theorem wordLinearMapTranspose_randomBase_boundary_injective
    {r : Nat} (baseSample : RandomBase.Sample r)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Function.Injective
      (wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample))) := by
  intro t u htu
  have hzero :
      wordLinearMapTranspose
          (Matrix.toLin' (RandomBase.boundary baseSample)) (t - u) = 0 := by
    rw [map_sub, htu, sub_self]
  have hsub : t - u = 0 := by
    apply (wordPairing_nondegenerate
      (F := ZMod 2) (ι := Fin (3 * r))).left
    intro y
    rcases hRank y with ⟨x, rfl⟩
    rw [← wordPairing_wordLinearMapTranspose, hzero]
    simp
  exact sub_eq_zero.mp hsub

/-- Base cohomology is the base one-cochain space modulo sampled base
coboundaries. -/
noncomputable abbrev HHO20BaseCohomology
    {r : Nat} (baseSample : RandomBase.Sample r) :=
  Word (ZMod 2) (Fin (4 * r)) ⧸
    LinearMap.range
      (wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample)))

/-- A full-row-rank sampled base has first-cohomology dimension exactly `r`. -/
theorem finrank_hho20BaseCohomology_eq
    {r : Nat} (baseSample : RandomBase.Sample r)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Module.finrank (ZMod 2) (HHO20BaseCohomology baseSample) = r := by
  let T := wordLinearMapTranspose
    (Matrix.toLin' (RandomBase.boundary baseSample))
  have hTInjective : Function.Injective T :=
    wordLinearMapTranspose_randomBase_boundary_injective baseSample hRank
  have hRankNullity := T.finrank_range_add_finrank_ker
  have hKer : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr hTInjective
  have hDomain :
      Module.finrank (ZMod 2)
        (Word (ZMod 2) (Fin (3 * r))) = 3 * r := by simp
  have hRange :
      Module.finrank (ZMod 2) (LinearMap.range T) = 3 * r := by
    rw [hKer, finrank_bot] at hRankNullity
    omega
  have hQuotient :=
    (LinearMap.range T).finrank_quotient_add_finrank
  change Module.finrank (ZMod 2)
      (Word (ZMod 2) (Fin (4 * r)) ⧸ LinearMap.range T) = r
  have hAmbient :
      Module.finrank (ZMod 2)
        (Word (ZMod 2) (Fin (4 * r))) = 4 * r := by simp
  rw [hRange, hAmbient] at hQuotient
  omega

/-- Horizontal lifting, with its cocycle proof bundled into the codomain. -/
noncomputable def horizontalBaseLiftCocycleLinearMap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Word (ZMod 2) (Fin (4 * r)) →ₗ[ZMod 2]
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier where
  toFun x := ⟨horizontalBaseLift
      (baseZero := Fin (3 * r))
      (fiberZero := ZMod (ell * ell))
      (fiberOne := ZMod (ell * ell)) x,
    horizontalBaseLift_mem_middleCocycleCode
      baseSample twistSample x⟩
  map_add' x y := by
    apply Subtype.ext
    exact horizontalBaseLift_add x y
  map_smul' coefficient x := by
    apply Subtype.ext
    funext q
    rcases q with bi | aj
    · rfl
    · rfl

/-- The representative map from base cochains to bundle cohomology. -/
noncomputable def baseCochainToBundleCohomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Word (ZMod 2) (Fin (4 * r)) →ₗ[ZMod 2]
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCohomology :=
  let K := chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
  K.middleCoboundaryInCocycles.mkQ.comp
    (horizontalBaseLiftCocycleLinearMap baseSample twistSample)

/-- Sampled base coboundaries vanish under the bundle-cohomology map. -/
theorem baseCoboundaryRange_le_ker_baseCochainToBundleCohomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    LinearMap.range
        (wordLinearMapTranspose
          (Matrix.toLin' (RandomBase.boundary baseSample))) ≤
      LinearMap.ker
        (baseCochainToBundleCohomology baseSample twistSample) := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  rw [LinearMap.mem_ker]
  change
    (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleCoboundaryInCocycles.mkQ
      (horizontalBaseLiftCocycleLinearMap baseSample twistSample
        (wordLinearMapTranspose
          (Matrix.toLin' (RandomBase.boundary baseSample)) t)) = 0
  rw [wordLinearMapTranspose_randomBase_boundary]
  change
    (horizontalBaseLiftCocycleLinearMap baseSample twistSample
      (baseCoboundary baseSample t)) ∈
      LinearMap.ker
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleCoboundaryInCocycles.mkQ
  rw [Submodule.ker_mkQ]
  change horizontalBaseLift
      (baseZero := Fin (3 * r))
      (fiberZero := ZMod (ell * ell))
      (fiberOne := ZMod (ell * ell))
      (baseCoboundary baseSample t) ∈
    (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).firstCoboundaryCheckCode.carrier
  rw [← bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
    baseSample twistSample t]
  exact bundleCoboundary_mem_firstCoboundaryCheckCode
    (RandomTwist.fiberBundleData baseSample twistSample)
    (constantFiberWord (fiberZero := ZMod (ell * ell)) t)

/-- The horizontal lift descends from base cohomology to bundle cohomology. -/
noncomputable def baseCohomologyToBundleCohomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    HHO20BaseCohomology baseSample →ₗ[ZMod 2]
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCohomology :=
  (LinearMap.range
    (wordLinearMapTranspose
      (Matrix.toLin' (RandomBase.boundary baseSample)))).liftQ
    (baseCochainToBundleCohomology baseSample twistSample)
    (baseCoboundaryRange_le_ker_baseCochainToBundleCohomology
      baseSample twistSample)

/-- The HHO20 cocycle representative theorem makes the induced base-to-bundle
cohomology map surjective. -/
theorem baseCohomologyToBundleCohomology_surjective
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Function.Surjective
      (baseCohomologyToBundleCohomology baseSample twistSample) := by
  intro zClass
  let K := chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
  obtain ⟨z, rfl⟩ := K.middleCoboundaryInCocycles.mkQ_surjective zClass
  rcases exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
      baseSample twistSample hRank z.1 z.2 with
    ⟨x, u, hDecomposition⟩
  refine ⟨(LinearMap.range
      (wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample)))).mkQ x, ?_⟩
  change
    K.middleCoboundaryInCocycles.mkQ
        (horizontalBaseLiftCocycleLinearMap baseSample twistSample x) =
      K.middleCoboundaryInCocycles.mkQ z
  apply (Submodule.Quotient.eq K.middleCoboundaryInCocycles).mpr
  change
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x - z.1 ∈
      K.firstCoboundaryCheckCode.carrier
  have hDifference :
      horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x - z.1 =
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u := by
    rw [hDecomposition]
    funext q
    change horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x q -
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x q +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u q) =
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u q
    rw [sub_eq_add_neg, neg_add_rev]
    simp only [ZMod.neg_eq_self_mod_two]
    have hdouble :
        horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x q +
          horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x q = 0 := by
      calc
        _ = horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x q +
            (-horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    calc
      _ = (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x q +
            horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x q) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u q := by
        abel
      _ = _ := by rw [hdouble, zero_add]
  rw [hDifference]
  exact bundleCoboundary_mem_firstCoboundaryCheckCode
    (RandomTwist.fiberBundleData baseSample twistSample) u

/-- For a finite binary chain complex, middle cohomology and middle homology
have the same dimension. -/
theorem finrank_middleCohomology_eq_middleHomology
    {ι κ lambda : Type u} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    Module.finrank (ZMod 2) K.middleCohomology =
      Module.finrank (ZMod 2) K.middleHomology := by
  have hQuotient :=
    K.middleCoboundaryInCocycles.finrank_quotient_add_finrank
  have hDenominator :
      Module.finrank (ZMod 2) K.middleCoboundaryInCocycles =
        Dimension K.firstCoboundaryCheckCode := by
    rw [Dimension_eq_finrank_carrier]
    exact K.middleCoboundaryInCocyclesEquiv.finrank_eq
  have hCocycle :
      Module.finrank (ZMod 2) K.middleCocycleCode.carrier =
        Length (ZMod 2) ι - Dimension K.middleBoundaryCode := by
    calc
      Module.finrank (ZMod 2) K.middleCocycleCode.carrier =
          Dimension K.middleBoundaryCode.dual := by
        rw [Dimension_eq_finrank_carrier]
        rw [K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      _ = Length (ZMod 2) ι - Dimension K.middleBoundaryCode :=
        K.middleBoundaryCode.dual_dimension_eq_length_sub_dimension
  have hHomology :=
    K.length_sub_firstCoboundaryCheckCode_sub_middleBoundaryCode_eq_finrank_middleHomology
  rw [hDenominator, hCocycle] at hQuotient
  have hCohomology := Nat.eq_sub_of_add_eq hQuotient
  calc
    Module.finrank (ZMod 2) K.middleCohomology =
        (Length (ZMod 2) ι - Dimension K.middleBoundaryCode) -
          Dimension K.firstCoboundaryCheckCode := hCohomology
    _ = Length (ZMod 2) ι -
        (Dimension K.middleBoundaryCode +
          Dimension K.firstCoboundaryCheckCode) := by
      rw [Nat.sub_sub]
    _ = Length (ZMod 2) ι -
        (Dimension K.firstCoboundaryCheckCode +
          Dimension K.middleBoundaryCode) := by
      rw [Nat.add_comm]
    _ = (Length (ZMod 2) ι -
          Dimension K.firstCoboundaryCheckCode) -
        Dimension K.middleBoundaryCode := by
      rw [Nat.sub_sub]
    _ = Module.finrank (ZMod 2) K.middleHomology := hHomology

/-- Full row rank fixes the initial HHO20 bundle's logical dimension exactly
at `r`. -/
theorem finrank_middleHomology_eq_r
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    Module.finrank (ZMod 2)
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleHomology = r := by
  let K := chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
  change Module.finrank (ZMod 2) K.middleHomology = r
  have hUpper :
      Module.finrank (ZMod 2) K.middleCohomology ≤ r := by
    calc
      Module.finrank (ZMod 2) K.middleCohomology ≤
          Module.finrank (ZMod 2) (HHO20BaseCohomology baseSample) :=
        LinearMap.finrank_le_finrank_of_surjective
          (baseCohomologyToBundleCohomology_surjective
            baseSample twistSample hRank)
      _ = r := finrank_hho20BaseCohomology_eq baseSample hRank
  have hLower :
      r ≤ Module.finrank (ZMod 2) K.middleHomology :=
    r_le_finrank_middleHomology baseSample twistSample hRank
  rw [finrank_middleCohomology_eq_middleHomology K] at hUpper
  omega

end QEC.Coding.FiberBundle
