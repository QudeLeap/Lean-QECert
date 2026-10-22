import QEC.Coding.FiberBundle.ExplicitFamily.InitialCode

/-!
# Logical dimension of the initial HHO20 bundle

The sampled base code has dimension `r` under the full-row-rank event.
Repeating a base codeword around every fiber one-cell embeds that code into
the kernel of the bundle's second boundary.  Rank-nullity and the exact cell
counts then give at least `r` independent middle-homology classes.
-/

namespace QEC.Coding.FiberBundle

namespace RandomBase

/-- A full-row-rank HHO20 base has the advertised classical dimension `r`. -/
theorem dimension_code_eq
    {r : Nat} (baseSample : Sample r)
    (hRank : HasFullRowRank baseSample) :
    Dimension (code baseSample) = r := by
  let P := Matrix.toLin' (boundary baseSample)
  have hRange : LinearMap.range P = ⊤ :=
    LinearMap.range_eq_top.mpr hRank
  have hRankNullity := P.finrank_range_add_finrank_ker
  have hSource :
      Module.finrank (ZMod 2)
          (Word (ZMod 2) (Fin (4 * r))) = 4 * r := by
    simp
  change Module.finrank (ZMod 2) (LinearMap.ker P) = r
  rw [hRange, finrank_top, finrank_word_eq_length] at hRankNullity
  simp only [Length, Fintype.card_fin] at hRankNullity
  rw [hSource] at hRankNullity
  omega

end RandomBase

/-- Constant-fiber extension sends every sampled-base codeword to a bundle
two-cycle. -/
noncomputable def constantFiberTwoCycleLinearMap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    (RandomBase.code baseSample).carrier →ₗ[ZMod 2]
      LinearMap.ker
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)) where
  toFun x := by
    refine ⟨constantFiberTwoChain
      (fiberOne := ZMod (ell * ell)) x.1, ?_⟩
    change boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (constantFiberTwoChain
        (fiberOne := ZMod (ell * ell)) x.1) = 0
    rw [boundary2_constantFiberTwoChain_eq_verticalFundamentalWord]
    have hx :
        Matrix.toLin' (RandomBase.boundary baseSample) x.1 = 0 := by
      exact (mem_parityCheckKernelCode
        (Matrix.toLin' (RandomBase.boundary baseSample)) x.1).mp x.2
    rw [hx]
    funext q
    rcases q with bi | aj
    · rfl
    · rfl
  map_add' x y := by
    ext bj
    rfl
  map_smul' coefficient x := by
    ext bj
    rfl

/-- The constant-fiber two-cycle embedding remembers the base codeword. -/
theorem constantFiberTwoCycleLinearMap_injective
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Function.Injective
      (constantFiberTwoCycleLinearMap baseSample twistSample) := by
  intro x y hxy
  apply Subtype.ext
  funext b
  have h := congrFun (congrArg Subtype.val hxy)
    (b, (0 : ZMod (ell * ell)))
  exact h

/-- The kernel of the second bundle boundary contains an `r`-dimensional
constant-fiber sector. -/
theorem r_le_finrank_ker_boundary2
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (LinearMap.ker
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample))) := by
  calc
    r = Dimension (RandomBase.code baseSample) :=
      (RandomBase.dimension_code_eq baseSample hRank).symm
    _ = Module.finrank (ZMod 2)
        (RandomBase.code baseSample).carrier := rfl
    _ ≤ Module.finrank (ZMod 2)
        (LinearMap.ker
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample))) :=
      LinearMap.finrank_le_finrank_of_injective
        (constantFiberTwoCycleLinearMap_injective
          baseSample twistSample)

/-- The initial HHO20 fiber bundle encodes at least `r` logical qubits. -/
theorem r_le_finrank_middleHomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleHomology := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let K := chainComplex D
  have hBoundary1 :=
    K.boundary1.finrank_range_add_finrank_ker
  have hBoundary2 :=
    K.boundary2.finrank_range_add_finrank_ker
  have hRange1 :
      Module.finrank (ZMod 2) (LinearMap.range K.boundary1) ≤
        3 * r * (ell * ell) := by
    calc
      Module.finrank (ZMod 2) (LinearMap.range K.boundary1) ≤
          Module.finrank (ZMod 2)
            (Word (ZMod 2)
              (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :=
        Submodule.finrank_le _
      _ = 3 * r * (ell * ell) := by
        simp [C0Index]
  have hKer2 :
      r ≤ Module.finrank (ZMod 2) (LinearMap.ker K.boundary2) := by
    exact r_le_finrank_ker_boundary2 baseSample twistSample hRank
  have hCells1 :
      Module.finrank (ZMod 2)
          (Word (ZMod 2)
            (QubitIndex (Fin (3 * r)) (Fin (4 * r))
              (ZMod (ell * ell)) (ZMod (ell * ell)))) =
        7 * r * (ell * ell) := by
    rw [finrank_word_eq_length]
    exact card_hho20_qubitIndex r ell
  have hCells2 :
      Module.finrank (ZMod 2)
          (Word (ZMod 2)
            (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) =
        4 * r * (ell * ell) := by
    simp [C2Index]
  have hBoundaryLeCycle :
      Module.finrank (ZMod 2) (LinearMap.range K.boundary2) ≤
        Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) := by
    exact Submodule.finrank_mono K.middleBoundaryCode_le_middleCycleCode
  have hCellSum :
      7 * r * (ell * ell) =
        3 * r * (ell * ell) + 4 * r * (ell * ell) := by
    ring
  have hHomology :=
    K.finrank_middleHomology_eq
  change r ≤
    Module.finrank (ZMod 2) K.middleHomology
  rw [hHomology, Dimension_eq_finrank_carrier,
    Dimension_eq_finrank_carrier]
  change r ≤
    Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) -
      Module.finrank (ZMod 2) (LinearMap.range K.boundary2)
  change
      Module.finrank (ZMod 2) (LinearMap.range K.boundary1) +
        Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) =
        Module.finrank (ZMod 2)
          (Word (ZMod 2)
            (QubitIndex (Fin (3 * r)) (Fin (4 * r))
              (ZMod (ell * ell)) (ZMod (ell * ell))) ) at hBoundary1
  change
      Module.finrank (ZMod 2) (LinearMap.range K.boundary2) +
        Module.finrank (ZMod 2) (LinearMap.ker K.boundary2) =
        Module.finrank (ZMod 2)
          (Word (ZMod 2)
            (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) at hBoundary2
  rw [hCells1] at hBoundary1
  rw [hCells2] at hBoundary2
  omega

end QEC.Coding.FiberBundle
