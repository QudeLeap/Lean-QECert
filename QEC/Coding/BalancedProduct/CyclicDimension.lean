import QEC.Coding.BalancedProduct.PKDistance

/-!
# Dimension of the cyclic lifted product

This file proves the dimension estimate used in the first Panteleev--Kalachev
almost-linear family.  The proof is independent of the Tanner matrix: the
binary cyclic difference `1+x` has one constant vector in its kernel on each
base coordinate, hence rank `|I|(q-1)`.  Its two occurrences in the lifted
product give rank lower bounds for both boundary maps.

No matrix-family, expansion, distance, or final code-parameter statement is
assumed here.
-/

namespace QEC.Coding.BalancedProduct.CyclicDimension

open QEC.Coding

universe u

/-- The binary action of the cyclic boundary element `1+x`. -/
def cyclicDifference (q : Nat) [NeZero q] (I : Type u) :
    Word (ZMod 2) (I × Unit × Cyclic.CyclicGroup q) →ₗ[ZMod 2]
      Word (ZMod 2) (I × Unit × Cyclic.CyclicGroup q) where
  toFun z p := z p + z (p.1, p.2.1, p.2.2 * (Cyclic.cyclicGenerator q)⁻¹)
  map_add' _ _ := by funext p; simp [add_assoc, add_left_comm]
  map_smul' _ _ := by funext p; simp [mul_add]

@[simp]
theorem cyclicDifference_apply
    (q : Nat) [NeZero q] (I : Type u)
    (z : Word (ZMod 2) (I × Unit × Cyclic.CyclicGroup q))
    (i : I) (g : Cyclic.CyclicGroup q) :
    cyclicDifference q I z (i, default, g) =
      z (i, default, g) +
        z (i, default, g * (Cyclic.cyclicGenerator q)⁻¹) := rfl

/-- A word on the base, extended constantly over every cyclic fibre. -/
def constantCyclicFibre (q : Nat) [NeZero q] (I : Type u) :
    Word (ZMod 2) I →ₗ[ZMod 2]
      Word (ZMod 2) (I × Unit × Cyclic.CyclicGroup q) where
  toFun z p := z p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem constantCyclicFibre_apply
    (q : Nat) [NeZero q] (I : Type u) (z : Word (ZMod 2) I)
    (i : I) (g : Cyclic.CyclicGroup q) :
    constantCyclicFibre q I z (i, default, g) = z i := rfl

/-- Evaluation of a cyclic word on the identity coordinate of every fibre. -/
def identityCyclicFibre (q : Nat) [NeZero q] (I : Type u) :
    Word (ZMod 2) (I × Unit × Cyclic.CyclicGroup q) →ₗ[ZMod 2]
      Word (ZMod 2) I where
  toFun z i := z (i, default, 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cyclicDifference_constantCyclicFibre
    (q : Nat) [NeZero q] (I : Type u) :
    (cyclicDifference q I).comp (constantCyclicFibre q I) = 0 := by
  ext z p
  rcases p with ⟨i, u, g⟩
  cases u
  change z i + z i = 0
  exact congrFun (PKDistance.binaryWord_add_self z) i

/-- The kernel of `1+x` consists exactly of the fibrewise constant words. -/
noncomputable def cyclicDifferenceKernelEquiv
    (q : Nat) [NeZero q] (I : Type u) :
    LinearMap.ker (cyclicDifference q I) ≃ₗ[ZMod 2] Word (ZMod 2) I where
  toFun z := identityCyclicFibre q I z.1
  invFun z := ⟨constantCyclicFibre q I z, by
    change cyclicDifference q I (constantCyclicFibre q I z) = 0
    exact LinearMap.congr_fun (cyclicDifference_constantCyclicFibre q I) z⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    apply Subtype.ext
    funext p
    rcases p with ⟨i, u, g⟩
    cases u
    let zflat : Word (ZMod 2) (I × Cyclic.CyclicGroup q) :=
      fun p => z.1 (p.1, default, p.2)
    have hzero : zflat +
        PKDistance.cyclicShift (Cyclic.cyclicGenerator q)
          zflat = 0 := by
      funext p
      rcases p with ⟨j, h⟩
      simpa [zflat, cyclicDifference, PKDistance.cyclicShift_apply] using
        congrFun z.2 (j, default, h)
    exact (PKDistance.cyclicInvariant_apply_eq q
      zflat hzero i g 1).symm
  right_inv z := by
    funext i
    rfl

theorem finrank_ker_cyclicDifference
    (q : Nat) [NeZero q] (I : Type u) [Fintype I] :
    Module.finrank (ZMod 2) (LinearMap.ker (cyclicDifference q I)) =
      Fintype.card I := by
  rw [(cyclicDifferenceKernelEquiv q I).finrank_eq]
  simp

/-- Exact rank of the cyclic difference on `|I|` disjoint `q`-cycles. -/
theorem finrank_range_cyclicDifference
    (q : Nat) [NeZero q] (I : Type u) [Fintype I] :
    Module.finrank (ZMod 2) (LinearMap.range (cyclicDifference q I)) =
      Fintype.card I * (q - 1) := by
  have hRankNullity := (cyclicDifference q I).finrank_range_add_finrank_ker
  rw [finrank_ker_cyclicDifference] at hRankNullity
  have hDomain : Module.finrank (ZMod 2)
      (Word (ZMod 2) (I × Unit × Cyclic.CyclicGroup q)) =
      Fintype.card I * q := by
    simp [Cyclic.CyclicGroup, ZMod.card]
  rw [hDomain] at hRankNullity
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqSplit : q = q - 1 + 1 := by omega
  have hProduct : Fintype.card I * q =
      Fintype.card I * (q - 1) + Fintype.card I := by
    conv_lhs => rw [hqSplit]
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The first lifted boundary contains the cyclic difference on its vertical
qubit block. -/
theorem cyclicDifference_eq_boundary1_comp_secondZeroExtension
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    cyclicDifference q aRow =
      (LiftedProduct.boundary1 (Cyclic.data q A)).comp
        (LiftedProduct.secondZeroExtension (Cyclic.data q A)) := by
  apply LinearMap.ext
  intro z
  funext p
  rcases p with ⟨r, u, g⟩
  have hu : u = () := Subsingleton.elim _ _
  subst u
  unfold Cyclic.data
  simpa [cyclicDifference, LiftedProduct.secondZeroExtension,
      PKDistance.horizontalPart, PKDistance.verticalPart,
      PKDistance.cyclicShift_apply] using
    (PKDistance.boundary1_eq_tannerAction_add_cyclicDifference
      A (Cyclic.cyclicGenerator q)
      (LiftedProduct.secondZeroExtension (Cyclic.data q A) z) r g).symm

/-- The second lifted boundary contains the cyclic difference on its
horizontal output block. -/
theorem cyclicDifference_eq_firstRestriction_comp_boundary2
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    cyclicDifference q aCol =
      (LiftedProduct.firstRestriction (Cyclic.data q A)).comp
        (LiftedProduct.boundary2 (Cyclic.data q A)) := by
  apply LinearMap.ext
  intro z
  funext p
  rcases p with ⟨c, u, g⟩
  have hu : u = () := Subsingleton.elim _ _
  subst u
  let h : Word (ZMod 2) (aCol × Cyclic.CyclicGroup q) :=
    fun p => z (p.1, (), p.2)
  have hz : z = PKDistance.primitiveTwoChain h := by
    funext p
    rcases p with ⟨c', u', g'⟩
    cases u'
    rfl
  rw [hz]
  unfold Cyclic.data
  simpa [cyclicDifference, h, LiftedProduct.firstRestriction,
      PKDistance.primitiveTwoChain] using
    (congrFun
      (PKDistance.horizontalPart_boundary2_primitiveTwoChain
        A (Cyclic.cyclicGenerator q) h) (c, g)).symm

/-- Rank lower bound for the first boundary, obtained from its vertical
cyclic block. -/
theorem boundary1_rank_lowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aRow * (q - 1) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (LiftedProduct.boundary1 (Cyclic.data q A))) := by
  rw [← finrank_range_cyclicDifference q aRow,
    cyclicDifference_eq_boundary1_comp_secondZeroExtension q A]
  exact Submodule.finrank_mono
    (LinearMap.range_comp_le_range
      (LiftedProduct.secondZeroExtension (Cyclic.data q A))
      (LiftedProduct.boundary1 (Cyclic.data q A)))

/-- Rank lower bound for the second boundary.  Postcomposition cannot raise
rank, so the visible horizontal cyclic block is a lower bound. -/
theorem boundary2_rank_lowerBound
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Fintype.card aCol * (q - 1) ≤
      Module.finrank (ZMod 2)
        (LinearMap.range (LiftedProduct.boundary2 (Cyclic.data q A))) := by
  rw [← finrank_range_cyclicDifference q aCol,
    cyclicDifference_eq_firstRestriction_comp_boundary2 q A]
  exact Module.finrank_le_finrank_of_rank_le_rank
    (LinearMap.lift_rank_comp_le_right
      (LiftedProduct.boundary2 (Cyclic.data q A))
      (LiftedProduct.firstRestriction (Cyclic.data q A)))
    (Module.rank_lt_aleph0 (ZMod 2)
      (LinearMap.range (LiftedProduct.boundary2 (Cyclic.data q A))))

/-- Tanner-matrix-independent upper bound on the number of encoded qubits in
the cyclic lifted product. -/
theorem finrank_middleHomology_le_card_add_card
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Module.finrank (ZMod 2)
        (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ≤
      Fintype.card aCol + Fintype.card aRow := by
  let D := Cyclic.data q A
  let K := LiftedProduct.chainComplex D
  have hBoundaryOne := boundary1_rank_lowerBound q A
  have hBoundaryTwo := boundary2_rank_lowerBound q A
  have hRankNullity := K.boundary1.finrank_range_add_finrank_ker
  have hMiddle : Module.finrank (ZMod 2)
      (Word (ZMod 2) (LiftedProduct.QubitIndex
        aRow aCol Unit Unit (Cyclic.CyclicGroup q))) =
      q * (Fintype.card aCol + Fintype.card aRow) := by
    simp [LiftedProduct.QubitIndex, Cyclic.CyclicGroup, ZMod.card,
      Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc]
  rw [hMiddle] at hRankNullity
  have hCycles : Dimension K.middleCycleCode =
      Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) := by
    rw [Dimension_eq_finrank_carrier]
    rfl
  have hBoundaries : Dimension K.middleBoundaryCode =
      Module.finrank (ZMod 2) (LinearMap.range K.boundary2) := by
    rw [Dimension_eq_finrank_carrier]
    rfl
  rw [K.finrank_middleHomology_eq, hCycles, hBoundaries]
  change _ ≤ Fintype.card aCol + Fintype.card aRow
  change Fintype.card aRow * (q - 1) ≤
    Module.finrank (ZMod 2) (LinearMap.range K.boundary1) at hBoundaryOne
  change Fintype.card aCol * (q - 1) ≤
    Module.finrank (ZMod 2) (LinearMap.range K.boundary2) at hBoundaryTwo
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqSplit : q = q - 1 + 1 := by omega
  have hDimensionSplit :
      q * (Fintype.card aCol + Fintype.card aRow) =
        Fintype.card aRow * (q - 1) +
          Fintype.card aCol * (q - 1) +
            (Fintype.card aCol + Fintype.card aRow) := by
    conv_lhs => rw [hqSplit]
    ring
  omega

end QEC.Coding.BalancedProduct.CyclicDimension
