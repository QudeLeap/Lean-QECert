import QEC.Coding.FiberBundle.CohomologyDistance

/-!
# Cohomology representatives for the HHO20 circle bundle

This module formalizes the representative theorem used before HHO20,
Lemma `cohomweight`: every nontrivial degree-one cohomology class of the
circle bundle is a lifted nontrivial base class plus a bundle coboundary.

The first step is an explicit primitive for every even-parity cochain on the
cycle fiber.  It avoids accepting exactness of the cycle complex as input.
-/

namespace QEC.Coding.FiberBundle

universe u

/-- The standard finite representative is the corresponding natural cast. -/
theorem zmodFinEquiv_apply
    (n : Nat) [NeZero n] (k : Fin n) :
    ZMod.finEquiv n k = (k.val : ZMod n) := by
  apply ZMod.val_injective n
  rw [ZMod.val_natCast_of_lt k.isLt]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/--
The prefix-sum primitive of a cochain on the explicit cyclic ordering
`0, ..., n - 1`.
-/
def cycleFiberPrimitive
    (n : Nat) [NeZero n]
    (g : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun j => ∑ k ∈ Finset.range j.val, g (k : ZMod n)

/--
Every zero-parity binary cochain on a nondegenerate cycle is the coboundary
of its explicit prefix-sum primitive.
-/
theorem cycleFiberCoboundary_cycleFiberPrimitive
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n))
    (hg : (∑ j : ZMod n, g j) = 0) :
    cycleFiberCoboundary n (cycleFiberPrimitive n g) = g := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have honeVal : (1 : ZMod n).val = 1 := by
    exact ZMod.val_one n
  funext j
  rw [cycleFiberCoboundary_apply n hn]
  by_cases hnext : j.val + 1 < n
  · have hval : (j + 1).val = j.val + 1 := by
      rw [ZMod.val_add_of_lt]
      · rw [honeVal]
      · simpa [honeVal] using hnext
    have hjCast : (j.val : ZMod n) = j := by
      exact ZMod.natCast_zmod_val j
    rw [cycleFiberPrimitive, cycleFiberPrimitive, hval,
      Finset.sum_range_succ, hjCast]
    let a := ∑ k ∈ Finset.range j.val, g (k : ZMod n)
    change a + (a + g j) = g j
    have haa : a + a = 0 := by
      calc
        a + a = a + (-a) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel a
    calc
      a + (a + g j) = (a + a) + g j := by abel
      _ = g j := by rw [haa, zero_add]
  · have hjLast : j.val + 1 = n := by
      have hjLt : j.val < n := j.val_lt
      omega
    have hval : (j + 1).val = 0 := by
      rw [ZMod.val_add]
      rw [honeVal]
      rw [hjLast, Nat.mod_self]
    have hjCast : (j.val : ZMod n) = j := by
      exact ZMod.natCast_zmod_val j
    have hsumRange :
        (∑ k ∈ Finset.range n, g (k : ZMod n)) =
          ∑ z : ZMod n, g z := by
      calc
        (∑ k ∈ Finset.range n, g (k : ZMod n)) =
            ∑ k : Fin n, g (k.val : ZMod n) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          simp [Finset.mem_range.mp hk]
        _ = ∑ z : ZMod n, g z := by
          apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
          intro k
          change g (k.val : ZMod n) = g (ZMod.finEquiv n k)
          rw [zmodFinEquiv_apply]
    have hprefix :
        (∑ k ∈ Finset.range j.val, g (k : ZMod n)) = g j := by
      have hrangeSucc :
          (∑ k ∈ Finset.range j.val, g (k : ZMod n)) + g j =
            ∑ k ∈ Finset.range (j.val + 1), g (k : ZMod n) := by
        rw [Finset.sum_range_succ, hjCast]
      have htotal :
          (∑ k ∈ Finset.range j.val, g (k : ZMod n)) + g j = 0 := by
        rw [hrangeSucc, hjLast, hsumRange, hg]
      calc
        (∑ k ∈ Finset.range j.val, g (k : ZMod n)) =
            -g j := eq_neg_of_add_eq_zero_left htotal
        _ = g j := ZMod.neg_eq_self_mod_two _
    rw [cycleFiberPrimitive, cycleFiberPrimitive, hval, hprefix]
    rw [Finset.sum_range_zero, add_zero]

/-- Zero parity is exactly the image condition for the cycle coboundary. -/
theorem exists_cycleFiberPrimitive_iff_sum_eq_zero
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n)) :
    (∃ f, cycleFiberCoboundary n f = g) ↔
      (∑ j : ZMod n, g j) = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact sum_cycleFiberCoboundary_eq_zero n hn f
  · intro hg
    exact ⟨cycleFiberPrimitive n g,
      cycleFiberCoboundary_cycleFiberPrimitive n hn g hg⟩

/--
Full row rank lets a base one-chain isolate any selected base zero-cell.
-/
theorem exists_baseChain_boundary_eq_single
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (a : Fin (3 * r)) :
    ∃ c : Word (ZMod 2) (Fin (4 * r)),
      ∀ a' : Fin (3 * r),
        (∑ b : Fin (4 * r),
          c b * RandomBase.boundary baseSample a' b) =
            if a' = a then 1 else 0 := by
  let e : Word (ZMod 2) (Fin (3 * r)) :=
    fun a' => if a' = a then 1 else 0
  rcases hRank e with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro a'
  have hca := congrFun hc a'
  simp only [Matrix.toLin'_apply, Matrix.mulVec] at hca
  simpa [dotProduct, mul_comm] using hca

/-- The transpose of the second bundle boundary on a degree-one cochain. -/
noncomputable def bundleCocoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) (C2Index baseOne fiberOne) :=
  wordLinearMapTranspose (boundary2 D) z

/-- Coordinate formula for the transpose of the second bundle boundary. -/
theorem bundleCocoboundary_apply
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (bj : C2Index baseOne fiberOne) :
    bundleCocoboundary D z bj =
      ∑ q : QubitIndex baseZero baseOne fiberZero fiberOne,
        z q * boundary2Matrix D q bj := by
  classical
  unfold bundleCocoboundary wordLinearMapTranspose
  dsimp
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  simp [boundary2, Matrix.toLin'_apply, Matrix.mulVec]

/-- The cocycle equation split into horizontal and vertical bundle sectors. -/
theorem bundleCocoboundary_apply_eq_horizontal_add_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) (j : fiberOne) :
    bundleCocoboundary D z (b, j) =
      (∑ i : fiberZero,
        z (Sum.inl (b, i)) * D.fiberBoundary i j) +
      ∑ a : baseZero,
        z (Sum.inr (a, (D.connection b a).onOne j)) *
          D.baseBoundary a b := by
  classical
  rw [bundleCocoboundary_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply, mul_ite, mul_zero]
  simp

/-- Membership in the middle cocycle code is vanishing bundle cocoboundary. -/
theorem mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    z ∈ (chainComplex D).middleCocycleCode.carrier ↔
      bundleCocoboundary D z = 0 := by
  exact (chainComplex D).mem_middleCocycleCode_iff z

/--
After summing a bundle cocycle equation around the cycle fiber, the horizontal
term vanishes and the vertical fiber parities form a base cocycle equation.
-/
theorem sum_verticalFibers_mul_baseBoundary_eq_zero_of_cocycle
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (b : Fin (4 * r)) :
    (∑ a : Fin (3 * r),
      (∑ j : ZMod (ell * ell), verticalFiber z a j) *
        RandomBase.boundary baseSample a b) = 0 := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hzZero : bundleCocoboundary D z = 0 :=
    (mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero D z).mp hz
  have hEquation (j : ZMod (ell * ell)) :
      (∑ i : ZMod (ell * ell),
        z (Sum.inl (b, i)) * cycleBoundary (ell * ell) i j) +
      ∑ a : Fin (3 * r),
        z (Sum.inr (a, (D.connection b a).onOne j)) *
          RandomBase.boundary baseSample a b = 0 := by
    have hj := congrFun hzZero (b, j)
    rw [bundleCocoboundary_apply_eq_horizontal_add_vertical] at hj
    exact hj
  have hSummed :
      (∑ j : ZMod (ell * ell),
        ∑ i : ZMod (ell * ell),
          z (Sum.inl (b, i)) * cycleBoundary (ell * ell) i j) +
      (∑ j : ZMod (ell * ell),
        ∑ a : Fin (3 * r),
          z (Sum.inr (a, (D.connection b a).onOne j)) *
            RandomBase.boundary baseSample a b) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp only [hEquation, Finset.sum_const_zero]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hCycle : 2 ≤ ell * ell := by nlinarith
  have hHorizontal :
      (∑ j : ZMod (ell * ell),
        ∑ i : ZMod (ell * ell),
          z (Sum.inl (b, i)) * cycleBoundary (ell * ell) i j) = 0 := by
    exact sum_cycleFiberCoboundary_eq_zero
      (ell * ell) hCycle (horizontalFiber z b)
  rw [hHorizontal, zero_add] at hSummed
  calc
    (∑ a : Fin (3 * r),
        (∑ j : ZMod (ell * ell), verticalFiber z a j) *
          RandomBase.boundary baseSample a b) =
      ∑ j : ZMod (ell * ell),
        ∑ a : Fin (3 * r),
          z (Sum.inr (a, (D.connection b a).onOne j)) *
            RandomBase.boundary baseSample a b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Fintype.sum_equiv (D.connection b a).onOne.symm
      intro j
      simp [verticalFiber]
    _ = 0 := hSummed

/-- Full row rank forces every vertical fiber of a bundle cocycle to have even parity. -/
theorem sum_verticalFiber_eq_zero_of_cocycle
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (a : Fin (3 * r)) :
    (∑ j : ZMod (ell * ell), verticalFiber z a j) = 0 := by
  rcases exists_baseChain_boundary_eq_single baseSample hRank a with
    ⟨c, hc⟩
  let parity := fun a' : Fin (3 * r) =>
    ∑ j : ZMod (ell * ell), verticalFiber z a' j
  have hBase (b : Fin (4 * r)) :
      ∑ a' : Fin (3 * r),
        parity a' * RandomBase.boundary baseSample a' b = 0 :=
    sum_verticalFibers_mul_baseBoundary_eq_zero_of_cocycle
      baseSample twistSample z hz b
  have hWeighted :
      (∑ b : Fin (4 * r), c b *
        ∑ a' : Fin (3 * r),
          parity a' * RandomBase.boundary baseSample a' b) = 0 := by
    simp_rw [hBase, mul_zero]
    simp
  calc
    parity a =
        ∑ a' : Fin (3 * r),
          parity a' * (if a' = a then 1 else 0) := by simp
    _ = ∑ a' : Fin (3 * r),
          parity a' *
            (∑ b : Fin (4 * r),
              c b * RandomBase.boundary baseSample a' b) := by
        apply Finset.sum_congr rfl
        intro a' _
        rw [hc a']
    _ = ∑ b : Fin (4 * r), c b *
          ∑ a' : Fin (3 * r),
            parity a' * RandomBase.boundary baseSample a' b := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a' _
        ring
    _ = 0 := hWeighted

/-- Prefix-sum primitives for all vertical fibers of a degree-one word. -/
def verticalFiberPrimitiveWord
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))) :=
  fun ai => cycleFiberPrimitive (ell * ell) (verticalFiber z ai.1) ai.2

/--
For a cocycle over a full-row-rank base, the coboundary of the explicit
vertical primitives reproduces every vertical fiber exactly.
-/
theorem verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (a : Fin (3 * r)) :
    verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (verticalFiberPrimitiveWord z)) a =
      verticalFiber z a := by
  rw [verticalFiber_bundleCoboundary_fiberBundleData]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hCycle : 2 ≤ ell * ell := by nlinarith
  exact cycleFiberCoboundary_cycleFiberPrimitive
    (ell * ell) hCycle (verticalFiber z a)
    (sum_verticalFiber_eq_zero_of_cocycle
      baseSample twistSample hRank z hz a)

/-- Adding the primitive coboundary clears the entire vertical sector. -/
theorem verticalComponent_add_primitiveCoboundary_eq_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier) :
    verticalComponent
        (z +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (verticalFiberPrimitiveWord z)) = 0 := by
  funext aj
  rcases aj with ⟨a, j⟩
  change z (Sum.inr (a, j)) +
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample)
      (verticalFiberPrimitiveWord z) (Sum.inr (a, j)) = 0
  have hFiber :=
    congrFun
      (verticalFiber_bundleCoboundary_verticalFiberPrimitiveWord
        baseSample twistSample hRank z hz a) j
  change
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample)
      (verticalFiberPrimitiveWord z) (Sum.inr (a, j)) =
        z (Sum.inr (a, j)) at hFiber
  rw [hFiber]
  calc
    z (Sum.inr (a, j)) + z (Sum.inr (a, j)) =
        z (Sum.inr (a, j)) + (-z (Sum.inr (a, j))) := by
      rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel _

/--
After clearing its vertical fibers, a bundle cocycle is exactly the
all-one-fiber lift of one base one-cochain.
-/
theorem exists_add_primitiveCoboundary_eq_horizontalBaseLift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      z +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (verticalFiberPrimitiveWord z) =
        horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let u := verticalFiberPrimitiveWord z
  let cleared := z + bundleCoboundary D u
  have hzCleared :
      cleared ∈ (chainComplex D).middleCocycleCode.carrier := by
    exact
      (add_bundleCoboundary_mem_middleCocycleCode_iff D z u).mpr hz
  have hCocycleZero : bundleCocoboundary D cleared = 0 :=
    (mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero D cleared).mp
      hzCleared
  have hVertical : verticalComponent cleared = 0 := by
    exact verticalComponent_add_primitiveCoboundary_eq_zero
      baseSample twistSample hRank z hz
  let x : Word (ZMod 2) (Fin (4 * r)) :=
    fun b => horizontalFiber cleared b 0
  refine ⟨x, ?_⟩
  funext q
  rcases q with ⟨bi⟩ | ⟨aj⟩
  · rcases bi with ⟨b, i⟩
    have hHorizontalCoboundary :
        cycleFiberCoboundary (ell * ell)
          (horizontalFiber cleared b) = 0 := by
      funext j
      have hj := congrFun hCocycleZero (b, j)
      rw [bundleCocoboundary_apply_eq_horizontal_add_vertical] at hj
      have hVerticalSum :
          (∑ a : Fin (3 * r),
            cleared (Sum.inr (a, (D.connection b a).onOne j)) *
              D.baseBoundary a b) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have ha := congrFun hVertical
          (a, (D.connection b a).onOne j)
        change cleared
          (Sum.inr (a, (D.connection b a).onOne j)) = 0 at ha
        rw [ha, zero_mul]
      rw [hVerticalSum, add_zero] at hj
      exact hj
    have hEll : 2 ≤ ell := by
      have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
      omega
    have hCycle : 2 ≤ ell * ell := by nlinarith
    have hConstant :=
      cycleFiberCoboundary_eq_zero_implies_constant
        (ell * ell) hCycle (horizontalFiber cleared b)
        hHorizontalCoboundary i
    exact hConstant
  · rcases aj with ⟨a, j⟩
    have haj := congrFun hVertical (a, j)
    exact haj

/--
Concrete representative form from HHO20 Proposition `prop:cohorep`: every
bundle cocycle over a full-row-rank base is a lifted base cochain plus an
explicit bundle coboundary.
-/
theorem exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
        z =
          horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u := by
  let u := verticalFiberPrimitiveWord z
  rcases exists_add_primitiveCoboundary_eq_horizontalBaseLift
      baseSample twistSample hRank z hz with ⟨x, hCleared⟩
  refine ⟨x, u, ?_⟩
  rw [← hCleared]
  funext q
  change z q = (z q + bundleCoboundary
    (RandomTwist.fiberBundleData baseSample twistSample) u q) +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u q
  let w :=
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample) u q
  have hww : w + w = 0 := by
    calc
      w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel w
  calc
    z q = z q + 0 := by rw [add_zero]
    _ = (z q + w) + w := by rw [add_assoc, hww, add_zero]

/-- A degree-zero bundle word constant along every fiber. -/
def constantFiberWord
    {baseZero fiberZero : Type u}
    (t : Word (ZMod 2) baseZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => t ai.1

/--
The bundle coboundary of a constant-fiber word is exactly the lift of the
ordinary base coboundary.
-/
theorem bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (constantFiberWord
          (fiberZero := ZMod (ell * ell)) t) =
      horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (baseCoboundary baseSample t) := by
  funext q
  rcases q with ⟨bi⟩ | ⟨aj⟩
  · rcases bi with ⟨b, i⟩
    change
      horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (constantFiberWord
              (fiberZero := ZMod (ell * ell)) t)) b i =
        baseCoboundary baseSample t b
    rw [horizontalFiber_bundleCoboundary]
    simp only [constantFiberWord, RandomTwist.fiberBundleData,
      multipleRotationCycleData, cycleData, RandomBase.boundary,
      baseCoboundary]
  · rcases aj with ⟨a, j⟩
    change
      verticalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (constantFiberWord
              (fiberZero := ZMod (ell * ell)) t)) a j = 0
    rw [verticalFiber_bundleCoboundary_fiberBundleData]
    have hEll : 2 ≤ ell := by
      have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
      omega
    have hCycle : 2 ≤ ell * ell := by nlinarith
    rw [cycleFiberCoboundary_apply (ell * ell) hCycle]
    change t a + t a = 0
    calc
      t a + t a = t a + (-t a) := by
        rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel _

/--
The lifted base cochain in the representative decomposition is nontrivial
whenever the original bundle cocycle is not a bundle coboundary.
-/
theorem isNontrivialBaseCohomology_of_decomposition
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hDecomposition :
      z =
        horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).firstCoboundaryCheckCode.carrier) :
    IsNontrivialBaseCohomology baseSample x := by
  intro t hxt
  apply hzNontrivial
  rw [hDecomposition, hxt,
    ← bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
      baseSample twistSample t]
  rw [ChainComplexData.mem_firstCoboundaryCheckCode_iff]
  refine ⟨constantFiberWord
      (fiberZero := ZMod (ell * ell)) t + u, ?_⟩
  exact map_add
    (wordLinearMapTranspose
      (boundary1
        (RandomTwist.fiberBundleData baseSample twistSample)))
    (constantFiberWord (fiberZero := ZMod (ell * ell)) t) u

/--
Complete source-form representative theorem: every nontrivial bundle
cohomology representative over a full-row-rank base is a lifted nontrivial
base cohomology representative plus a bundle coboundary.
-/
theorem exists_nontrivial_horizontalBaseLift_add_bundleCoboundary_eq
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).firstCoboundaryCheckCode.carrier) :
    ∃ x : Word (ZMod 2) (Fin (4 * r)),
      IsNontrivialBaseCohomology baseSample x ∧
      ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
        z =
          horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u := by
  rcases exists_horizontalBaseLift_add_bundleCoboundary_eq_of_cocycle
      baseSample twistSample hRank z hz with ⟨x, u, hDecomposition⟩
  refine ⟨x, ?_, u, hDecomposition⟩
  exact isNontrivialBaseCohomology_of_decomposition
    baseSample twistSample z x u hDecomposition hzNontrivial

/--
Universal HHO20 cohomology-weight alternative for every nontrivial bundle
cocycle, with all integer constants explicit.
-/
theorem cohomologyWeightAlternative
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).firstCoboundaryCheckCode.carrier) :
    Fintype.card (ZMod (ell * ell)) ≤ 2 * HammingWeight z ∨
      6 * r < 100000 * Delta * HammingWeight z := by
  rcases exists_nontrivial_horizontalBaseLift_add_bundleCoboundary_eq
      baseSample twistSample hRank z hz hzNontrivial with
    ⟨x, hx, u, hDecomposition⟩
  have hBound :=
    weight_bound_for_all_corrections_of_nontrivial_base
      baseSample twistSample x hx hDelta hDegree hExpansion u
  simpa only [← hDecomposition] using hBound

/--
The cohomology-weight alternative implies any numerical lower bound lying
below both explicit scales.
-/
theorem cohomologyDistanceAtLeast_of_numeric_bounds
    {r typeCount ell Delta d : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hFiber : 2 * d ≤ Fintype.card (ZMod (ell * ell)))
    (hBase : 100000 * Delta * d ≤ 6 * r) :
    CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d := by
  intro z hz hzNontrivial
  rcases cohomologyWeightAlternative
      baseSample twistSample hRank hDelta hDegree hExpansion
      z hz hzNontrivial with hFiberWeight | hBaseWeight
  · omega
  · have hCoefficient : 0 < 100000 * Delta := by omega
    have hScaled :
        100000 * Delta * d <
          100000 * Delta * HammingWeight z :=
      hBase.trans_lt hBaseWeight
    have hdlt : d < HammingWeight z := by
      exact (Nat.mul_lt_mul_left hCoefficient).mp hScaled
    exact hdlt.le

/--
Explicit cohomology-distance lower bound at the minimum of the half-fiber
scale and the inverse-degree base scale.
-/
theorem cohomologyDistanceAtLeast_explicit
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample) :
    CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample)
      (min
        (Fintype.card (ZMod (ell * ell)) / 2)
        ((6 * r) / (100000 * Delta))) := by
  apply cohomologyDistanceAtLeast_of_numeric_bounds
    baseSample twistSample hRank hDelta hDegree hExpansion
  · calc
      2 * min
          (Fintype.card (ZMod (ell * ell)) / 2)
          ((6 * r) / (100000 * Delta)) ≤
        2 * (Fintype.card (ZMod (ell * ell)) / 2) := by
          exact Nat.mul_le_mul_left 2 (min_le_left _ _)
      _ ≤ Fintype.card (ZMod (ell * ell)) := Nat.mul_div_le _ _
  · calc
      100000 * Delta *
          min
            (Fintype.card (ZMod (ell * ell)) / 2)
            ((6 * r) / (100000 * Delta)) ≤
        100000 * Delta * ((6 * r) / (100000 * Delta)) := by
          exact Nat.mul_le_mul_left _ (min_le_right _ _)
      _ ≤ 6 * r := Nat.mul_div_le _ _

end QEC.Coding.FiberBundle
