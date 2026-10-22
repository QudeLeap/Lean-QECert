import QEC.Coding.FiberBundle.CohomologyRepresentatives
import QEC.Coding.FiberBundle.TwistGraph

/-!
# Homology representatives for the HHO20 circle bundle

This module formalizes the algebraic part of the bundle projection used in
HHO20 before Lemma `sliding`.  A bundle one-chain is projected to the base by
summing each horizontal fiber.  The proofs below derive its interaction with
the two bundle boundaries from their coordinate formulas.
-/

namespace QEC.Coding.FiberBundle

universe u

/-- Sum the horizontal fiber of a bundle one-chain over every base one-cell. -/
def homologyBaseProjection
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype fiberZero]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) baseOne :=
  fun b => ∑ i : fiberZero, horizontalFiber z b i

@[simp]
theorem homologyBaseProjection_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype fiberZero]
    (z z' : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    homologyBaseProjection (z + z') =
      homologyBaseProjection z + homologyBaseProjection z' := by
  funext b
  simp [homologyBaseProjection, horizontalFiber, Finset.sum_add_distrib]

/--
The horizontal fiber of a bundle two-boundary is the fiber boundary of the
corresponding two-chain fiber.
-/
theorem horizontalFiber_boundary2
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (c : Word (ZMod 2) (C2Index baseOne fiberOne))
    (b : baseOne) (i : fiberZero) :
    horizontalFiber (boundary2 D c) b i =
      ∑ j : fiberOne, D.fiberBoundary i j * c (b, j) := by
  classical
  rw [horizontalFiber, boundary2, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type]
  simp [boundary2Matrix]

/--
If every fiber one-cell has even boundary parity, the bundle projection kills
every total-degree-two boundary.
-/
theorem homologyBaseProjection_boundary2_eq_zero
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (hFiberParity : ∀ j : fiberOne, (∑ i : fiberZero,
      D.fiberBoundary i j) = 0)
    (c : Word (ZMod 2) (C2Index baseOne fiberOne)) :
    homologyBaseProjection (boundary2 D c) = 0 := by
  funext b
  simp only [homologyBaseProjection, horizontalFiber_boundary2]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _hj
  rw [← Finset.sum_mul]
  simp [hFiberParity j]

/-- The cycle fiber satisfies the parity condition used by bundle projection. -/
theorem homologyBaseProjection_boundary2_fiberBundleData_eq_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) :
    homologyBaseProjection
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample) c) = 0 := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  apply homologyBaseProjection_boundary2_eq_zero
  intro j
  let f : Word (ZMod 2) (ZMod (ell * ell)) := fun _ => 1
  change (∑ i : ZMod (ell * ell),
    cycleBoundary (ell * ell) i j) = 0
  calc
    _ = cycleFiberCoboundary (ell * ell) f j := by
      simp [cycleFiberCoboundary, f]
    _ = 0 := by
      rw [cycleFiberCoboundary_apply (ell * ell) (by nlinarith)]
      change (1 : ZMod 2) + 1 = 0
      rfl

/-- Coordinate formula for the first bundle boundary, split by cell sector. -/
theorem boundary1_apply_eq_horizontal_add_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) (i : fiberZero) :
    boundary1 D z (a, i) =
      (∑ b : baseOne,
        D.baseBoundary a b *
          z (Sum.inl (b, (D.connection b a).onZero.symm i))) +
      ∑ j : fiberOne, D.fiberBoundary i j * z (Sum.inr (a, j)) := by
  classical
  rw [boundary1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro b _hb
    rw [Finset.sum_eq_single ((D.connection b a).onZero.symm i)]
    · simp
    · intro j _hj hji
      simp only [boundary1Matrix_inl_apply]
      have hne : i ≠ (D.connection b a).onZero j := by
        intro h
        apply hji
        exact (D.connection b a).onZero.injective
          (by simpa using h.symm)
      simp [hne]
    · simp
  · rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ha' hne
      simp [Ne.symm hne]
    · simp

/--
Summing the bundle cycle equation over one complete fiber leaves exactly the
base boundary of the horizontal projection.
-/
theorem sum_boundary1_eq_baseBoundary_projection
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (hFiberParity : ∀ j : fiberOne, (∑ i : fiberZero,
      D.fiberBoundary i j) = 0)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) :
    (∑ i : fiberZero, boundary1 D z (a, i)) =
      ∑ b : baseOne,
        homologyBaseProjection z b * D.baseBoundary a b := by
  simp_rw [boundary1_apply_eq_horizontal_add_vertical]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hvertical :
      (∑ i : fiberZero,
        ∑ j : fiberOne,
          D.fiberBoundary i j * z (Sum.inr (a, j))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [← Finset.sum_mul]
    simp [hFiberParity j]
  rw [hvertical, add_zero]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [← Finset.mul_sum]
  have hsum :
      (∑ i : fiberZero,
        z (Sum.inl (b, (D.connection b a).onZero.symm i))) =
        ∑ i : fiberZero, horizontalFiber z b i := by
    apply Fintype.sum_equiv (D.connection b a).onZero.symm
    intro i
    rfl
  rw [hsum, mul_comm]
  rfl

/-- A bundle cycle projects to a cycle of the base complex. -/
theorem baseBoundary_projection_eq_zero_of_boundary1_eq_zero
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (hFiberParity : ∀ j : fiberOne, (∑ i : fiberZero,
      D.fiberBoundary i j) = 0)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (hz : boundary1 D z = 0)
    (a : baseZero) :
    (∑ b : baseOne,
      homologyBaseProjection z b * D.baseBoundary a b) = 0 := by
  rw [← sum_boundary1_eq_baseBoundary_projection D hFiberParity z a]
  simp [hz]

/-- Specialized cycle-projection equation for the sampled HHO20 bundle. -/
theorem randomBase_boundary_projection_eq_zero_of_bundleCycle
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
        ).middleCycleCode.carrier)
    (a : Fin (3 * r)) :
    (∑ b : Fin (4 * r),
      homologyBaseProjection z b *
        RandomBase.boundary baseSample a b) = 0 := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  apply baseBoundary_projection_eq_zero_of_boundary1_eq_zero
    (RandomTwist.fiberBundleData baseSample twistSample)
  · intro j
    let f : Word (ZMod 2) (ZMod (ell * ell)) := fun _ => 1
    change (∑ i : ZMod (ell * ell),
      cycleBoundary (ell * ell) i j) = 0
    calc
      _ = cycleFiberCoboundary (ell * ell) f j := by
        simp [cycleFiberCoboundary, f]
      _ = 0 := by
        rw [cycleFiberCoboundary_apply (ell * ell) (by nlinarith)]
        change (1 : ZMod 2) + 1 = 0
        rfl
  · exact ((chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).mem_middleCycleCode_iff z).1 hz

/--
A bundle one-boundary has zero base projection.  Consequently, a nonzero
projection is an explicit certificate that a bundle cycle is homologically
nontrivial.
-/
theorem not_mem_middleBoundaryCode_of_projection_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzProjection : homologyBaseProjection z ≠ 0) :
    z ∉ (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleBoundaryCode.carrier := by
  intro hzBoundary
  rcases ((chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
    ).mem_middleBoundaryCode_iff z).1 hzBoundary with ⟨c, rfl⟩
  exact hzProjection
    (homologyBaseProjection_boundary2_fiberBundleData_eq_zero
      baseSample twistSample c)

/-! ## Explicit chain primitives on the cycle fiber -/

/-- The cellular boundary of a chain on the explicit cycle fiber. -/
def cycleFiberChainBoundary
    (n : Nat) [NeZero n]
    (c : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun i => ∑ j : ZMod n, cycleBoundary n i j * c j

/-- A cycle chain boundary is the sum of the two incident edge coefficients. -/
theorem cycleFiberChainBoundary_apply
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (c : Word (ZMod 2) (ZMod n)) (i : ZMod n) :
    cycleFiberChainBoundary n c i = c i + c (i - 1) := by
  classical
  have hne : i ≠ i - 1 := by
    intro h
    have hzeroOne : (0 : ZMod n) = 1 := by
      simpa using congrArg (fun z => i - z) h
    have hone : (1 : ZMod n) ≠ 0 := by
      rw [ne_eq, ZMod.one_eq_zero_iff]
      omega
    exact hone hzeroOne.symm
  have hfilter :
      (Finset.univ.filter fun j : ZMod n => i = j ∨ i = j + 1) =
        {i, i - 1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · right
        apply add_right_cancel (b := (1 : ZMod n))
        simpa [sub_eq_add_neg, add_assoc] using h.symm
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · right
        simp
  rw [cycleFiberChainBoundary]
  simp_rw [cycleBoundary, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, hfilter]
  simp [hne]

/--
Shift the cochain prefix primitive once so that it is a primitive for the
chain boundary rather than the transpose coboundary.
-/
def cycleFiberChainPrimitive
    (n : Nat) [NeZero n]
    (g : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  cycleFiberPrimitive n (fun i => g (i + 1))

/-- Every even-parity cycle zero-chain has the explicit shifted primitive. -/
theorem cycleFiberChainBoundary_cycleFiberChainPrimitive
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (g : Word (ZMod 2) (ZMod n))
    (hg : (∑ i : ZMod n, g i) = 0) :
    cycleFiberChainBoundary n (cycleFiberChainPrimitive n g) = g := by
  have hshift : (∑ i : ZMod n, g (i + 1)) = ∑ i : ZMod n, g i := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
      (fun i => g (i + 1)) g (by intro i; rfl)
  have hprimitive :=
    cycleFiberCoboundary_cycleFiberPrimitive n hn
      (fun i => g (i + 1)) (by simpa [hshift] using hg)
  funext i
  rw [cycleFiberChainBoundary_apply n hn]
  have hi := congrFun hprimitive (i - 1)
  rw [cycleFiberCoboundary_apply n hn] at hi
  simpa [cycleFiberChainPrimitive, add_comm] using hi

/-! ## Clearing the horizontal sector of a zero-projection cycle -/

/-- Fiberwise chain primitives assembled into one total-degree-two word. -/
def horizontalFiberPrimitiveTwoChain
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))) := by
  letI : NeZero (ell * ell) :=
    ⟨Nat.mul_ne_zero (NeZero.ne ell) (NeZero.ne ell)⟩
  exact fun bj =>
    cycleFiberChainPrimitive (ell * ell)
      (horizontalFiber z bj.1) bj.2

/--
When the base projection vanishes, the boundary of the assembled primitives
reproduces every horizontal fiber exactly.
-/
theorem horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzProjection : homologyBaseProjection z = 0)
    (b : Fin (4 * r)) :
    horizontalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (horizontalFiberPrimitiveTwoChain z)) b =
      horizontalFiber z b := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  funext i
  rw [horizontalFiber_boundary2]
  simp only [RandomTwist.fiberBundleData, multipleRotationCycleData,
    cycleData]
  change cycleFiberChainBoundary (ell * ell)
    (cycleFiberChainPrimitive (ell * ell) (horizontalFiber z b)) i =
      horizontalFiber z b i
  apply congrFun
  apply cycleFiberChainBoundary_cycleFiberChainPrimitive
    (ell * ell) (by nlinarith)
  have hb := congrFun hzProjection b
  simpa [homologyBaseProjection] using hb

/-- Adding the explicit primitive boundary clears the full horizontal sector. -/
theorem horizontalFiber_add_primitiveBoundary_eq_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzProjection : homologyBaseProjection z = 0)
    (b : Fin (4 * r)) :
    horizontalFiber
        (z +
          boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (horizontalFiberPrimitiveTwoChain z)) b = 0 := by
  rw [show horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (horizontalFiberPrimitiveTwoChain z)) b =
      horizontalFiber z b +
        horizontalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (horizontalFiberPrimitiveTwoChain z)) b by rfl]
  rw [horizontalFiber_boundary2_horizontalFiberPrimitiveTwoChain
    baseSample twistSample z hzProjection b]
  funext i
  change horizontalFiber z b i + horizontalFiber z b i = 0
  calc
    horizontalFiber z b i + horizontalFiber z b i =
        horizontalFiber z b i + (-(horizontalFiber z b i)) := by
      rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel (horizontalFiber z b i)

/-! ## The remaining vertical fundamental cycles -/

/-- A cycle-fiber chain with zero cellular boundary is constant. -/
theorem cycleFiberChainBoundary_eq_zero_implies_constant
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (c : Word (ZMod 2) (ZMod n))
    (hc : cycleFiberChainBoundary n c = 0) :
    ∀ j, c j = c 0 := by
  have hcoboundary : cycleFiberCoboundary n c = 0 := by
    funext j
    rw [cycleFiberCoboundary_apply n hn]
    have hj := congrFun hc (j + 1)
    rw [cycleFiberChainBoundary_apply n hn] at hj
    simpa [add_comm] using hj
  exact cycleFiberCoboundary_eq_zero_implies_constant
    n hn c hcoboundary

/--
Once all horizontal fibers vanish, the bundle cycle equation says that every
remaining vertical fiber is a constant multiple of the fiber fundamental
cycle.
-/
theorem verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzCycle :
      boundary1
        (RandomTwist.fiberBundleData baseSample twistSample) z = 0)
    (hzHorizontal : ∀ b : Fin (4 * r), horizontalFiber z b = 0)
    (a : Fin (3 * r)) :
    ∀ j, verticalFiber z a j = verticalFiber z a 0 := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  apply cycleFiberChainBoundary_eq_zero_implies_constant
    (ell * ell) (by nlinarith)
  funext i
  have hi := congrFun hzCycle (a, i)
  rw [boundary1_apply_eq_horizontal_add_vertical] at hi
  have hHorizontalSum :
      (∑ b : Fin (4 * r),
        (RandomTwist.fiberBundleData baseSample twistSample).baseBoundary a b *
          z (Sum.inl (b,
            ((RandomTwist.fiberBundleData baseSample twistSample
              ).connection b a).onZero.symm i))) = 0 := by
    apply Finset.sum_eq_zero
    intro b _hb
    have hb := congrFun (hzHorizontal b)
      ((((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero.symm) i)
    change z (Sum.inl (b,
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero.symm i)) = 0 at hb
    rw [hb, mul_zero]
  rw [hHorizontalSum, zero_add] at hi
  change cycleFiberChainBoundary (ell * ell) (verticalFiber z a) i = 0
  exact hi

/-- The coefficient of the vertical fiber fundamental cycle over `a`. -/
def verticalFundamentalCoefficient
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Zero fiberOne]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) : ZMod 2 :=
  verticalFiber z a 0

/-- The pure-vertical word with constant coefficient on every fiber. -/
def verticalFundamentalWord
    {baseZero baseOne fiberZero fiberOne : Type u}
    (y : Word (ZMod 2) baseZero) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)
  | Sum.inl _ => 0
  | Sum.inr (a, _j) => y a

/-- A word with zero horizontal sector and constant vertical fibers is explicit. -/
theorem eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzHorizontal : ∀ b : Fin (4 * r), horizontalFiber z b = 0)
    (hzVertical : ∀ a : Fin (3 * r), ∀ j,
      verticalFiber z a j = verticalFiber z a 0) :
    z =
      verticalFundamentalWord
        (baseOne := Fin (4 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (verticalFundamentalCoefficient z) := by
  funext q
  rcases q with ⟨b, i⟩ | ⟨a, j⟩
  · have hi := congrFun (hzHorizontal b) i
    simpa [horizontalFiber, verticalFundamentalWord] using hi
  · exact hzVertical a j

/-- A base one-chain repeated constantly around every two-cell fiber. -/
def constantFiberTwoChain
    {baseOne fiberOne : Type u}
    (x : Word (ZMod 2) baseOne) :
    Word (ZMod 2) (C2Index baseOne fiberOne) :=
  fun bj => x bj.1

/-- Vertical coordinate formula for a general bundle two-boundary. -/
theorem boundary2_apply_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (c : Word (ZMod 2) (C2Index baseOne fiberOne))
    (a : baseZero) (j : fiberOne) :
    boundary2 D c (Sum.inr (a, j)) =
      ∑ b : baseOne,
        D.baseBoundary a b *
          c (b, (D.connection b a).onOne.symm j) := by
  classical
  rw [boundary2, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_eq_single ((D.connection b a).onOne.symm j)]
  · simp
  · intro k _hk hkj
    simp only [boundary2Matrix_inr_apply]
    have hcond : j ≠ (D.connection b a).onOne k := by
      intro h
      apply hkj
      have hh := congrArg (D.connection b a).onOne.symm h
      simpa only [Equiv.symm_apply_apply] using hh.symm
    simp [hcond]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/--
The boundary of a constant-fiber two-chain is the pure vertical fundamental
word whose coefficient vector is the ordinary sampled base boundary.
-/
theorem boundary2_constantFiberTwoChain_eq_verticalFundamentalWord
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    boundary2
        (RandomTwist.fiberBundleData baseSample twistSample)
        (constantFiberTwoChain
          (fiberOne := ZMod (ell * ell)) x) =
      verticalFundamentalWord
        (baseOne := Fin (4 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (Matrix.toLin' (RandomBase.boundary baseSample) x) := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  funext q
  rcases q with ⟨b, i⟩ | ⟨a, j⟩
  · change horizontalFiber
      (boundary2
        (RandomTwist.fiberBundleData baseSample twistSample)
        (constantFiberTwoChain
          (fiberOne := ZMod (ell * ell)) x)) b i = 0
    rw [horizontalFiber_boundary2]
    change cycleFiberChainBoundary (ell * ell)
      (fun _j => x b) i = 0
    rw [cycleFiberChainBoundary_apply (ell * ell) (by nlinarith)]
    calc
      x b + x b = x b + (-x b) := by
        rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel _
  · rw [boundary2_apply_vertical]
    simp only [constantFiberTwoChain, RandomTwist.fiberBundleData,
      multipleRotationCycleData, cycleData]
    change (∑ b : Fin (4 * r),
      RandomBase.boundary baseSample a b * x b) =
        Matrix.toLin' (RandomBase.boundary baseSample) x a
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/--
Full row rank supplies the constant-fiber two-chain whose boundary realizes
any prescribed collection of vertical fundamental cycles.
-/
theorem exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (y : Word (ZMod 2) (Fin (3 * r))) :
    ∃ c : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))),
      boundary2
          (RandomTwist.fiberBundleData baseSample twistSample) c =
        verticalFundamentalWord
          (baseOne := Fin (4 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) y := by
  rcases hRank y with ⟨x, hx⟩
  refine ⟨constantFiberTwoChain
    (fiberOne := ZMod (ell * ell)) x, ?_⟩
  rw [boundary2_constantFiberTwoChain_eq_verticalFundamentalWord]
  rw [hx]

/-! ## The bundle-to-base isomorphism on first homology -/

/--
Over a full-row-rank sampled base, every bundle cycle with zero base
projection is the boundary of an explicit sum of two two-chains:

* fiberwise prefix primitives clear its horizontal sector;
* a constant-fiber lift supplied by base surjectivity clears the remaining
  vertical fundamental cycles.
-/
theorem mem_middleBoundaryCode_of_projection_eq_zero
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
        ).middleCycleCode.carrier)
    (hzProjection : homologyBaseProjection z = 0) :
    z ∈ (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleBoundaryCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let primitive := horizontalFiberPrimitiveTwoChain z
  let cleared := z + boundary2 D primitive
  have hzCycle : boundary1 D z = 0 :=
    ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  have hBoundaryCycle : boundary1 D (boundary2 D primitive) = 0 := by
    have hsquare := congrArg
      (fun f : Word (ZMod 2)
          (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
          Word (ZMod 2)
            (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
        f primitive)
      (boundary_squared D)
    simpa using hsquare
  have hClearedCycle : boundary1 D cleared = 0 := by
    change boundary1 D (z + boundary2 D primitive) = 0
    rw [map_add, hzCycle, hBoundaryCycle, add_zero]
  have hClearedHorizontal :
      ∀ b : Fin (4 * r), horizontalFiber cleared b = 0 := by
    intro b
    change horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (horizontalFiberPrimitiveTwoChain z)) b = 0
    exact horizontalFiber_add_primitiveBoundary_eq_zero
      baseSample twistSample z hzProjection b
  have hClearedVertical :
      ∀ a : Fin (3 * r), ∀ j,
        verticalFiber cleared a j = verticalFiber cleared a 0 := by
    intro a
    exact verticalFiber_constant_of_boundary1_eq_zero_of_horizontal_zero
      baseSample twistSample cleared hClearedCycle hClearedHorizontal a
  have hClearedForm :
      cleared =
        verticalFundamentalWord
          (baseOne := Fin (4 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell))
          (verticalFundamentalCoefficient cleared) :=
    eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
      cleared hClearedHorizontal hClearedVertical
  rcases exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
      baseSample twistSample hRank
      (verticalFundamentalCoefficient cleared) with ⟨c, hc⟩
  have hcCleared : boundary2 D c = cleared := by
    calc
      boundary2 D c =
          verticalFundamentalWord
            (baseOne := Fin (4 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (verticalFundamentalCoefficient cleared) := by
              simpa [D] using hc
      _ = cleared := hClearedForm.symm
  apply ((chainComplex D).mem_middleBoundaryCode_iff z).2
  refine ⟨primitive + c, ?_⟩
  change boundary2 D (primitive + c) = z
  rw [map_add, hcCleared]
  change boundary2 D primitive + (z + boundary2 D primitive) = z
  funext q
  let w := boundary2 D primitive q
  change w + (z q + w) = z q
  have hww : w + w = 0 := by
    calc
      w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel w
  calc
    w + (z q + w) = z q + (w + w) := by abel
    _ = z q := by rw [hww, add_zero]

/--
For bundle cycles over a full-row-rank base, nontrivial first homology is
equivalent to nonzero base projection.
-/
theorem not_mem_middleBoundaryCode_iff_projection_ne_zero
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
        ).middleCycleCode.carrier) :
    z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier ↔
      homologyBaseProjection z ≠ 0 := by
  constructor
  · intro hzNontrivial hzProjection
    exact hzNontrivial
      (mem_middleBoundaryCode_of_projection_eq_zero
        baseSample twistSample hRank z hz hzProjection)
  · exact not_mem_middleBoundaryCode_of_projection_ne_zero
      baseSample twistSample z

/-! ## Classical support inherited by a nontrivial bundle cycle -/

/-- The projection of a bundle cycle belongs to the sampled classical code. -/
theorem homologyBaseProjection_mem_randomBaseCode_of_bundleCycle
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
        ).middleCycleCode.carrier) :
    homologyBaseProjection z ∈
      (RandomBase.code baseSample).carrier := by
  rw [RandomBase.code, mem_parityCheckKernelCode]
  funext a
  change (∑ b : Fin (4 * r),
    RandomBase.boundary baseSample a b *
      homologyBaseProjection z b) = 0
  have ha :=
    randomBase_boundary_projection_eq_zero_of_bundleCycle
      baseSample twistSample z hz a
  simpa only [mul_comm] using ha

/-- Projection support costs at most the full horizontal Hamming weight. -/
theorem hammingWeight_homologyBaseProjection_le_horizontalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (homologyBaseProjection z) ≤
      HammingWeight (horizontalComponent z) := by
  rw [hammingWeight_eq_sum_indicator,
    hammingWeight_horizontalComponent_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro b _hb
  by_cases hp : homologyBaseProjection z b = 0
  · rw [if_neg (not_ne_iff.mpr hp)]
    exact Nat.zero_le _
  · rw [if_pos hp]
    have hFiber : horizontalFiber z b ≠ 0 := by
      intro hzero
      apply hp
      change (∑ i : fiberZero, horizontalFiber z b i) = 0
      rw [hzero]
      simp only [Pi.zero_apply, Finset.sum_const_zero]
    exact Nat.one_le_iff_ne_zero.mpr
      ((HammingWeight_eq_zero_iff (horizontalFiber z b)).not.mpr hFiber)

/-- Horizontal weight is bounded by the total bundle one-chain weight. -/
theorem hammingWeight_horizontalComponent_le
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (horizontalComponent z) ≤ HammingWeight z := by
  rw [hammingWeight_eq_horizontal_add_vertical]
  omega

/--
The sampled base-distance event forces at least `4r/5` distinct projected
base variables in every nontrivial bundle homology representative.
-/
theorem baseDistance_bound_of_nontrivial_bundleCycle
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier) :
    4 * r ≤ 5 * HammingWeight (homologyBaseProjection z) := by
  exact hDistance
    (homologyBaseProjection z)
    (homologyBaseProjection_mem_randomBaseCode_of_bundleCycle
      baseSample twistSample z hz)
    ((not_mem_middleBoundaryCode_iff_projection_ne_zero
      baseSample twistSample hRank z hz).1 hzNontrivial)

/-- Coarse total-weight consequence of the base-distance event. -/
theorem baseDistance_totalWeight_bound_of_nontrivial_bundleCycle
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier) :
    4 * r ≤ 5 * HammingWeight z := by
  have hBase := baseDistance_bound_of_nontrivial_bundleCycle
    baseSample twistSample hRank hDistance z hz hzNontrivial
  have hProjectionHorizontal :=
    hammingWeight_homologyBaseProjection_le_horizontalComponent z
  have hHorizontalTotal := hammingWeight_horizontalComponent_le z
  omega

/-! ## Residue structure used by HHO20 sliding -/

/-- Reduction of a fiber position modulo the bundle scale `ell`. -/
def fiberResidue (ell : Nat) [NeZero ell] :
    ZMod (ell * ell) →+ ZMod ell :=
  (ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom

/-- Every residue-zero fiber position is a unique embedded twist-graph layer. -/
theorem exists_unique_layerEmbedding_eq_of_fiberResidue_eq_zero
    (ell : Nat) [NeZero ell]
    (i : ZMod (ell * ell))
    (hi : fiberResidue ell i = 0) :
    ∃! u : ZMod ell, TwistGraph.layerEmbedding ell u = i := by
  have hdiv : ell ∣ i.val := by
    change
      ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell) i = 0 at hi
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hi
    exact (ZMod.natCast_eq_zero_iff i.val ell).1 hi
  have hquotient : i.val / ell < ell := by
    have hiLt := i.val_lt
    have hell : 0 < ell := NeZero.pos ell
    nlinarith [Nat.div_mul_cancel hdiv]
  let u0 : ZMod ell := (i.val / ell : Nat)
  have hu0 : TwistGraph.layerEmbedding ell u0 = i := by
    dsimp [u0]
    rw [TwistGraph.layerEmbedding_eq_val_mul,
      ZMod.val_natCast_of_lt hquotient,
      Nat.div_mul_cancel hdiv]
    exact ZMod.natCast_zmod_val i
  refine ⟨u0, hu0, ?_⟩
  intro u hu
  apply TwistGraph.layerEmbedding_injective ell
  exact hu.trans hu0.symm

/-- Every construction-selected rotation has zero residue modulo `ell`. -/
theorem fiberResidue_multipleRotation_eq_zero
    (ell : Nat) [NeZero ell] (k : Fin ell) :
    fiberResidue ell (multipleRotation ell k) = 0 := by
  rw [fiberResidue, multipleRotation]
  change ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)
    (((k.val * ell : Nat) : ZMod (ell * ell))) = 0
  rw [ZMod.castHom_apply,
    ZMod.cast_natCast (R := ZMod ell) (dvd_mul_right ell ell)]
  rw [Nat.cast_mul]
  rw [ZMod.natCast_self, mul_zero]

/--
Every actual HHO20 connection preserves the fiber residue class because its
rotation is a multiple of `ell`.
-/
theorem fiberResidue_connection_onZero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r))
    (i : ZMod (ell * ell)) :
    fiberResidue ell
        ((((RandomTwist.fiberBundleData baseSample twistSample
          ).connection b a).onZero) i) =
      fiberResidue ell i := by
  change fiberResidue ell
    (i + multipleRotation ell
      (RandomTwist.connectionIndex twistSample b a)) =
    fiberResidue ell i
  rw [map_add]
  rw [fiberResidue_multipleRotation_eq_zero, add_zero]

/-- The one-cell action of every construction connection preserves residue too. -/
theorem fiberResidue_connection_onOne
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r))
    (j : ZMod (ell * ell)) :
    fiberResidue ell
        ((((RandomTwist.fiberBundleData baseSample twistSample
          ).connection b a).onOne) j) =
      fiberResidue ell j := by
  change fiberResidue ell
    (j + multipleRotation ell
      (RandomTwist.connectionIndex twistSample b a)) =
    fiberResidue ell j
  rw [map_add]
  rw [fiberResidue_multipleRotation_eq_zero, add_zero]

/-- Horizontal support lies only at fiber positions congruent to zero mod `ell`. -/
def IsHorizontallyResidueNormalized
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Prop :=
  ∀ b i, z (Sum.inl (b, i)) ≠ 0 → fiberResidue ell i = 0

/--
Two horizontal cells whose bundle boundaries meet over one base zero-cell
have the same residue class.  This is the exact discrete invariant used to
form the clusters in HHO20 Lemma `sliding`.
-/
theorem fiberResidue_eq_of_connected_horizontal_positions
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (b b' : Fin (4 * r)) (a : Fin (3 * r))
    (i i' : ZMod (ell * ell))
    (hMeet :
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b a).onZero i =
      ((RandomTwist.fiberBundleData baseSample twistSample
        ).connection b' a).onZero i') :
    fiberResidue ell i = fiberResidue ell i' := by
  have h := congrArg (fiberResidue ell) hMeet
  rw [fiberResidue_connection_onZero
      baseSample twistSample b a i,
    fiberResidue_connection_onZero
      baseSample twistSample b' a i'] at h
  exact h

/-! ## Finite overlap clusters -/

/--
Two horizontal cells are adjacent in the HHO20 sliding graph when their
bundle boundaries meet at the same total-degree-zero coordinate.
-/
def HorizontalBoundaryOverlap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  ∃ a : Fin (3 * r),
    RandomBase.boundary baseSample a x.1 ≠ 0 ∧
    RandomBase.boundary baseSample a y.1 ≠ 0 ∧
    (((RandomTwist.fiberBundleData baseSample twistSample
      ).connection x.1 a).onZero) x.2 =
    (((RandomTwist.fiberBundleData baseSample twistSample
      ).connection y.1 a).onZero) y.2

/-- The overlap relation is symmetric. -/
theorem horizontalBoundaryOverlap_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Symmetric (HorizontalBoundaryOverlap baseSample twistSample) := by
  intro x y
  rintro ⟨a, hax, hay, hxy⟩
  exact ⟨a, hay, hax, hxy.symm⟩

/-- Adjacent horizontal cells have the same residue class. -/
theorem fiberResidue_eq_of_horizontalBoundaryOverlap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : HorizontalBoundaryOverlap baseSample twistSample x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by
  rcases hxy with ⟨a, _hax, _hay, hMeet⟩
  exact fiberResidue_eq_of_connected_horizontal_positions
    baseSample twistSample x.1 y.1 a x.2 y.2 hMeet

/-- Reflexive-transitive connectivity in the finite horizontal overlap graph. -/
def InSameHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  Relation.ReflTransGen
    (HorizontalBoundaryOverlap baseSample twistSample) x y

/-- Every horizontal overlap cluster has one well-defined fiber residue. -/
theorem fiberResidue_eq_of_inSameHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : InSameHorizontalCluster baseSample twistSample x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by
  induction hxy with
  | refl => rfl
  | tail hxy hyz ih =>
      exact ih.trans
        (fiberResidue_eq_of_horizontalBoundaryOverlap
          baseSample twistSample hyz)

/-- Cluster connectivity is symmetric because boundary overlap is symmetric. -/
theorem inSameHorizontalCluster_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Symmetric (InSameHorizontalCluster baseSample twistSample) := by
  letI : Std.Symm (HorizontalBoundaryOverlap baseSample twistSample) :=
    ⟨fun _ _ h => horizontalBoundaryOverlap_symmetric baseSample twistSample h⟩
  exact fun _ _ h => Relation.ReflTransGen.stdSymm.symm _ _ h

/--
The actual sliding graph is the overlap graph induced on horizontal cells
currently present in the representative's support.
-/
def SupportedHorizontalBoundaryOverlap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  z (Sum.inl x) ≠ 0 ∧
  z (Sum.inl y) ≠ 0 ∧
  HorizontalBoundaryOverlap baseSample twistSample x y

/-- Connectivity in the overlap graph induced on the current support. -/
def InSameSupportedHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (x y : Fin (4 * r) × ZMod (ell * ell)) : Prop :=
  Relation.ReflTransGen
    (SupportedHorizontalBoundaryOverlap
      baseSample twistSample z) x y

/-- The support-induced overlap relation is symmetric. -/
theorem supportedHorizontalBoundaryOverlap_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Symmetric
      (SupportedHorizontalBoundaryOverlap
        baseSample twistSample z) := by
  intro x y
  rintro ⟨hx, hy, hxy⟩
  exact ⟨hy, hx,
    horizontalBoundaryOverlap_symmetric
      baseSample twistSample hxy⟩

/-- Connectivity in the support-induced overlap graph is symmetric. -/
theorem inSameSupportedHorizontalCluster_symmetric
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Symmetric
      (InSameSupportedHorizontalCluster
        baseSample twistSample z) := by
  letI : Std.Symm (SupportedHorizontalBoundaryOverlap baseSample twistSample z) :=
    ⟨fun _ _ h => supportedHorizontalBoundaryOverlap_symmetric baseSample twistSample z h⟩
  exact fun _ _ h => Relation.ReflTransGen.stdSymm.symm _ _ h

/-- The finite vertex type consisting only of nonzero horizontal cells. -/
def SupportedHorizontalCell
    {r ell : Nat}
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :=
  {x : Fin (4 * r) × ZMod (ell * ell) // z (Sum.inl x) ≠ 0}

/-- Connected support cells form an equivalence relation. -/
def supportedHorizontalClusterSetoid
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Setoid (SupportedHorizontalCell z) where
  r x y :=
    InSameSupportedHorizontalCluster
      baseSample twistSample z x.1 y.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Relation.ReflTransGen.refl
    · intro x y hxy
      exact inSameSupportedHorizontalCluster_symmetric
        baseSample twistSample z hxy
    · intro x y w hxy hyw
      exact Relation.ReflTransGen.trans hxy hyw

/--
The strict finite potential for the merging phase: the number of connected
components of the overlap graph on actual horizontal support.
-/
noncomputable def horizontalClusterCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Nat := by
  exact Nat.card
    (Quotient
      (supportedHorizontalClusterSetoid
        baseSample twistSample z))

/-- A nonempty connected support has exactly one horizontal cluster. -/
theorem horizontalClusterCount_eq_one_of_connected
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : SupportedHorizontalCell z)
    (hConnected :
      ∀ x : SupportedHorizontalCell z,
        InSameSupportedHorizontalCluster
          baseSample twistSample z root.1 x.1) :
    horizontalClusterCount baseSample twistSample z = 1 := by
  classical
  rw [horizontalClusterCount, Nat.card_eq_one_iff_exists]
  refine ⟨Quotient.mk
    (supportedHorizontalClusterSetoid
      baseSample twistSample z) root, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      apply Quotient.sound
      exact inSameSupportedHorizontalCluster_symmetric
        baseSample twistSample z (hConnected x)

/-- Cluster count one means that every supported cell is connected to any root. -/
theorem connected_of_horizontalClusterCount_eq_one
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : SupportedHorizontalCell z)
    (hCount :
      horizontalClusterCount baseSample twistSample z = 1) :
    ∀ x : SupportedHorizontalCell z,
      InSameSupportedHorizontalCluster
        baseSample twistSample z root.1 x.1 := by
  classical
  rw [horizontalClusterCount, Nat.card_eq_one_iff_exists] at hCount
  rcases hCount with ⟨q, hq⟩
  intro x
  apply @Quotient.exact _
    (supportedHorizontalClusterSetoid
      baseSample twistSample z) root x
  calc
    Quotient.mk
        (supportedHorizontalClusterSetoid
          baseSample twistSample z) root = q := hq _
    _ = Quotient.mk
        (supportedHorizontalClusterSetoid
          baseSample twistSample z) x := (hq _).symm

/-- A nonzero bundle-to-base projection supplies an actual horizontal support cell. -/
theorem nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hProjection : homologyBaseProjection z ≠ 0) :
    Nonempty (SupportedHorizontalCell z) := by
  classical
  have hExists :
      ∃ x : Fin (4 * r) × ZMod (ell * ell),
        z (Sum.inl x) ≠ 0 := by
    by_contra hNot
    apply hProjection
    funext b
    change (∑ i : ZMod (ell * ell), z (Sum.inl (b, i))) = 0
    apply Finset.sum_eq_zero
    intro i _hi
    by_contra hi
    exact hNot ⟨(b, i), hi⟩
  rcases hExists with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

/-- A support-induced cluster still has one fiber residue class. -/
theorem fiberResidue_eq_of_inSameSupportedHorizontalCluster
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : InSameSupportedHorizontalCluster
      baseSample twistSample z x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by
  apply fiberResidue_eq_of_inSameHorizontalCluster
    baseSample twistSample
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih hyz.2.2

/-- The horizontal subchain belonging to the cluster rooted at `root`. -/
noncomputable def horizontalClusterSubchain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    Word (ZMod 2) (Fin (4 * r) × ZMod (ell * ell)) := by
  classical
  exact fun x =>
    if InSameSupportedHorizontalCluster
        baseSample twistSample z root x
    then z (Sum.inl x)
    else 0

/-- Every nonzero cell selected by a cluster subchain lies in that cluster. -/
theorem inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root x : Fin (4 * r) × ZMod (ell * ell))
    (hx : horizontalClusterSubchain
      baseSample twistSample z root x ≠ 0) :
    InSameSupportedHorizontalCluster
      baseSample twistSample z root x := by
  classical
  by_contra hnot
  exact hx (by simp [horizontalClusterSubchain, hnot])

/--
A supported horizontal neighbor of a supported cell already reached from the
root belongs to the same support-induced cluster.
-/
theorem inSameSupportedHorizontalCluster_tail
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root x y : Fin (4 * r) × ZMod (ell * ell))
    (hxCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root x)
    (hxSupport : z (Sum.inl x) ≠ 0)
    (hySupport : z (Sum.inl y) ≠ 0)
    (hxy : HorizontalBoundaryOverlap baseSample twistSample x y) :
    InSameSupportedHorizontalCluster
      baseSample twistSample z root y := by
  exact Relation.ReflTransGen.tail hxCluster
    ⟨hxSupport, hySupport, hxy⟩

/-- Every nonzero cluster subchain has the residue of its root. -/
theorem fiberResidue_clusterSubchain_eq_root
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root x : Fin (4 * r) × ZMod (ell * ell))
    (hx : horizontalClusterSubchain
      baseSample twistSample z root x ≠ 0) :
    fiberResidue ell x.2 = fiberResidue ell root.2 := by
  exact (fiberResidue_eq_of_inSameSupportedHorizontalCluster
    baseSample twistSample z
    (inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
      baseSample twistSample z root x hx)).symm

/-! ## Horizontal cost of a cluster slide -/

/-- A binary word obtained by retaining a subset of another word's coordinates. -/
def IsBinarySubword
    {ι : Type u}
    (h z : Word (ZMod 2) ι) : Prop :=
  ∀ i, h i = 0 ∨ h i = z i

/-- Deleting a binary subword partitions Hamming weight exactly. -/
theorem hammingWeight_add_subword_add_hammingWeight
    {ι : Type u} [Fintype ι]
    (h z : Word (ZMod 2) ι)
    (hhz : IsBinarySubword h z) :
    HammingWeight (z + h) + HammingWeight h =
      HammingWeight z := by
  rw [hammingWeight_eq_sum_indicator,
    hammingWeight_eq_sum_indicator,
    hammingWeight_eq_sum_indicator,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    (if z i + h i ≠ 0 then 1 else 0) +
      (if h i ≠ 0 then 1 else 0) =
    if z i ≠ 0 then 1 else 0
  rcases hhz i with hi | hi
  · have hadd : z i + h i = z i := by rw [hi, add_zero]
    rw [hadd, hi]
    simp
  · rw [hi]
    have hzz : z i + z i = 0 := by
      calc
        z i + z i = z i + (-z i) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    rw [hzz]
    simp

/-- A coordinate-weighted support cost for a binary word. -/
def WeightedHammingCost
    {ι : Type u} [Fintype ι]
    (weight : ι → Nat)
    (z : Word (ZMod 2) ι) : Nat :=
  ∑ i, if z i ≠ 0 then weight i else 0

/-- Weighted support cost is subadditive under binary word addition. -/
theorem weightedHammingCost_add_le
    {ι : Type u} [Fintype ι]
    (weight : ι → Nat)
    (x y : Word (ZMod 2) ι) :
    WeightedHammingCost weight (x + y) ≤
      WeightedHammingCost weight x +
        WeightedHammingCost weight y := by
  classical
  rw [WeightedHammingCost, WeightedHammingCost,
    WeightedHammingCost, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hx : x i = 0
  · simp [hx]
  by_cases hy : y i = 0
  · simp [hy]
  by_cases hxy : x i + y i = 0 <;> simp [hxy, hx, hy]

/-- Deleting a binary subword partitions every weighted support cost exactly. -/
theorem weightedHammingCost_add_subword_add
    {ι : Type u} [Fintype ι]
    (weight : ι → Nat)
    (h z : Word (ZMod 2) ι)
    (hhz : IsBinarySubword h z) :
    WeightedHammingCost weight (z + h) +
        WeightedHammingCost weight h =
      WeightedHammingCost weight z := by
  classical
  rw [WeightedHammingCost, WeightedHammingCost,
    WeightedHammingCost, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    ((if z i + h i ≠ 0 then weight i else 0) +
      if h i ≠ 0 then weight i else 0) =
    if z i ≠ 0 then weight i else 0
  rcases hhz i with hi | hi
  · have hadd : z i + h i = z i := by rw [hi, add_zero]
    rw [hadd, hi]
    simp
  · rw [hi]
    have hzz : z i + z i = 0 := by
      calc
        z i + z i = z i + (-z i) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    rw [hzz]
    simp

/-- A cluster subchain is coordinatewise a subword of the horizontal sector. -/
theorem horizontalClusterSubchain_isBinarySubword
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    IsBinarySubword
      (horizontalClusterSubchain
        baseSample twistSample z root)
      (horizontalComponent z) := by
  classical
  intro x
  by_cases hx : InSameSupportedHorizontalCluster
      baseSample twistSample z root x
  · right
    simp [horizontalClusterSubchain, horizontalComponent, hx]
  · left
    simp [horizontalClusterSubchain, hx]

/-- Move every horizontal coefficient forward by one fiber position. -/
def shiftHorizontalSubchain
    {baseOne : Type u}
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    Word (ZMod 2) (baseOne × ZMod n) :=
  fun bi => h (bi.1, bi.2 - 1)

/-- A horizontal shift preserves Hamming weight. -/
theorem hammingWeight_shiftHorizontalSubchain
    {baseOne : Type u} [Fintype baseOne]
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    HammingWeight (shiftHorizontalSubchain n h) =
      HammingWeight h := by
  let e : (baseOne × ZMod n) ≃ (baseOne × ZMod n) :=
    Equiv.prodCongr (Equiv.refl baseOne) (Equiv.addRight 1)
  have heq : shiftHorizontalSubchain n h = reindexWord e h := by
    funext bi
    rcases bi with ⟨b, i⟩
    simp [shiftHorizontalSubchain, reindexWord, e, sub_eq_add_neg,
      Equiv.prodCongr]
  rw [heq]
  exact hammingWeight_reindexWord e h

/--
Potential used to terminate residue normalization: each supported horizontal
cell is weighted by the number of positive unit shifts needed to reach
residue zero.
-/
def horizontalResiduePotential
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Nat :=
  WeightedHammingCost
    (fun bi => (-fiberResidue ell bi.2).val)
    (horizontalComponent z)

/--
For a nonzero residue, one positive unit shift reduces its positive distance
to zero by exactly one.
-/
theorem fiberResidue_positiveDistance_add_one
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (q : ZMod ell) (hq : q ≠ 0) :
    (-(q + 1)).val + 1 = (-q).val := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  letI : Fact (1 < ell) := ⟨hEll⟩
  let d : ZMod ell := -q
  have hd : d ≠ 0 := neg_ne_zero.mpr hq
  have hdPos : 1 ≤ d.val := Nat.one_le_iff_ne_zero.mpr
    ((ZMod.val_eq_zero d).not.mpr hd)
  have hOneVal : (1 : ZMod ell).val = 1 := by
    exact ZMod.val_one ell
  have hEq : -(q + 1) = d - 1 := by
    dsimp [d]
    abel
  rw [hEq, ZMod.val_sub (by simpa [hOneVal] using hdPos), hOneVal]
  rw [Nat.sub_add_cancel hdPos]

/--
Shifting a nonzero-residue cluster forward lowers its weighted residue cost
by exactly the cluster's Hamming weight.
-/
theorem weightedHammingCost_shiftCluster_add_hammingWeight
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hRootResidue : fiberResidue ell root.2 ≠ 0) :
    WeightedHammingCost
        (fun bi => (-fiberResidue ell bi.2).val)
        (shiftHorizontalSubchain (ell * ell)
          (horizontalClusterSubchain
            baseSample twistSample z root)) +
      HammingWeight
        (horizontalClusterSubchain
          baseSample twistSample z root) =
    WeightedHammingCost
        (fun bi => (-fiberResidue ell bi.2).val)
        (horizontalClusterSubchain
          baseSample twistSample z root) := by
  classical
  let h := horizontalClusterSubchain
    baseSample twistSample z root
  let e :
      (Fin (4 * r) × ZMod (ell * ell)) ≃
        (Fin (4 * r) × ZMod (ell * ell)) :=
    Equiv.prodCongr (Equiv.refl (Fin (4 * r))) (Equiv.addRight (-1))
  rw [WeightedHammingCost, WeightedHammingCost,
    hammingWeight_eq_sum_indicator]
  have hShift :
      (∑ bi : Fin (4 * r) × ZMod (ell * ell),
        if shiftHorizontalSubchain (ell * ell) h bi ≠ 0
        then (-fiberResidue ell bi.2).val else 0) =
      ∑ bi : Fin (4 * r) × ZMod (ell * ell),
        if h bi ≠ 0
        then (-fiberResidue ell (bi.2 + 1)).val else 0 := by
    apply Fintype.sum_equiv e
    intro bi
    rcases bi with ⟨b, i⟩
    simp [shiftHorizontalSubchain, e, sub_eq_add_neg]
  rw [hShift, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro bi _hbi
  change
    ((if h bi ≠ 0
      then (-fiberResidue ell (bi.2 + 1)).val else 0) +
      if h bi ≠ 0 then 1 else 0) =
    if h bi ≠ 0
      then (-fiberResidue ell bi.2).val else 0
  by_cases hbi : h bi = 0
  · simp [hbi]
  have hResidue :
      fiberResidue ell bi.2 = fiberResidue ell root.2 :=
    fiberResidue_clusterSubchain_eq_root
      baseSample twistSample z root bi hbi
  simp only [if_pos hbi]
  have hOne :
      fiberResidue ell (1 : ZMod (ell * ell)) = 1 := by
    simp [fiberResidue]
  rw [map_add, hOne, hResidue]
  exact fiberResidue_positiveDistance_add_one
    ell (fiberResidue ell root.2) hRootResidue

/-! ## One discrete sliding step -/

/-- Embed a horizontal chain into the total-degree-one bundle word. -/
def horizontalChainWord
    {baseZero baseOne fiberZero fiberOne : Type u}
    (h : Word (ZMod 2) (baseOne × fiberZero)) :
    Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)
  | Sum.inl bi => h bi
  | Sum.inr _ => 0

/--
Use the same coefficients as fiber one-cells over each base one-cell.  Its
two-boundary performs one discrete positive slide of the horizontal chain.
-/
def oneStepSlideTwoChain
    {baseOne fiber : Type u}
    (h : Word (ZMod 2) (baseOne × fiber)) :
    Word (ZMod 2) (C2Index baseOne fiber) :=
  fun bj => h bj

/-- Exact horizontal coordinate formula for one discrete sliding boundary. -/
theorem horizontalFiber_boundary2_oneStepSlideTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (b : Fin (4 * r)) (i : ZMod (ell * ell)) :
    horizontalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) b i =
      h (b, i) + h (b, i - 1) := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  rw [horizontalFiber_boundary2]
  change cycleFiberChainBoundary (ell * ell) (fun j => h (b, j)) i =
    h (b, i) + h (b, i - 1)
  exact cycleFiberChainBoundary_apply (ell * ell) (by nlinarith) _ i

/-- Exact vertical coordinate formula for one discrete sliding boundary. -/
theorem verticalFiber_boundary2_oneStepSlideTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) (j : ZMod (ell * ell)) :
    verticalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) a j =
      ∑ b : Fin (4 * r),
        RandomBase.boundary baseSample a b *
          h (b,
            (((RandomTwist.fiberBundleData baseSample twistSample
              ).connection b a).onOne.symm) j) := by
  change boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (oneStepSlideTwoChain h) (Sum.inr (a, j)) = _
  rw [boundary2_apply_vertical]
  rfl

/-- Add the explicit two-boundary that performs one discrete slide. -/
noncomputable def oneStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))) :=
  z +
    boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (oneStepSlideTwoChain h)

/-- One sliding step stays in the same middle-homology class. -/
theorem oneStepSlide_add_boundary_eq
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    oneStepSlide baseSample twistSample z h =
      z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h) := by
  rfl

/-- Horizontal sector after a slide: delete the subchain and add its shift. -/
theorem horizontalComponent_oneStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    horizontalComponent
        (oneStepSlide baseSample twistSample z h) =
      (horizontalComponent z + h) +
        shiftHorizontalSubchain (ell * ell) h := by
  funext bi
  rcases bi with ⟨b, i⟩
  change horizontalFiber
      (oneStepSlide baseSample twistSample z h) b i =
    ((horizontalComponent z + h) +
      shiftHorizontalSubchain (ell * ell) h) (b, i)
  rw [oneStepSlide, show horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (oneStepSlideTwoChain h)) b i =
      horizontalFiber z b i +
        horizontalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (oneStepSlideTwoChain h)) b i by rfl]
  rw [horizontalFiber_boundary2_oneStepSlideTwoChain]
  change z (Sum.inl (b, i)) + (h (b, i) + h (b, i - 1)) =
    (z (Sum.inl (b, i)) + h (b, i)) + h (b, i - 1)
  abel

/-- Sliding any coordinate subword cannot increase horizontal Hamming weight. -/
theorem hammingWeight_horizontalComponent_oneStepSlide_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (hhz : IsBinarySubword h (horizontalComponent z)) :
    HammingWeight
        (horizontalComponent
          (oneStepSlide baseSample twistSample z h)) ≤
      HammingWeight (horizontalComponent z) := by
  rw [horizontalComponent_oneStepSlide]
  calc
    HammingWeight
        ((horizontalComponent z + h) +
          shiftHorizontalSubchain (ell * ell) h) ≤
        HammingWeight (horizontalComponent z + h) +
          HammingWeight (shiftHorizontalSubchain (ell * ell) h) :=
      HammingWeight_add_le _ _
    _ = HammingWeight (horizontalComponent z + h) +
          HammingWeight h := by
      rw [hammingWeight_shiftHorizontalSubchain]
    _ = HammingWeight (horizontalComponent z) :=
      hammingWeight_add_subword_add_hammingWeight h
        (horizontalComponent z) hhz

/-- In particular, sliding a support-induced cluster never raises horizontal cost. -/
theorem hammingWeight_horizontalComponent_slideCluster_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (horizontalComponent
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) ≤
      HammingWeight (horizontalComponent z) := by
  apply hammingWeight_horizontalComponent_oneStepSlide_le
  exact horizontalClusterSubchain_isBinarySubword
    baseSample twistSample z root

/--
A positive slide of a supported cluster with nonzero residue strictly lowers
the residue potential.  Cancellations at the destination can only lower it
further.
-/
theorem horizontalResiduePotential_oneStepSlideCluster_lt
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hRootSupport : z (Sum.inl root) ≠ 0)
    (hRootResidue : fiberResidue ell root.2 ≠ 0) :
    horizontalResiduePotential
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) <
      horizontalResiduePotential z := by
  let h := horizontalClusterSubchain
    baseSample twistSample z root
  let weight := fun bi : Fin (4 * r) × ZMod (ell * ell) =>
    (-fiberResidue ell bi.2).val
  have hSubword : IsBinarySubword h (horizontalComponent z) :=
    horizontalClusterSubchain_isBinarySubword
      baseSample twistSample z root
  have hRootCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root root :=
    Relation.ReflTransGen.refl
  have hRootEq : h root = z (Sum.inl root) := by
    simp [h, horizontalClusterSubchain, hRootCluster]
  have hNonzero : h ≠ 0 := by
    intro hzero
    apply hRootSupport
    rw [← hRootEq, hzero]
    rfl
  have hWeightPos : 0 < HammingWeight h := by
    exact Nat.pos_of_ne_zero
      ((HammingWeight_eq_zero_iff h).not.mpr hNonzero)
  have hAdd :
      WeightedHammingCost weight
          ((horizontalComponent z + h) +
            shiftHorizontalSubchain (ell * ell) h) ≤
        WeightedHammingCost weight (horizontalComponent z + h) +
          WeightedHammingCost weight
            (shiftHorizontalSubchain (ell * ell) h) :=
    weightedHammingCost_add_le weight
      (horizontalComponent z + h)
      (shiftHorizontalSubchain (ell * ell) h)
  have hPartition :
      WeightedHammingCost weight (horizontalComponent z + h) +
          WeightedHammingCost weight h =
        WeightedHammingCost weight (horizontalComponent z) :=
    weightedHammingCost_add_subword_add
      weight h (horizontalComponent z) hSubword
  have hShift :
      WeightedHammingCost weight
          (shiftHorizontalSubchain (ell * ell) h) +
        HammingWeight h =
      WeightedHammingCost weight h := by
    exact weightedHammingCost_shiftCluster_add_hammingWeight
      baseSample twistSample z root hRootResidue
  rw [horizontalResiduePotential,
    horizontalComponent_oneStepSlide]
  change
    WeightedHammingCost weight
        ((horizontalComponent z + h) +
          shiftHorizontalSubchain (ell * ell) h) <
      WeightedHammingCost weight (horizontalComponent z)
  omega

/-! ## The opposite discrete sliding direction -/

/-- Move every horizontal coefficient backward by one fiber position. -/
def backwardShiftHorizontalSubchain
    {baseOne : Type u}
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    Word (ZMod 2) (baseOne × ZMod n) :=
  fun bi => h (bi.1, bi.2 + 1)

/-- A backward horizontal shift preserves Hamming weight. -/
theorem hammingWeight_backwardShiftHorizontalSubchain
    {baseOne : Type u} [Fintype baseOne]
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    HammingWeight (backwardShiftHorizontalSubchain n h) =
      HammingWeight h := by
  let e : (baseOne × ZMod n) ≃ (baseOne × ZMod n) :=
    Equiv.prodCongr (Equiv.refl baseOne) (Equiv.addRight (-1))
  have heq : backwardShiftHorizontalSubchain n h = reindexWord e h := by
    funext bi
    rcases bi with ⟨b, i⟩
    simp [backwardShiftHorizontalSubchain, reindexWord, e,
      Equiv.prodCongr]
  rw [heq]
  exact hammingWeight_reindexWord e h

/--
Shift the chosen coefficients by one before regarding them as fiber
one-cells; its two-boundary performs one discrete negative slide.
-/
def negativeStepSlideTwoChain
    {baseOne : Type u}
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    Word (ZMod 2) (C2Index baseOne (ZMod n)) :=
  fun bj => h (bj.1, bj.2 + 1)

/-- Add the explicit two-boundary that performs one negative slide. -/
noncomputable def negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))) :=
  z +
    boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (negativeStepSlideTwoChain (ell * ell) h)

/-- Exact horizontal coordinate formula for a negative sliding boundary. -/
theorem horizontalFiber_boundary2_negativeStepSlideTwoChain
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (b : Fin (4 * r)) (i : ZMod (ell * ell)) :
    horizontalFiber
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (negativeStepSlideTwoChain (ell * ell) h)) b i =
      h (b, i + 1) + h (b, i) := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  rw [horizontalFiber_boundary2]
  change cycleFiberChainBoundary (ell * ell)
      (fun j => h (b, j + 1)) i =
    h (b, i + 1) + h (b, i)
  rw [cycleFiberChainBoundary_apply (ell * ell) (by nlinarith)]
  congr 1
  simp

/-- Horizontal sector after a negative slide: delete the subchain and shift it backward. -/
theorem horizontalComponent_negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    horizontalComponent
        (negativeStepSlide baseSample twistSample z h) =
      (horizontalComponent z + h) +
        backwardShiftHorizontalSubchain (ell * ell) h := by
  funext bi
  rcases bi with ⟨b, i⟩
  change horizontalFiber
      (negativeStepSlide baseSample twistSample z h) b i =
    ((horizontalComponent z + h) +
      backwardShiftHorizontalSubchain (ell * ell) h) (b, i)
  rw [negativeStepSlide, show horizontalFiber
      (z +
        boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)
          (negativeStepSlideTwoChain (ell * ell) h)) b i =
      horizontalFiber z b i +
        horizontalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (negativeStepSlideTwoChain (ell * ell) h)) b i by rfl]
  rw [horizontalFiber_boundary2_negativeStepSlideTwoChain]
  change z (Sum.inl (b, i)) + (h (b, i + 1) + h (b, i)) =
    (z (Sum.inl (b, i)) + h (b, i)) + h (b, i + 1)
  abel

/-- Sliding any coordinate subword negatively cannot increase horizontal weight. -/
theorem hammingWeight_horizontalComponent_negativeStepSlide_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (hhz : IsBinarySubword h (horizontalComponent z)) :
    HammingWeight
        (horizontalComponent
          (negativeStepSlide baseSample twistSample z h)) ≤
      HammingWeight (horizontalComponent z) := by
  rw [horizontalComponent_negativeStepSlide]
  calc
    HammingWeight
        ((horizontalComponent z + h) +
          backwardShiftHorizontalSubchain (ell * ell) h) ≤
        HammingWeight (horizontalComponent z + h) +
          HammingWeight
            (backwardShiftHorizontalSubchain (ell * ell) h) :=
      HammingWeight_add_le _ _
    _ = HammingWeight (horizontalComponent z + h) +
          HammingWeight h := by
      rw [hammingWeight_backwardShiftHorizontalSubchain]
    _ = HammingWeight (horizontalComponent z) :=
      hammingWeight_add_subword_add_hammingWeight h
        (horizontalComponent z) hhz

/-- A support-induced cluster also has nonincreasing horizontal cost backward. -/
theorem hammingWeight_horizontalComponent_negativeSlideCluster_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (horizontalComponent
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) ≤
      HammingWeight (horizontalComponent z) := by
  apply hammingWeight_horizontalComponent_negativeStepSlide_le
  exact horizontalClusterSubchain_isBinarySubword
    baseSample twistSample z root

/-! ## Vertical cost in the two sliding directions -/

/--
Restrict the horizontal sector of a bundle word to the `ell` residue-zero
fiber positions used by the HHO20 twist graph code.
-/
def twistGraphWordOfHorizontalComponent
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Word (ZMod 2) (ZMod ell × Fin (4 * r)) :=
  fun ub =>
    horizontalFiber z ub.2
      (TwistGraph.layerEmbedding ell ub.1)

/--
For a residue-normalized representative, a horizontal fiber is supported
exactly on the image of its twist-graph column.
-/
theorem hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (b : Fin (4 * r)) :
    hammingSupport (horizontalFiber z b) =
      (hammingSupport
        (TwistGraph.variableWord
          (twistGraphWordOfHorizontalComponent z) b)).image
        (TwistGraph.layerEmbedding ell) := by
  classical
  ext i
  constructor
  · intro hi
    have hiNonzero : horizontalFiber z b i ≠ 0 := by
      simpa [hammingSupport] using hi
    have hResidue : fiberResidue ell i = 0 := by
      apply hNormalized b i
      simpa [horizontalFiber] using hiNonzero
    obtain ⟨u, hu, _hUnique⟩ :=
      exists_unique_layerEmbedding_eq_of_fiberResidue_eq_zero
        ell i hResidue
    apply Finset.mem_image.mpr
    refine ⟨u, ?_, hu⟩
    have huNonzero :
        horizontalFiber z b (TwistGraph.layerEmbedding ell u) ≠ 0 := by
      rw [hu]
      exact hiNonzero
    simpa [hammingSupport, TwistGraph.variableWord,
      twistGraphWordOfHorizontalComponent] using huNonzero
  · intro hi
    obtain ⟨u, huSupport, hu⟩ := Finset.mem_image.mp hi
    have huNonzero :
        TwistGraph.variableWord
            (twistGraphWordOfHorizontalComponent z) b u ≠ 0 := by
      simpa [hammingSupport] using huSupport
    have hiNonzero : horizontalFiber z b i ≠ 0 := by
      rw [← hu]
      simpa [TwistGraph.variableWord,
        twistGraphWordOfHorizontalComponent] using huNonzero
    simpa [hammingSupport] using hiNonzero

/-- Normalized horizontal fiber weight equals its twist-graph column weight. -/
theorem hammingWeight_twistGraph_variableWord_eq_horizontalFiber
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (b : Fin (4 * r)) :
    HammingWeight
        (TwistGraph.variableWord
          (twistGraphWordOfHorizontalComponent z) b) =
      HammingWeight (horizontalFiber z b) := by
  rw [HammingWeight, HammingWeight,
    hammingSupport_horizontalFiber_eq_image_twistGraph_variableWord
      z hNormalized b,
    Finset.card_image_of_injective _
      (TwistGraph.layerEmbedding_injective ell)]

/--
The twist-graph word of a residue-normalized representative has exactly the
full horizontal-sector Hamming weight; no coordinates are discarded.
-/
theorem hammingWeight_twistGraphWordOfHorizontalComponent
    {r ell : Nat}
    [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z) :
    HammingWeight (twistGraphWordOfHorizontalComponent z) =
      HammingWeight (horizontalComponent z) := by
  rw [TwistGraph.hammingWeight_eq_sum_variableWord,
    hammingWeight_horizontalComponent_eq_sum_fibers]
  apply Finset.sum_congr rfl
  intro b _hb
  exact hammingWeight_twistGraph_variableWord_eq_horizontalFiber
    z hNormalized b

/--
The contribution of a horizontal subchain to the bundle boundary over one
base zero-cell.  This is also the vertical toggle created by its positive
slide.
-/
noncomputable def horizontalChainBoundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    Word (ZMod 2) (ZMod (ell * ell)) :=
  fun j =>
    ∑ b : Fin (4 * r),
      RandomBase.boundary baseSample a b *
        h (b,
          (((RandomTwist.fiberBundleData baseSample twistSample
            ).connection b a).onOne.symm) j)

/-- Base zero-cells over which a horizontal chain has nonzero boundary. -/
noncomputable def horizontalBoundaryShadow
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    Finset (Fin (3 * r)) := by
  classical
  exact Finset.univ.filter (fun a =>
    ∃ j, horizontalChainBoundary baseSample twistSample h a j ≠ 0)

/--
The parity check on the type edge out of `u` is exactly the horizontal bundle
boundary at the embedded target layer.  This fixes the source/target
orientation used by the later LTC argument.
-/
theorem twistGraph_checkSyndrome_eq_horizontalChainBoundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (u : ZMod ell) (a : Fin (3 * r)) :
    TwistGraph.checkSyndrome baseSample twistSample
        (twistGraphWordOfHorizontalComponent z) u a =
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a
        (TwistGraph.layerEmbedding ell
          (TwistGraph.outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u)) := by
  classical
  simp only [TwistGraph.checkSyndrome, horizontalChainBoundary]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [TwistGraph.connection_onOne_symm_layerEmbedding_outNeighbor]
  cases htail : RandomTwist.isTail twistSample a b <;>
    simp [twistGraphWordOfHorizontalComponent,
      horizontalComponent, horizontalFiber]

@[simp]
theorem mem_horizontalBoundaryShadow_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    a ∈ horizontalBoundaryShadow baseSample twistSample h ↔
      ∃ j, horizontalChainBoundary baseSample twistSample h a j ≠ 0 := by
  classical
  simp [horizontalBoundaryShadow]

/-- Every violated twist-graph check projects to a nonzero bundle boundary. -/
theorem snd_mem_horizontalBoundaryShadow_of_mem_twistGraph_violationSet
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (ua : ZMod ell × Fin (3 * r))
    (hua :
      ua ∈ TwistGraph.violationSet baseSample twistSample
        (twistGraphWordOfHorizontalComponent z)) :
    ua.2 ∈ horizontalBoundaryShadow baseSample twistSample
      (horizontalComponent z) := by
  rw [mem_horizontalBoundaryShadow_iff]
  refine ⟨TwistGraph.layerEmbedding ell
    (TwistGraph.outNeighbor twistSample
      (RandomTwist.checkType typeCount ua.2) ua.1), ?_⟩
  rw [← twistGraph_checkSyndrome_eq_horizontalChainBoundary]
  exact
    (TwistGraph.mem_violationSet_iff baseSample twistSample
      (twistGraphWordOfHorizontalComponent z) ua.1 ua.2).1 hua

/--
There are at most `ell` violated twist checks above each base check in the
horizontal boundary shadow.
-/
theorem twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    TwistGraph.violationCount baseSample twistSample
        (twistGraphWordOfHorizontalComponent z) ≤
      ell *
        (horizontalBoundaryShadow baseSample twistSample
          (horizontalComponent z)).card := by
  classical
  let shadow :=
    horizontalBoundaryShadow baseSample twistSample
      (horizontalComponent z)
  have hsubset :
      TwistGraph.violationSet baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) ⊆
        Finset.univ.product shadow := by
    intro ua hua
    rcases ua with ⟨u, a⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_univ u,
        snd_mem_horizontalBoundaryShadow_of_mem_twistGraph_violationSet
          baseSample twistSample z (u, a) hua⟩
  have hcard := Finset.card_le_card hsubset
  simpa [TwistGraph.violationCount, shadow, ZMod.card] using hcard

/--
The boundary of a residue-normalized horizontal sector is supported only at
fiber vertices of residue zero.
-/
theorem fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hNormalized : IsHorizontallyResidueNormalized z)
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hj :
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a j ≠ 0) :
    fiberResidue ell j = 0 := by
  classical
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hSum :
      (∑ b : Fin (4 * r),
        RandomBase.boundary baseSample a b *
          z (Sum.inl
            (b, ((D.connection b a).onOne.symm) j))) ≠ 0 := by
    simpa [horizontalChainBoundary, horizontalComponent, D] using hj
  obtain ⟨b, _hb, hbTerm⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hSum
  have hbSupport :
      z (Sum.inl
        (b, ((D.connection b a).onOne.symm) j)) ≠ 0 := by
    intro hbZero
    apply hbTerm
    simp [hbZero]
  have hPosition :
      fiberResidue ell ((D.connection b a).onOne.symm j) = 0 :=
    hNormalized b ((D.connection b a).onOne.symm j) hbSupport
  have hConnection :=
    fiberResidue_connection_onOne
      baseSample twistSample b a
        ((D.connection b a).onOne.symm j)
  rw [(D.connection b a).onOne.apply_symm_apply] at hConnection
  exact hConnection.trans hPosition

/--
If the fine cycle boundary is supported at residue-zero positions, the word
is constant throughout every length-`ell` block.
-/
theorem cycleWord_block_constant_of_boundary_supported_at_zero_residue
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0)
    (u : ZMod ell) (k : Fin ell) :
    v (TwistGraph.blockPosition ell (u, k)) =
      v (TwistGraph.layerEmbedding ell u) := by
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  let start := TwistGraph.layerEmbedding ell u
  have hStartResidue : fiberResidue ell start = 0 := by
    dsimp [start]
    rw [TwistGraph.layerEmbedding_eq_val_mul]
    change ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)
      (((u.val * ell : Nat) : ZMod (ell * ell))) = 0
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast (R := ZMod ell) (dvd_mul_right ell ell),
      Nat.cast_mul, ZMod.natCast_self, mul_zero]
  have hRun :
      ∀ t : Nat, t < ell →
        v (start + (t : ZMod (ell * ell))) = v start := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
        have htPrev : t < ell := by omega
        have hResidueNe :
            fiberResidue ell
              (start + ((t + 1 : Nat) : ZMod (ell * ell))) ≠ 0 := by
          rw [map_add, hStartResidue, zero_add]
          change ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)
            (((t + 1 : Nat) : ZMod (ell * ell))) ≠ 0
          rw [ZMod.castHom_apply,
            ZMod.cast_natCast (R := ZMod ell)
              (dvd_mul_right ell ell)]
          intro hzero
          have hval := congrArg ZMod.val hzero
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
          omega
        have hBoundaryZero :
            cycleFiberChainBoundary (ell * ell) v
              (start + ((t + 1 : Nat) : ZMod (ell * ell))) = 0 := by
          by_contra hne
          exact hResidueNe (hBoundarySupport _ hne)
        rw [cycleFiberChainBoundary_apply
          (ell * ell) (by nlinarith)] at hBoundaryZero
        have hStep :
            v (start + ((t + 1 : Nat) : ZMod (ell * ell))) =
              v ((start + ((t + 1 : Nat) :
                ZMod (ell * ell))) - 1) := by
          have hneg := eq_neg_of_add_eq_zero_left hBoundaryZero
          simpa [ZMod.neg_eq_self_mod_two] using hneg
        calc
          v (start + ((t + 1 : Nat) : ZMod (ell * ell))) =
              v ((start + ((t + 1 : Nat) :
                ZMod (ell * ell))) - 1) := hStep
          _ = v (start + (t : ZMod (ell * ell))) := by
            congr 2
            push_cast
            abel
          _ = v start := ih htPrev
  change v (start + (k.val : ZMod (ell * ell))) = v start
  exact hRun k.val k.isLt

/-- The coarse word obtained by sampling one cell from every fiber block. -/
def coarseFiberWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell))) :
    Word (ZMod 2) (ZMod ell) :=
  fun u => v (TwistGraph.layerEmbedding ell u)

/--
A block-constant fine word has exactly `ell` copies of every coarse-layer
bit.
-/
theorem hammingWeight_eq_ell_mul_coarseFiberWord
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    HammingWeight v =
      ell * HammingWeight (coarseFiberWord ell v) := by
  let e :
      ZMod (ell * ell) ≃ (ZMod ell × Fin ell) :=
    (TwistGraph.blockEquiv ell).symm
  have hReindexed :
      reindexWord e v =
        fun uk : ZMod ell × Fin ell =>
          coarseFiberWord ell v uk.1 := by
    funext uk
    change v (TwistGraph.blockEquiv ell uk) =
      v (TwistGraph.layerEmbedding ell uk.1)
    rw [TwistGraph.blockEquiv_apply]
    exact
      cycleWord_block_constant_of_boundary_supported_at_zero_residue
        ell v hBoundarySupport uk.1 uk.2
  have hProduct :
      HammingWeight
          (fun uk : ZMod ell × Fin ell =>
            coarseFiberWord ell v uk.1) =
        ell * HammingWeight (coarseFiberWord ell v) := by
    rw [hammingWeight_eq_sum_indicator,
      hammingWeight_eq_sum_indicator, Fintype.sum_prod_type]
    calc
      (∑ u : ZMod ell,
          ∑ _k : Fin ell,
            if coarseFiberWord ell v u ≠ 0 then 1 else 0) =
        ∑ u : ZMod ell,
          ell * (if coarseFiberWord ell v u ≠ 0 then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro u _hu
            simp
      _ = ell *
          ∑ u : ZMod ell,
            if coarseFiberWord ell v u ≠ 0 then 1 else 0 := by
            rw [Finset.mul_sum]
  calc
    HammingWeight v = HammingWeight (reindexWord e v) :=
      (hammingWeight_reindexWord e v).symm
    _ = HammingWeight
          (fun uk : ZMod ell × Fin ell =>
            coarseFiberWord ell v uk.1) := by rw [hReindexed]
    _ = ell * HammingWeight (coarseFiberWord ell v) := hProduct

/-- A cyclic boundary has weight at most twice the word weight. -/
theorem hammingWeight_cycleFiberChainBoundary_le_two_mul
    (n : Nat) [NeZero n] [NeZero (n - 1)]
    (v : Word (ZMod 2) (ZMod n)) :
    HammingWeight (cycleFiberChainBoundary n v) ≤
      2 * HammingWeight v := by
  have hTwo : 2 ≤ n := by
    have hne : n - 1 ≠ 0 := NeZero.ne (n - 1)
    omega
  let shifted : Word (ZMod 2) (ZMod n) := fun i => v (i - 1)
  have hBoundary :
      cycleFiberChainBoundary n v = v + shifted := by
    funext i
    rw [cycleFiberChainBoundary_apply n hTwo]
    rfl
  have hShifted : HammingWeight shifted = HammingWeight v := by
    let e : ZMod n ≃ ZMod n := Equiv.addRight (1 : ZMod n)
    have hreindex := hammingWeight_reindexWord e v
    change HammingWeight shifted = HammingWeight v
    have hwords : shifted = reindexWord e v := by
      funext i
      change v (i - 1) = v (i + -1)
      rw [sub_eq_add_neg]
    rw [hwords]
    exact hreindex
  rw [hBoundary]
  calc
    HammingWeight (v + shifted) ≤
        HammingWeight v + HammingWeight shifted :=
      HammingWeight_add_le v shifted
    _ = 2 * HammingWeight v := by omega

/-- Sample the fine cyclic boundary at every residue-zero layer. -/
def coarseBoundaryWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell))) :
    Word (ZMod 2) (ZMod ell) :=
  fun u =>
    cycleFiberChainBoundary (ell * ell) v
      (TwistGraph.layerEmbedding ell u)

/-- A residue-zero-supported fine boundary has exactly its coarse support. -/
theorem hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    hammingSupport (cycleFiberChainBoundary (ell * ell) v) =
      (hammingSupport (coarseBoundaryWord ell v)).image
        (TwistGraph.layerEmbedding ell) := by
  classical
  ext j
  constructor
  · intro hj
    have hjNonzero :
        cycleFiberChainBoundary (ell * ell) v j ≠ 0 := by
      simpa [hammingSupport] using hj
    obtain ⟨u, hu, _hUnique⟩ :=
      exists_unique_layerEmbedding_eq_of_fiberResidue_eq_zero
        ell j (hBoundarySupport j hjNonzero)
    apply Finset.mem_image.mpr
    refine ⟨u, ?_, hu⟩
    have huNonzero :
        coarseBoundaryWord ell v u ≠ 0 := by
      rw [coarseBoundaryWord, hu]
      exact hjNonzero
    simpa [hammingSupport] using huNonzero
  · intro hj
    obtain ⟨u, huSupport, hu⟩ := Finset.mem_image.mp hj
    have huNonzero : coarseBoundaryWord ell v u ≠ 0 := by
      simpa [hammingSupport] using huSupport
    have hjNonzero :
        cycleFiberChainBoundary (ell * ell) v j ≠ 0 := by
      rw [← hu]
      simpa [coarseBoundaryWord] using huNonzero
    simpa [hammingSupport] using hjNonzero

/-- Fine boundary weight equals the sampled coarse-boundary weight. -/
theorem hammingWeight_cycleBoundary_eq_coarseBoundaryWord
    (ell : Nat) [NeZero ell]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    HammingWeight (cycleFiberChainBoundary (ell * ell) v) =
      HammingWeight (coarseBoundaryWord ell v) := by
  rw [HammingWeight, HammingWeight,
    hammingSupport_cycleBoundary_eq_image_coarseBoundaryWord
      ell v hBoundarySupport,
    Finset.card_image_of_injective _
      (TwistGraph.layerEmbedding_injective ell)]

/-- The sampled fine boundary is the cyclic boundary of the coarse word. -/
theorem coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    coarseBoundaryWord ell v =
      cycleFiberChainBoundary ell (coarseFiberWord ell v) := by
  have hTwo : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  funext u
  rw [coarseBoundaryWord,
    cycleFiberChainBoundary_apply (ell * ell) (by nlinarith),
    cycleFiberChainBoundary_apply ell hTwo]
  change
    v (TwistGraph.layerEmbedding ell u) +
        v (TwistGraph.layerEmbedding ell u - 1) =
      v (TwistGraph.layerEmbedding ell u) +
        v (TwistGraph.layerEmbedding ell (u - 1))
  congr 1
  have hBlock :=
    cycleWord_block_constant_of_boundary_supported_at_zero_residue
      ell v hBoundarySupport (u - 1)
        ⟨ell - 1, Nat.sub_lt (NeZero.pos ell) Nat.zero_lt_one⟩
  rw [TwistGraph.blockPosition_previous] at hBlock
  exact hBlock

/--
Quantitative string counting: every nonzero coarse boundary endpoint costs a
length-`ell` block, with the factor two accounting for the two endpoints of
each binary run.
-/
theorem ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0) :
    ell * HammingWeight (cycleFiberChainBoundary (ell * ell) v) ≤
      2 * HammingWeight v := by
  have hFine :=
    hammingWeight_eq_ell_mul_coarseFiberWord
      ell v hBoundarySupport
  have hBoundary :=
    hammingWeight_cycleBoundary_eq_coarseBoundaryWord
      ell v hBoundarySupport
  have hCoarseBoundary :=
    coarseBoundaryWord_eq_cycleFiberChainBoundary_coarseFiberWord
      ell v hBoundarySupport
  calc
    ell * HammingWeight (cycleFiberChainBoundary (ell * ell) v) =
        ell * HammingWeight
          (cycleFiberChainBoundary ell (coarseFiberWord ell v)) := by
            rw [hBoundary, hCoarseBoundary]
    _ ≤ ell * (2 * HammingWeight (coarseFiberWord ell v)) :=
      Nat.mul_le_mul_left ell
        (hammingWeight_cycleFiberChainBoundary_le_two_mul
          ell (coarseFiberWord ell v))
    _ = 2 * HammingWeight v := by
      rw [hFine]
      ac_rfl

/--
A binary cycle chain whose nonzero boundary vertices all have residue zero
has weight at least `ell` whenever its boundary is nonzero.
-/
theorem ell_le_hammingWeight_of_cycleBoundary_supported_at_zero_residue
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (v : Word (ZMod 2) (ZMod (ell * ell)))
    (hBoundarySupport :
      ∀ j, cycleFiberChainBoundary (ell * ell) v j ≠ 0 →
        fiberResidue ell j = 0)
    (hBoundaryNonzero :
      cycleFiberChainBoundary (ell * ell) v ≠ 0) :
    ell ≤ HammingWeight v := by
  classical
  have hEll : 2 ≤ ell := by
    have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hSquare : ell ≤ ell * ell := by nlinarith
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hBoundaryNonzero
  change cycleFiberChainBoundary (ell * ell) v j ≠ 0 at hj
  have hjResidue : fiberResidue ell j = 0 :=
    hBoundarySupport j hj
  have hBlockBound
      (start : ZMod (ell * ell))
      (hStartResidue : fiberResidue ell start = 0)
      (hSome :
        ∃ k : Fin ell,
          v (start + (k.val : ZMod (ell * ell))) ≠ 0) :
      ell ≤ HammingWeight v := by
    have hRun :
        ∀ k : Nat, k < ell →
          v (start + (k : ZMod (ell * ell))) = v start := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
          have hkPrev : k < ell := by omega
          have hResidueNe :
              fiberResidue ell
                (start + ((k + 1 : Nat) : ZMod (ell * ell))) ≠ 0 := by
            rw [map_add, hStartResidue, zero_add]
            change ZMod.castHom (by exact dvd_mul_right ell ell) (ZMod ell)
              (((k + 1 : Nat) : ZMod (ell * ell))) ≠ 0
            rw [ZMod.castHom_apply,
              ZMod.cast_natCast (R := ZMod ell)
                (dvd_mul_right ell ell)]
            intro hzero
            have hval := congrArg ZMod.val hzero
            rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
            omega
          have hBoundaryZero :
              cycleFiberChainBoundary (ell * ell) v
                (start + ((k + 1 : Nat) : ZMod (ell * ell))) = 0 := by
            by_contra hne
            exact hResidueNe (hBoundarySupport _ hne)
          rw [cycleFiberChainBoundary_apply
            (ell * ell) (by nlinarith)] at hBoundaryZero
          have hStep :
              v (start + ((k + 1 : Nat) : ZMod (ell * ell))) =
                v ((start + ((k + 1 : Nat) :
                  ZMod (ell * ell))) - 1) := by
            have hneg := eq_neg_of_add_eq_zero_left hBoundaryZero
            simpa [ZMod.neg_eq_self_mod_two] using hneg
          calc
            v (start + ((k + 1 : Nat) : ZMod (ell * ell))) =
                v ((start + ((k + 1 : Nat) :
                  ZMod (ell * ell))) - 1) := hStep
            _ = v (start + (k : ZMod (ell * ell))) := by
              congr 2
              push_cast
              abel
            _ = v start := ih hkPrev
    rcases hSome with ⟨k₀, hk₀⟩
    have hStartNonzero : v start ≠ 0 := by
      rw [hRun k₀.val k₀.isLt] at hk₀
      exact hk₀
    let supportEmbedding :
        Fin ell → ↥(hammingSupport v) :=
      fun k => ⟨start + (k.val : ZMod (ell * ell)), by
        simp only [hammingSupport, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [hRun k.val k.isLt]
        exact hStartNonzero⟩
    have hInjective : Function.Injective supportEmbedding := by
      intro k l hkl
      apply Fin.ext
      have hCoord :
          start + (k.val : ZMod (ell * ell)) =
            start + (l.val : ZMod (ell * ell)) :=
        congrArg Subtype.val hkl
      have hCast :
          (k.val : ZMod (ell * ell)) =
            (l.val : ZMod (ell * ell)) :=
        add_left_cancel hCoord
      have hVal := congrArg ZMod.val hCast
      rw [ZMod.val_natCast_of_lt
          (lt_of_lt_of_le k.isLt hSquare),
        ZMod.val_natCast_of_lt
          (lt_of_lt_of_le l.isLt hSquare)] at hVal
      exact hVal
    have hCard :
        Fintype.card (Fin ell) ≤
          Fintype.card ↥(hammingSupport v) :=
      Fintype.card_le_of_injective supportEmbedding hInjective
    rw [Fintype.card_fin, Fintype.card_coe] at hCard
    simpa [HammingWeight] using hCard
  rw [cycleFiberChainBoundary_apply
    (ell * ell) (by nlinarith)] at hj
  by_cases hvj : v j = 0
  · have hvPrev : v (j - 1) ≠ 0 := by
      intro hzero
      apply hj
      rw [hvj, hzero, zero_add]
    let start : ZMod (ell * ell) := j - (ell : Nat)
    have hStartResidue : fiberResidue ell start = 0 := by
      change fiberResidue ell (j - (ell : Nat)) = 0
      rw [map_sub, hjResidue]
      have hEllResidue :
          fiberResidue ell
            ((ell : Nat) : ZMod (ell * ell)) = 0 := by
        simp [fiberResidue]
      rw [hEllResidue, sub_zero]
    apply hBlockBound start hStartResidue
    let k : Fin ell := ⟨ell - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hCoord :
        start + (k.val : ZMod (ell * ell)) = j - 1 := by
      dsimp [start, k]
      have hEllCast :
          ((ell : Nat) : ZMod (ell * ell)) =
            ((ell - 1 : Nat) : ZMod (ell * ell)) + 1 := by
        calc
          ((ell : Nat) : ZMod (ell * ell)) =
              (((ell - 1) + 1 : Nat) : ZMod (ell * ell)) := by
                congr 1
                omega
          _ = ((ell - 1 : Nat) : ZMod (ell * ell)) + 1 := by
                rw [Nat.cast_add, Nat.cast_one]
      rw [hEllCast]
      abel
    rw [hCoord]
    exact hvPrev
  · apply hBlockBound j hjResidue
    exact ⟨0, by simpa using hvj⟩

/--
For a bundle cycle, the full horizontal boundary contribution at a base
zero-cell is exactly the cycle boundary of the vertical fiber there.
-/
theorem horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
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
        ).middleCycleCode.carrier)
    (a : Fin (3 * r)) :
    horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a =
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hzZero : boundary1 D z = 0 :=
    ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  funext j
  have hj := congrFun hzZero (a, j)
  rw [boundary1_apply_eq_horizontal_add_vertical] at hj
  have hHorizontal :
      horizontalChainBoundary baseSample twistSample
          (horizontalComponent z) a j =
        -(∑ k : ZMod (ell * ell),
          D.fiberBoundary j k * z (Sum.inr (a, k))) := by
    apply eq_neg_of_add_eq_zero_left
    exact hj
  rw [hHorizontal, ZMod.neg_eq_self_mod_two]
  rfl

/--
For a fixed base check, twist violations across source layers are a
permutation of the sampled coarse boundary of the corresponding vertical
fiber.
-/
theorem hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
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
        ).middleCycleCode.carrier)
    (a : Fin (3 * r)) :
    HammingWeight
        (TwistGraph.checkColumn baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) a) =
      HammingWeight (coarseBoundaryWord ell (verticalFiber z a)) := by
  let e : ZMod ell ≃ ZMod ell :=
    (TwistGraph.typeTranslation twistSample
      (RandomTwist.checkType typeCount a)).symm
  have hWord :
      TwistGraph.checkColumn baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) a =
        reindexWord e
          (coarseBoundaryWord ell (verticalFiber z a)) := by
    funext u
    change
      TwistGraph.checkSyndrome baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) u a =
        cycleFiberChainBoundary (ell * ell) (verticalFiber z a)
          (TwistGraph.layerEmbedding ell
            (TwistGraph.outNeighbor twistSample
              (RandomTwist.checkType typeCount a) u))
    rw [twistGraph_checkSyndrome_eq_horizontalChainBoundary]
    exact congrFun
      (horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
        baseSample twistSample z hz a) _
  rw [hWord]
  exact hammingWeight_reindexWord e
    (coarseBoundaryWord ell (verticalFiber z a))

/--
Full quantitative vertical string bound: every violated twist check costs a
length-`ell` string, up to the unavoidable factor two for its endpoints.
-/
theorem ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
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
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z) :
    ell *
        TwistGraph.violationCount baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) ≤
      2 * HammingWeight (verticalComponent z) := by
  rw [TwistGraph.violationCount_eq_sum_checkColumn,
    hammingWeight_verticalComponent_eq_sum_fibers,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  rw [hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
    baseSample twistSample z hz a]
  have hSupport :
      ∀ j,
        cycleFiberChainBoundary (ell * ell) (verticalFiber z a) j ≠ 0 →
          fiberResidue ell j = 0 := by
    intro j hj
    apply fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
      baseSample twistSample z hNormalized a j
    rw [horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
      baseSample twistSample z hz a]
    exact hj
  rw [← hammingWeight_cycleBoundary_eq_coarseBoundaryWord
    ell (verticalFiber z a) hSupport]
  exact ell_mul_hammingWeight_cycleBoundary_le_two_mul_hammingWeight
    ell (verticalFiber z a) hSupport

/-- Every normalized horizontal error forces at least `ell` vertical cells. -/
theorem ell_le_hammingWeight_verticalFiber_of_mem_horizontalBoundaryShadow
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
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z)
    (a : Fin (3 * r))
    (ha :
      a ∈ horizontalBoundaryShadow baseSample twistSample
        (horizontalComponent z)) :
    ell ≤ HammingWeight (verticalFiber z a) := by
  have hBoundaryEq :=
    horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
      baseSample twistSample z hz a
  have hBoundarySupport :
      ∀ j,
        cycleFiberChainBoundary (ell * ell) (verticalFiber z a) j ≠ 0 →
          fiberResidue ell j = 0 := by
    intro j hj
    apply fiberResidue_eq_zero_of_horizontalChainBoundary_ne_zero
      baseSample twistSample z hNormalized a j
    rw [hBoundaryEq]
    exact hj
  have hBoundaryNonzero :
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) ≠ 0 := by
    rcases (mem_horizontalBoundaryShadow_iff
      baseSample twistSample (horizontalComponent z) a).1 ha with
      ⟨j, hj⟩
    intro hzero
    apply hj
    rw [hBoundaryEq]
    exact congrFun hzero j
  exact
    ell_le_hammingWeight_of_cycleBoundary_supported_at_zero_residue
      ell (verticalFiber z a) hBoundarySupport hBoundaryNonzero

/--
After sliding, vertical weight is at least `ell` times the number of base
zero-cells on which the horizontal boundary is nonzero.
-/
theorem ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
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
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z) :
    ell *
        (horizontalBoundaryShadow baseSample twistSample
          (horizontalComponent z)).card ≤
      HammingWeight (verticalComponent z) := by
  rw [hammingWeight_verticalComponent_eq_sum_fibers]
  let shadow := horizontalBoundaryShadow baseSample twistSample
    (horizontalComponent z)
  calc
    ell * shadow.card =
        ∑ _a ∈ shadow, ell := by
          simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ shadow, HammingWeight (verticalFiber z a) := by
          apply Finset.sum_le_sum
          intro a ha
          exact
            ell_le_hammingWeight_verticalFiber_of_mem_horizontalBoundaryShadow
              baseSample twistSample z hz hNormalized a ha
    _ ≤ ∑ a : Fin (3 * r), HammingWeight (verticalFiber z a) := by
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ shadow)

/--
Conditional deterministic closure of the HHO20 twist-graph step: once the
internally proved LTC good event is available, every sufficiently light
normalized horizontal sector is controlled by the real vertical weight.
-/
theorem horizontalComponent_le_250_mul_verticalComponent_of_twistGraphLTC
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z)
    (hSmall :
      5000 * Delta * HammingWeight (horizontalComponent z) ≤
        ell * (4 * r)) :
    HammingWeight (horizontalComponent z) ≤
      250 * HammingWeight (verticalComponent z) := by
  have hSmallTwist :
      5000 * Delta *
          HammingWeight (twistGraphWordOfHorizontalComponent z) ≤
        ell * (4 * r) := by
    rw [hammingWeight_twistGraphWordOfHorizontalComponent
      z hNormalized]
    exact hSmall
  have hSound :=
    hLTC (twistGraphWordOfHorizontalComponent z) hSmallTwist
  rw [hammingWeight_twistGraphWordOfHorizontalComponent
    z hNormalized] at hSound
  have hViolVertical :
      TwistGraph.violationCount baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) ≤
        HammingWeight (verticalComponent z) :=
    le_trans
      (twistGraph_violationCount_le_ell_mul_horizontalBoundaryShadow
        baseSample twistSample z)
      (ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
        baseSample twistSample z hz hNormalized)
  exact hSound.trans (Nat.mul_le_mul_left 250 hViolVertical)

/--
The quantitative version retaining the HHO20 string-length factor:
`ell * |h| ≤ 500 * |v|` in the small-word LTC regime.
-/
theorem ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z)
    (hSmall :
      5000 * Delta * HammingWeight (horizontalComponent z) ≤
        ell * (4 * r)) :
    ell * HammingWeight (horizontalComponent z) ≤
      500 * HammingWeight (verticalComponent z) := by
  have hSmallTwist :
      5000 * Delta *
          HammingWeight (twistGraphWordOfHorizontalComponent z) ≤
        ell * (4 * r) := by
    rw [hammingWeight_twistGraphWordOfHorizontalComponent
      z hNormalized]
    exact hSmall
  have hSound :=
    hLTC (twistGraphWordOfHorizontalComponent z) hSmallTwist
  rw [hammingWeight_twistGraphWordOfHorizontalComponent
    z hNormalized] at hSound
  have hStrings :=
    ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
      baseSample twistSample z hz hNormalized
  calc
    ell * HammingWeight (horizontalComponent z) ≤
        ell * (250 *
          TwistGraph.violationCount baseSample twistSample
            (twistGraphWordOfHorizontalComponent z)) :=
      Nat.mul_le_mul_left ell hSound
    _ = 250 * (ell *
          TwistGraph.violationCount baseSample twistSample
            (twistGraphWordOfHorizontalComponent z)) := by ac_rfl
    _ ≤ 250 * (2 * HammingWeight (verticalComponent z)) :=
      Nat.mul_le_mul_left 250 hStrings
    _ = 500 * HammingWeight (verticalComponent z) := by ring

/--
If the boundary of a support-induced cluster is nonzero at a coordinate, it
equals the boundary of the entire horizontal sector there.  Indeed, one
selected contributor at that coordinate overlaps every other supported
contributor, so cluster closure selects all of them.
-/
theorem horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hg :
      horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j ≠ 0) :
    horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j =
      horizontalChainBoundary baseSample twistSample
        (horizontalComponent z) a j := by
  classical
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let h := horizontalClusterSubchain
    baseSample twistSample z root
  have hSum :
      (∑ b : Fin (4 * r),
        RandomBase.boundary baseSample a b *
          h (b, ((D.connection b a).onOne.symm) j)) ≠ 0 := by
    simpa [horizontalChainBoundary, h, D] using hg
  obtain ⟨b₀, _hb₀Mem, hb₀Term⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hSum
  let x : Fin (4 * r) × ZMod (ell * ell) :=
    (b₀, ((D.connection b₀ a).onOne.symm) j)
  have hb₀Boundary :
      RandomBase.boundary baseSample a b₀ ≠ 0 := by
    intro hb₀
    apply hb₀Term
    simp [hb₀]
  have hxSubchain : h x ≠ 0 := by
    intro hx
    apply hb₀Term
    simp [x, hx]
  have hxCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root x :=
    inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
      baseSample twistSample z root x hxSubchain
  have hxEq : h x = z (Sum.inl x) := by
    simp [h, horizontalClusterSubchain, hxCluster]
  have hxSupport : z (Sum.inl x) ≠ 0 := by
    rw [← hxEq]
    exact hxSubchain
  simp only [horizontalChainBoundary]
  apply Finset.sum_congr rfl
  intro b _hbMem
  by_cases hbBoundary :
      RandomBase.boundary baseSample a b = 0
  · simp [hbBoundary]
  let y : Fin (4 * r) × ZMod (ell * ell) :=
    (b, ((D.connection b a).onOne.symm) j)
  by_cases hySupport : z (Sum.inl y) = 0
  · have hySubchain : h y = 0 := by
      simp [h, horizontalClusterSubchain, hySupport]
    change RandomBase.boundary baseSample a b * h y =
      RandomBase.boundary baseSample a b * horizontalComponent z y
    rw [hySubchain]
    have hyHorizontal : horizontalComponent z y = 0 := by
      simpa [horizontalComponent] using hySupport
    rw [hyHorizontal]
  have hxy : HorizontalBoundaryOverlap
      baseSample twistSample x y := by
    refine ⟨a, hb₀Boundary, hbBoundary, ?_⟩
    simp [x, y, D, RandomTwist.fiberBundleData,
      multipleRotationCycleData, cycleData, cycleRotationAutomorphism]
  have hyCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root y :=
    inSameSupportedHorizontalCluster_tail
      baseSample twistSample z root x y
      hxCluster hxSupport hySupport hxy
  have hyEq : h y = z (Sum.inl y) := by
    simp [h, horizontalClusterSubchain, hyCluster]
  change RandomBase.boundary baseSample a b * h y =
    RandomBase.boundary baseSample a b * horizontalComponent z y
  rw [hyEq]
  rfl

/--
Thus every nonzero boundary coordinate of a support-induced cluster is a
genuine boundary coordinate of the vertical cycle fiber.
-/
theorem horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) (j : ZMod (ell * ell))
    (hg :
      horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j ≠ 0) :
    horizontalChainBoundary baseSample twistSample
        (horizontalClusterSubchain
          baseSample twistSample z root) a j =
      cycleFiberChainBoundary (ell * ell) (verticalFiber z a) j := by
  rw [horizontalChainBoundary_cluster_eq_horizontalComponent_of_ne_zero
    baseSample twistSample z root a j hg]
  exact congrFun
    (horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
      baseSample twistSample z hz a) j

/-- The vertical sector of a positive slide is toggled by its horizontal boundary. -/
theorem verticalFiber_oneStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    verticalFiber
        (oneStepSlide baseSample twistSample z h) a =
      verticalFiber z a +
        horizontalChainBoundary baseSample twistSample h a := by
  funext j
  change
    verticalFiber z a j +
        verticalFiber
          (boundary2
            (RandomTwist.fiberBundleData baseSample twistSample)
            (oneStepSlideTwoChain h)) a j =
      verticalFiber z a j +
        horizontalChainBoundary baseSample twistSample h a j
  rw [verticalFiber_boundary2_oneStepSlideTwoChain]
  rfl

/-- Toggle the edge immediately before each selected cycle vertex. -/
def backwardVertexToggle
    (n : Nat) [NeZero n]
    (g : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun j => g (j + 1)

/--
The vertical sector of a negative slide is the backward toggle of the same
horizontal boundary word.
-/
theorem verticalFiber_negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (a : Fin (3 * r)) :
    verticalFiber
        (negativeStepSlide baseSample twistSample z h) a =
      verticalFiber z a +
        backwardVertexToggle (ell * ell)
          (horizontalChainBoundary baseSample twistSample h a) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  funext j
  change
    verticalFiber z a j +
        verticalFiber
          (boundary2 D
            (negativeStepSlideTwoChain (ell * ell) h)) a j =
      verticalFiber z a j +
        horizontalChainBoundary baseSample twistSample h a (j + 1)
  congr 1
  change boundary2 D
      (negativeStepSlideTwoChain (ell * ell) h) (Sum.inr (a, j)) =
    horizontalChainBoundary baseSample twistSample h a (j + 1)
  rw [boundary2_apply_vertical]
  change
    (∑ b : Fin (4 * r),
      RandomBase.boundary baseSample a b *
        h (b, ((D.connection b a).onOne.symm) j + 1)) =
    ∑ b : Fin (4 * r),
      RandomBase.boundary baseSample a b *
        h (b, ((D.connection b a).onOne.symm) (j + 1))
  apply Finset.sum_congr rfl
  intro b _hb
  congr 2
  simp [D, RandomTwist.fiberBundleData,
    multipleRotationCycleData, cycleData, cycleRotationAutomorphism]
  abel

/--
At a genuine boundary vertex of a binary cycle chain, toggling the edge after
the vertex and toggling the edge before it have complementary weight changes.
-/
theorem binary_cycle_toggle_indicator_identity
    (a b g : ZMod 2)
    (hg : g ≠ 0 → g = a + b) :
    (if a + g ≠ 0 then 1 else 0) +
        (if b + g ≠ 0 then 1 else 0) =
      (if a ≠ 0 then 1 else 0) +
        (if b ≠ 0 then 1 else 0) := by
  by_cases hgZero : g = 0
  · simp [hgZero]
  have hOneAddOne : (1 : ZMod 2) + 1 = 0 := by
    exact ZMod.natCast_self 2
  have hgOne : g = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero g hgZero
  by_cases haZero : a = 0
  · by_cases hbZero : b = 0
    · exfalso
      apply hgZero
      rw [hg hgZero, haZero, hbZero, zero_add]
    · have hbOne : b = 1 :=
        RandomBase.zmod2_eq_one_of_ne_zero b hbZero
      simp [haZero, hbOne, hgOne, hOneAddOne]
  · have haOne : a = 1 :=
      RandomBase.zmod2_eq_one_of_ne_zero a haZero
    by_cases hbZero : b = 0
    · simp [haOne, hbZero, hgOne, hOneAddOne]
    · have hbOne : b = 1 :=
        RandomBase.zmod2_eq_one_of_ne_zero b hbZero
      exfalso
      apply hgZero
      rw [hg hgZero, haOne, hbOne]
      exact ZMod.natCast_self 2

/--
If a selected vertex set is supported inside the actual boundary of a cycle
chain, the two possible vertical slides have exactly complementary total
weight changes.
-/
theorem hammingWeight_forward_add_backward_cycle_toggles
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (v g : Word (ZMod 2) (ZMod n))
    (hgBoundary : ∀ j, g j ≠ 0 →
      g j = cycleFiberChainBoundary n v j) :
    HammingWeight (v + g) +
        HammingWeight (v + backwardVertexToggle n g) =
      2 * HammingWeight v := by
  rw [hammingWeight_eq_sum_indicator,
    hammingWeight_eq_sum_indicator,
    hammingWeight_eq_sum_indicator]
  have hBackward :
      (∑ j : ZMod n,
        if (v + backwardVertexToggle n g) j ≠ 0 then 1 else 0) =
      ∑ j : ZMod n,
        if v (j - 1) + g j ≠ 0 then 1 else 0 := by
    apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
    intro j
    change
      (if v j + g (j + 1) ≠ 0 then 1 else 0) =
      if v (j + 1 - 1) + g (j + 1) ≠ 0 then 1 else 0
    simp
  rw [hBackward, ← Finset.sum_add_distrib]
  have hPointwise (j : ZMod n) :
      (if v j + g j ≠ 0 then 1 else 0) +
          (if v (j - 1) + g j ≠ 0 then 1 else 0) =
        (if v j ≠ 0 then 1 else 0) +
          (if v (j - 1) ≠ 0 then 1 else 0) := by
    apply binary_cycle_toggle_indicator_identity
    intro hgj
    rw [hgBoundary j hgj, cycleFiberChainBoundary_apply n hn]
  have hPointwiseSum :
      (∑ j : ZMod n,
        ((if v j + g j ≠ 0 then 1 else 0) +
          (if v (j - 1) + g j ≠ 0 then 1 else 0))) =
      ∑ j : ZMod n,
        ((if v j ≠ 0 then 1 else 0) +
          (if v (j - 1) ≠ 0 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact hPointwise j
  change
    (∑ j : ZMod n,
      ((if v j + g j ≠ 0 then 1 else 0) +
        (if v (j - 1) + g j ≠ 0 then 1 else 0))) =
      2 * ∑ j : ZMod n, if v j ≠ 0 then 1 else 0
  rw [hPointwiseSum]
  rw [Finset.sum_add_distrib]
  have hShift :
      (∑ j : ZMod n, if v (j - 1) ≠ 0 then 1 else 0) =
        ∑ j : ZMod n, if v j ≠ 0 then 1 else 0 := by
    exact Fintype.sum_equiv (Equiv.addRight (-1 : ZMod n))
      (fun j => if v (j - 1) ≠ 0 then 1 else 0)
      (fun j => if v j ≠ 0 then 1 else 0)
      (by
        intro j
        change (if v (j - 1) ≠ 0 then (1 : Nat) else 0) =
          (if v (j + -1) ≠ 0 then 1 else 0)
        rw [sub_eq_add_neg])
  rw [hShift]
  omega

/--
At every base zero-cell, the positive cluster slide and the complementary
backward toggle have vertical weights summing to twice the original vertical
fiber weight.
-/
theorem hammingWeight_verticalFiber_slideCluster_add_backward
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) :
    HammingWeight
        (verticalFiber
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) +
      HammingWeight
        (verticalFiber z a +
          backwardVertexToggle (ell * ell)
            (horizontalChainBoundary baseSample twistSample
              (horizontalClusterSubchain
                baseSample twistSample z root) a)) =
      2 * HammingWeight (verticalFiber z a) := by
  rw [verticalFiber_oneStepSlide]
  apply hammingWeight_forward_add_backward_cycle_toggles
    (ell * ell) (by
      have hEll : 2 ≤ ell := by
        have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
        omega
      nlinarith)
  intro j hgj
  exact
    horizontalChainBoundary_cluster_eq_cycleFiberChainBoundary_of_ne_zero
      baseSample twistSample z hz root a j hgj

/--
The abstract backward toggle above is exactly the vertical sector of the
explicit negative cluster slide.
-/
theorem hammingWeight_verticalFiber_positive_add_negative_slideCluster
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (a : Fin (3 * r)) :
    HammingWeight
        (verticalFiber
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) +
      HammingWeight
        (verticalFiber
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) a) =
      2 * HammingWeight (verticalFiber z a) := by
  rw [verticalFiber_negativeStepSlide]
  exact hammingWeight_verticalFiber_slideCluster_add_backward
    baseSample twistSample z hz root a

/-- Positive and negative cluster slides have complementary total vertical cost. -/
theorem hammingWeight_verticalComponent_positive_add_negative_slideCluster
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (verticalComponent
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) +
      HammingWeight
        (verticalComponent
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root))) =
      2 * HammingWeight (verticalComponent z) := by
  rw [hammingWeight_verticalComponent_eq_sum_fibers,
    hammingWeight_verticalComponent_eq_sum_fibers,
    hammingWeight_verticalComponent_eq_sum_fibers,
    ← Finset.sum_add_distrib]
  calc
    (∑ a : Fin (3 * r),
      (HammingWeight
          (verticalFiber
            (oneStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root)) a) +
        HammingWeight
          (verticalFiber
            (negativeStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root)) a))) =
      ∑ a : Fin (3 * r),
        2 * HammingWeight (verticalFiber z a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            hammingWeight_verticalFiber_positive_add_negative_slideCluster
              baseSample twistSample z hz root a
    _ = 2 * ∑ a : Fin (3 * r),
        HammingWeight (verticalFiber z a) := by
          rw [Finset.mul_sum]

/--
The two explicit directions together cost at most twice the original total
weight: horizontally each direction is nonincreasing, while vertically their
costs are exactly complementary.
-/
theorem hammingWeight_positive_add_negative_slideCluster_le
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) +
      HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤
      2 * HammingWeight z := by
  have hPositiveHorizontal :
      HammingWeight
          (horizontalComponent
            (oneStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root))) ≤
        HammingWeight (horizontalComponent z) :=
    hammingWeight_horizontalComponent_slideCluster_le
      baseSample twistSample z root
  have hNegativeHorizontal :
      HammingWeight
          (horizontalComponent
            (negativeStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root))) ≤
        HammingWeight (horizontalComponent z) :=
    hammingWeight_horizontalComponent_negativeSlideCluster_le
      baseSample twistSample z root
  have hVertical :
      HammingWeight
          (verticalComponent
            (oneStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root))) +
        HammingWeight
          (verticalComponent
            (negativeStepSlide baseSample twistSample z
              (horizontalClusterSubchain
                baseSample twistSample z root))) =
        2 * HammingWeight (verticalComponent z) :=
    hammingWeight_verticalComponent_positive_add_negative_slideCluster
      baseSample twistSample z hz root
  rw [hammingWeight_eq_horizontal_add_vertical,
    hammingWeight_eq_horizontal_add_vertical,
    hammingWeight_eq_horizontal_add_vertical]
  omega

/--
Consequently at least one of the two explicit sliding directions does not
increase total Hamming weight.
-/
theorem exists_slideCluster_direction_hammingWeight_le
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤ HammingWeight z ∨
      HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) ≤ HammingWeight z := by
  have h :=
    hammingWeight_positive_add_negative_slideCluster_le
      baseSample twistSample z hz root
  omega

/-- Sliding a bundle cycle produces another bundle cycle. -/
theorem oneStepSlide_mem_middleCycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    oneStepSlide baseSample twistSample z h ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rw [(chainComplex D).mem_middleCycleCode_iff]
  rw [oneStepSlide, map_add]
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  rw [hzZero, zero_add]
  have hsquare := congrArg
    (fun f : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
        Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
      f (oneStepSlideTwoChain h))
    (boundary_squared D)
  exact hsquare

/-- A sliding step does not change the bundle-to-base homology projection. -/
theorem homologyBaseProjection_oneStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    homologyBaseProjection
        (oneStepSlide baseSample twistSample z h) =
      homologyBaseProjection z := by
  rw [oneStepSlide, homologyBaseProjection_add,
    homologyBaseProjection_boundary2_fiberBundleData_eq_zero,
    add_zero]

/-- Adding the sliding boundary preserves boundary membership in both directions. -/
theorem oneStepSlide_mem_middleBoundaryCode_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    oneStepSlide baseSample twistSample z h ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let c := oneStepSlideTwoChain h
  constructor
  · intro hSlide
    rcases ((chainComplex D).mem_middleBoundaryCode_iff
      (oneStepSlide baseSample twistSample z h)).1 hSlide with
      ⟨d, hd⟩
    apply ((chainComplex D).mem_middleBoundaryCode_iff z).2
    refine ⟨c + d, ?_⟩
    change boundary2 D (c + d) = z
    rw [map_add]
    have hd' : boundary2 D d = z + boundary2 D c := by
      exact hd
    rw [hd']
    funext q
    let w := boundary2 D c q
    change w + (z q + w) = z q
    have hww : w + w = 0 := by
      calc
        w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel w
    calc
      w + (z q + w) = z q + (w + w) := by abel
      _ = z q := by rw [hww, add_zero]
  · intro hzBoundary
    rcases ((chainComplex D).mem_middleBoundaryCode_iff z).1
      hzBoundary with ⟨d, hd⟩
    apply ((chainComplex D).mem_middleBoundaryCode_iff
      (oneStepSlide baseSample twistSample z h)).2
    refine ⟨d + c, ?_⟩
    change boundary2 D (d + c) =
      oneStepSlide baseSample twistSample z h
    have hd' : boundary2 D d = z := hd
    rw [map_add, hd']
    rfl

/-- Consequently, one sliding step preserves homological nontriviality. -/
theorem oneStepSlide_not_mem_middleBoundaryCode_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    oneStepSlide baseSample twistSample z h ∉
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∉
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  exact not_congr
    (oneStepSlide_mem_middleBoundaryCode_iff
      baseSample twistSample z h)

/-- A negative slide of a bundle cycle also produces a bundle cycle. -/
theorem negativeStepSlide_mem_middleCycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell)))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    negativeStepSlide baseSample twistSample z h ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rw [(chainComplex D).mem_middleCycleCode_iff]
  rw [negativeStepSlide, map_add]
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  rw [hzZero, zero_add]
  have hsquare := congrArg
    (fun f : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
        Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
      f (negativeStepSlideTwoChain (ell * ell) h))
    (boundary_squared D)
  exact hsquare

/-- A negative slide leaves the bundle-to-base homology projection unchanged. -/
theorem homologyBaseProjection_negativeStepSlide
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    homologyBaseProjection
        (negativeStepSlide baseSample twistSample z h) =
      homologyBaseProjection z := by
  rw [negativeStepSlide, homologyBaseProjection_add,
    homologyBaseProjection_boundary2_fiberBundleData_eq_zero,
    add_zero]

/-- Adding a negative sliding boundary preserves boundary membership. -/
theorem negativeStepSlide_mem_middleBoundaryCode_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    negativeStepSlide baseSample twistSample z h ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let c := negativeStepSlideTwoChain (ell * ell) h
  have hc : boundary2 D c ∈
      (chainComplex D).middleBoundaryCode.carrier :=
    ((chainComplex D).mem_middleBoundaryCode_iff
      (boundary2 D c)).2 ⟨c, rfl⟩
  change z + boundary2 D c ∈
      (chainComplex D).middleBoundaryCode.carrier ↔
    z ∈ (chainComplex D).middleBoundaryCode.carrier
  exact (chainComplex D).middleBoundaryCode.carrier.add_mem_iff_left hc

/-- Consequently, a negative slide preserves homological nontriviality. -/
theorem negativeStepSlide_not_mem_middleBoundaryCode_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (h : Word (ZMod 2)
      (Fin (4 * r) × ZMod (ell * ell))) :
    negativeStepSlide baseSample twistSample z h ∉
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∉
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  exact not_congr
    (negativeStepSlide_mem_middleBoundaryCode_iff
      baseSample twistSample z h)

/-! ## Minimum-weight representatives of one homology class -/

/--
A representative is minimum weight among all additions of degree-two
boundaries.  The comparison space is construction-owned and finite.
-/
def IsHomologyClassWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) : Prop :=
  ∀ c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))),
    HammingWeight z ≤
      HammingWeight
        (z +
          boundary2
            (RandomTwist.fiberBundleData baseSample twistSample) c)

/-- Adding an arbitrary degree-two boundary to a cycle preserves the cycle condition. -/
theorem add_boundary2_mem_middleCycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier) :
    z + boundary2
        (RandomTwist.fiberBundleData baseSample twistSample) c ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rw [(chainComplex D).mem_middleCycleCode_iff]
  change boundary1 D
    (z + boundary2 D c) = 0
  rw [map_add]
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  change boundary1 D z = 0 at hzZero
  rw [hzZero, zero_add]
  have hsquare := congrArg
    (fun f : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
        Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
      f c)
    (boundary_squared D)
  simpa using hsquare

/-- Equal-weight addition of a boundary preserves class-weight minimality. -/
theorem IsHomologyClassWeightMinimal.add_boundary2
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hMinimal :
      IsHomologyClassWeightMinimal baseSample twistSample z)
    (c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))))
    (hWeight :
      HammingWeight
          (z + boundary2
            (RandomTwist.fiberBundleData baseSample twistSample) c) =
        HammingWeight z) :
    IsHomologyClassWeightMinimal baseSample twistSample
      (z + boundary2
        (RandomTwist.fiberBundleData baseSample twistSample) c) := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  intro d
  have hcd := hMinimal (c + d)
  change HammingWeight (z + boundary2 D c) ≤
    HammingWeight
      ((z + boundary2 D c) + boundary2 D d)
  rw [hWeight]
  simpa [map_add, add_assoc] using hcd

/--
Every bundle cycle has a no-heavier, homologous representative that minimizes
weight over its entire degree-two-boundary coset.
-/
theorem exists_homologyClassWeightMinimal
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
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHomologyClassWeightMinimal baseSample twistSample z' := by
  classical
  let D := RandomTwist.fiberBundleData baseSample twistSample
  let weight := fun c : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell))) =>
    HammingWeight (z + boundary2 D c)
  obtain ⟨c, _hc, hleast⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset
        (Word (ZMod 2)
          (C2Index (Fin (4 * r)) (ZMod (ell * ell)))))
      weight Finset.univ_nonempty
  let z' := z + boundary2 D c
  have hzCycle : z' ∈ (chainComplex D).middleCycleCode.carrier := by
    rw [(chainComplex D).mem_middleCycleCode_iff]
    change boundary1 D (z + boundary2 D c) = 0
    rw [map_add]
    have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
    change boundary1 D z = 0 at hzZero
    rw [hzZero, zero_add]
    have hsquare := congrArg
      (fun f : Word (ZMod 2)
          (C2Index (Fin (4 * r)) (ZMod (ell * ell))) →ₗ[ZMod 2]
          Word (ZMod 2)
            (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
        f c)
      (boundary_squared D)
    simpa using hsquare
  have hWeight : HammingWeight z' ≤ HammingWeight z := by
    have hzero := hleast 0 (Finset.mem_univ 0)
    simpa [weight, z'] using hzero
  have hHomologous : z' + z ∈
      (chainComplex D).middleBoundaryCode.carrier := by
    apply ((chainComplex D).mem_middleBoundaryCode_iff (z' + z)).2
    refine ⟨c, ?_⟩
    funext q
    change boundary2 D c q =
      (z q + boundary2 D c q) + z q
    have hzz : z q + z q = 0 := by
      calc
        z q + z q = z q + (-z q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    calc
      boundary2 D c q =
          (z q + z q) + boundary2 D c q := by rw [hzz, zero_add]
      _ = (z q + boundary2 D c q) + z q := by abel
  have hMinimal :
      IsHomologyClassWeightMinimal baseSample twistSample z' := by
    intro d
    have hcd := hleast (c + d) (Finset.mem_univ (c + d))
    change HammingWeight (z + boundary2 D c) ≤
      HammingWeight
        ((z + boundary2 D c) + boundary2 D d)
    simpa [weight, map_add, add_assoc] using hcd
  exact ⟨z', hzCycle, hWeight, hHomologous, hMinimal⟩

/--
At a minimum-weight representative, both cluster-slide directions preserve
weight exactly; neither direction can lie below the class minimum, and their
sum is already bounded above by twice that minimum.
-/
theorem hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
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
        ).middleCycleCode.carrier)
    (hMinimal :
      IsHomologyClassWeightMinimal baseSample twistSample z)
    (root : Fin (4 * r) × ZMod (ell * ell)) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) =
        HammingWeight z ∧
    HammingWeight
        (negativeStepSlide baseSample twistSample z
          (horizontalClusterSubchain
            baseSample twistSample z root)) =
        HammingWeight z := by
  have hPositiveLower :
      HammingWeight z ≤
        HammingWeight
          (oneStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) := by
    exact hMinimal
      (oneStepSlideTwoChain
        (horizontalClusterSubchain
          baseSample twistSample z root))
  have hNegativeLower :
      HammingWeight z ≤
        HammingWeight
          (negativeStepSlide baseSample twistSample z
            (horizontalClusterSubchain
              baseSample twistSample z root)) := by
    exact hMinimal
      (negativeStepSlideTwoChain (ell * ell)
        (horizontalClusterSubchain
          baseSample twistSample z root))
  have hSum :=
    hammingWeight_positive_add_negative_slideCluster_le
      baseSample twistSample z hz root
  constructor <;> omega

/--
HHO20 Lemma `sliding`, with all finite choices internalized: every bundle
cycle has a homologous representative of no greater weight whose nonzero
horizontal cells all lie at fiber positions congruent to zero modulo `ell`.
-/
theorem exists_homologous_isHorizontallyResidueNormalized
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
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized z' := by
  classical
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rcases exists_homologyClassWeightMinimal
      baseSample twistSample z hz with
    ⟨zMin, hzMin, hMinWeight, hMinHomologous, hMinClass⟩
  let candidates : Finset
      (Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) :=
    Finset.univ.filter (fun c =>
      HammingWeight (zMin + boundary2 D c) = HammingWeight zMin)
  have hZeroCandidate : (0 : Word (ZMod 2)
      (C2Index (Fin (4 * r)) (ZMod (ell * ell)))) ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [map_zero, add_zero]⟩
  obtain ⟨c, hcCandidate, hleast⟩ :=
    Finset.exists_min_image candidates
      (fun d => horizontalResiduePotential
        (zMin + boundary2 D d))
      ⟨0, hZeroCandidate⟩
  let z' := zMin + boundary2 D c
  have hcWeight :
      HammingWeight z' = HammingWeight zMin := by
    exact (Finset.mem_filter.mp hcCandidate).2
  have hz' : z' ∈ (chainComplex D).middleCycleCode.carrier := by
    exact add_boundary2_mem_middleCycleCode
      baseSample twistSample zMin c hzMin
  have hClass' :
      IsHomologyClassWeightMinimal baseSample twistSample z' := by
    exact hMinClass.add_boundary2
      baseSample twistSample zMin c hcWeight
  have hPrimeMinHomologous :
      z' + zMin ∈ (chainComplex D).middleBoundaryCode.carrier := by
    apply ((chainComplex D).mem_middleBoundaryCode_iff
      (z' + zMin)).2
    refine ⟨c, ?_⟩
    funext q
    change boundary2 D c q =
      (zMin q + boundary2 D c q) + zMin q
    have hmm : zMin q + zMin q = 0 := by
      calc
        zMin q + zMin q = zMin q + (-zMin q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    calc
      boundary2 D c q =
          (zMin q + zMin q) + boundary2 D c q := by
            rw [hmm, zero_add]
      _ = (zMin q + boundary2 D c q) + zMin q := by abel
  have hPrimeHomologous :
      z' + z ∈ (chainComplex D).middleBoundaryCode.carrier := by
    have hsum := Submodule.add_mem _
      hPrimeMinHomologous hMinHomologous
    have heq :
        (z' + zMin) + (zMin + z) = z' + z := by
      funext q
      change (z' q + zMin q) + (zMin q + z q) = z' q + z q
      have hmm : zMin q + zMin q = 0 := by
        calc
          zMin q + zMin q = zMin q + (-zMin q) := by
            rw [ZMod.neg_eq_self_mod_two]
          _ = 0 := add_neg_cancel _
      calc
        (z' q + zMin q) + (zMin q + z q) =
            z' q + (zMin q + zMin q) + z q := by abel
        _ = z' q + z q := by rw [hmm, add_zero]
    rw [heq] at hsum
    exact hsum
  have hNormalized : IsHorizontallyResidueNormalized z' := by
    by_contra hNotNormalized
    have hBad :
        ∃ b : Fin (4 * r), ∃ i : ZMod (ell * ell),
          z' (Sum.inl (b, i)) ≠ 0 ∧ fiberResidue ell i ≠ 0 := by
      unfold IsHorizontallyResidueNormalized at hNotNormalized
      push Not at hNotNormalized
      exact hNotNormalized
    rcases hBad with ⟨b, i, hSupport, hResidue⟩
    let root : Fin (4 * r) × ZMod (ell * ell) := (b, i)
    let h := horizontalClusterSubchain
      baseSample twistSample z' root
    let e : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))) :=
      c + oneStepSlideTwoChain h
    have hSlideWeight :
        HammingWeight
            (oneStepSlide baseSample twistSample z' h) =
          HammingWeight z' := by
      exact
        (hammingWeight_positive_eq_and_negative_eq_of_homologyClassWeightMinimal
          baseSample twistSample z' hz' hClass' root).1
    have hWordEq :
        zMin + boundary2 D e =
          oneStepSlide baseSample twistSample z' h := by
      funext q
      change zMin q +
          boundary2 D (c + oneStepSlideTwoChain h) q =
        (zMin q + boundary2 D c q) +
          boundary2 D (oneStepSlideTwoChain h) q
      rw [map_add]
      change zMin q +
          (boundary2 D c q +
            boundary2 D (oneStepSlideTwoChain h) q) =
        (zMin q + boundary2 D c q) +
          boundary2 D (oneStepSlideTwoChain h) q
      abel
    have heCandidate : e ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ e, ?_⟩
      rw [hWordEq, hSlideWeight, hcWeight]
    have hLeastPotential := hleast e heCandidate
    have hPotentialStrict :
        horizontalResiduePotential
            (oneStepSlide baseSample twistSample z' h) <
          horizontalResiduePotential z' := by
      exact horizontalResiduePotential_oneStepSlideCluster_lt
        baseSample twistSample z' root hSupport hResidue
    change horizontalResiduePotential z' ≤
      horizontalResiduePotential (zMin + boundary2 D e) at hLeastPotential
    rw [hWordEq] at hLeastPotential
    exact (not_lt_of_ge hLeastPotential) hPotentialStrict
  refine ⟨z', ?_, ?_, ?_, hNormalized⟩
  · simpa [D] using hz'
  · rw [hcWeight]
    exact hMinWeight
  · simpa [D] using hPrimeHomologous

/-- Homologous bundle words have the same bundle-to-base homology projection. -/
theorem homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z' z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hHomologous :
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier) :
    homologyBaseProjection z' = homologyBaseProjection z := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  rcases ((chainComplex D).mem_middleBoundaryCode_iff
      (z' + z)).1 hHomologous with ⟨c, hc⟩
  have hProjection :
      homologyBaseProjection (z' + z) = 0 := by
    rw [← hc]
    exact homologyBaseProjection_boundary2_fiberBundleData_eq_zero
      baseSample twistSample c
  rw [homologyBaseProjection_add] at hProjection
  funext b
  have hb := congrFun hProjection b
  have hneg := eq_neg_of_add_eq_zero_left hb
  rw [ZMod.neg_eq_self_mod_two] at hneg
  exact hneg

/-- Homologous bundle words are boundaries simultaneously. -/
theorem mem_middleBoundaryCode_iff_of_add_mem
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z' z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hHomologous :
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier) :
    z' ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ↔
      z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  let S := (chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
    ).middleBoundaryCode.carrier
  have hCancelLeft : (z' + z) + z' = z := by
    funext q
    have hself : z' q + z' q = 0 := by
      calc
        z' q + z' q = z' q + (-z' q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    change (z' q + z q) + z' q = z q
    calc
      (z' q + z q) + z' q = (z' q + z' q) + z q := by abel
      _ = z q := by rw [hself, zero_add]
  have hCancelRight : (z' + z) + z = z' := by
    funext q
    have hself : z q + z q = 0 := by
      calc
        z q + z q = z q + (-z q) := by
          rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel _
    change (z' q + z q) + z q = z' q
    calc
      (z' q + z q) + z q = z' q + (z q + z q) := by abel
      _ = z' q := by rw [hself, add_zero]
  constructor
  · intro hz'
    have hsum : (z' + z) + z' ∈ S :=
      Submodule.add_mem S hHomologous hz'
    rw [hCancelLeft] at hsum
    exact hsum
  · intro hz
    have hsum : (z' + z) + z ∈ S :=
      Submodule.add_mem S hHomologous hz
    rw [hCancelRight] at hsum
    exact hsum

/--
Packaged sliding reduction for the homology-distance argument.  All
downstream invariants and the vertical error-shadow bound are exposed
together on one construction-owned representative.
-/
theorem exists_slidHomologyRepresentative
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
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      homologyBaseProjection z' = homologyBaseProjection z ∧
      (z' ∉
          (chainComplex
            (RandomTwist.fiberBundleData baseSample twistSample)
            ).middleBoundaryCode.carrier ↔
        z ∉
          (chainComplex
            (RandomTwist.fiberBundleData baseSample twistSample)
            ).middleBoundaryCode.carrier) ∧
      IsHorizontallyResidueNormalized z' ∧
      ell *
          (horizontalBoundaryShadow baseSample twistSample
            (horizontalComponent z')).card ≤
        HammingWeight (verticalComponent z') := by
  rcases exists_homologous_isHorizontallyResidueNormalized
      baseSample twistSample z hz with
    ⟨z', hz', hWeight, hHomologous, hNormalized⟩
  refine ⟨z', hz', hWeight, hHomologous, ?_, ?_,
    hNormalized, ?_⟩
  · exact homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
      baseSample twistSample z' z hHomologous
  · exact not_congr
      (mem_middleBoundaryCode_iff_of_add_mem
        baseSample twistSample z' z hHomologous)
  · exact ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
      baseSample twistSample z' hz' hNormalized

/--
Conditional HHO20 `homweight` closure with all constants cleared to natural
number inequalities.  The LTC proposition here is the internal random good
event; the final construction theorem must obtain it from the samplers.
-/
theorem homologyWeight_bound_of_twistGraphLTC
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (hDelta : 1 ≤ Delta)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier) :
    ell * (4 * r) ≤
      5000 * Delta * HammingWeight z := by
  rcases exists_slidHomologyRepresentative
      baseSample twistSample z hz with
    ⟨z', hz', hWeight, _hHomologous, _hProjection,
      hNontrivialIff, hNormalized, _hShadow⟩
  have hz'Nontrivial := hNontrivialIff.mpr hzNontrivial
  have hBase :=
    baseDistance_bound_of_nontrivial_bundleCycle
      baseSample twistSample hRank hDistance z' hz' hz'Nontrivial
  have hProjection :=
    hammingWeight_homologyBaseProjection_le_horizontalComponent z'
  have hBaseHorizontal :
      4 * r ≤ 5 * HammingWeight (horizontalComponent z') :=
    hBase.trans (Nat.mul_le_mul_left 5 hProjection)
  have hHorizontalTotal :
      HammingWeight (horizontalComponent z') ≤ HammingWeight z' :=
    hammingWeight_horizontalComponent_le z'
  have hVerticalTotal :
      HammingWeight (verticalComponent z') ≤ HammingWeight z' := by
    have hDecomp := hammingWeight_eq_horizontal_add_vertical z'
    omega
  by_cases hSmall :
      5000 * Delta * HammingWeight (horizontalComponent z') ≤
        ell * (4 * r)
  · have hStrong :=
      ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
        baseSample twistSample hLTC z' hz' hNormalized hSmall
    calc
      ell * (4 * r) ≤
          ell * (5 * HammingWeight (horizontalComponent z')) :=
        Nat.mul_le_mul_left ell hBaseHorizontal
      _ = 5 * (ell * HammingWeight (horizontalComponent z')) := by
        ac_rfl
      _ ≤ 5 * (500 * HammingWeight (verticalComponent z')) :=
        Nat.mul_le_mul_left 5 hStrong
      _ = 2500 * HammingWeight (verticalComponent z') := by ring
      _ ≤ 2500 * HammingWeight z' :=
        Nat.mul_le_mul_left 2500 hVerticalTotal
      _ ≤ 2500 * HammingWeight z :=
        Nat.mul_le_mul_left 2500 hWeight
      _ ≤ 5000 * Delta * HammingWeight z := by
        have hCoefficient : 2500 ≤ 5000 * Delta := by nlinarith
        exact Nat.mul_le_mul_right (HammingWeight z) hCoefficient
  · have hLarge :
        ell * (4 * r) <
          5000 * Delta * HammingWeight (horizontalComponent z') :=
      Nat.lt_of_not_ge hSmall
    calc
      ell * (4 * r) ≤
          5000 * Delta * HammingWeight (horizontalComponent z') :=
        Nat.le_of_lt hLarge
      _ ≤ 5000 * Delta * HammingWeight z' :=
        Nat.mul_le_mul_left (5000 * Delta) hHorizontalTotal
      _ ≤ 5000 * Delta * HammingWeight z :=
        Nat.mul_le_mul_left (5000 * Delta) hWeight

/-! ## Global translation after the clusters have merged -/

/-- Simultaneously translate both degree-one fiber-coordinate sectors. -/
def bundleFiberTranslationEquiv
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n) :
    QubitIndex baseZero baseOne (ZMod n) (ZMod n) ≃
      QubitIndex baseZero baseOne (ZMod n) (ZMod n) :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl baseOne) (Equiv.addRight t))
    (Equiv.prodCongr (Equiv.refl baseZero) (Equiv.addRight t))

/-- Translate a bundle one-chain by `t` in both fiber-coordinate sectors. -/
def translateBundleWord
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)) :=
  reindexWord (bundleFiberTranslationEquiv n t) z

@[simp]
theorem translateBundleWord_apply_inl
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)))
    (b : baseOne) (i : ZMod n) :
    translateBundleWord n t z (Sum.inl (b, i)) =
      z (Sum.inl (b, i - t)) := by
  simp [translateBundleWord, reindexWord, bundleFiberTranslationEquiv,
    sub_eq_add_neg]

@[simp]
theorem translateBundleWord_apply_inr
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)))
    (a : baseZero) (j : ZMod n) :
    translateBundleWord n t z (Sum.inr (a, j)) =
      z (Sum.inr (a, j - t)) := by
  simp [translateBundleWord, reindexWord, bundleFiberTranslationEquiv,
    sub_eq_add_neg]

/-- Global fiber translation preserves total Hamming weight exactly. -/
theorem hammingWeight_translateBundleWord
    {baseZero baseOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n] (t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    HammingWeight (translateBundleWord n t z) = HammingWeight z := by
  exact hammingWeight_reindexWord
    (bundleFiberTranslationEquiv n t) z

/--
Sliding the complete horizontal sector of a bundle cycle once is exactly
global translation by one fiber cell.
-/
theorem oneStepSlide_horizontalComponent_eq_translateBundleWord
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
        ).middleCycleCode.carrier) :
    oneStepSlide baseSample twistSample z (horizontalComponent z) =
      translateBundleWord (ell * ell) 1 z := by
  let D := RandomTwist.fiberBundleData baseSample twistSample
  have hzZero : boundary1 D z = 0 :=
    ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  funext q
  rcases q with ⟨b, i⟩ | ⟨a, j⟩
  · rw [translateBundleWord_apply_inl]
    change horizontalFiber
      (oneStepSlide baseSample twistSample z
        (horizontalComponent z)) b i =
      z (Sum.inl (b, i - 1))
    rw [oneStepSlide, show horizontalFiber
        (z +
          boundary2 D (oneStepSlideTwoChain (horizontalComponent z))) b i =
        horizontalFiber z b i +
          horizontalFiber
            (boundary2 D
              (oneStepSlideTwoChain (horizontalComponent z))) b i by rfl]
    rw [horizontalFiber_boundary2_oneStepSlideTwoChain]
    change z (Sum.inl (b, i)) +
      (z (Sum.inl (b, i)) + z (Sum.inl (b, i - 1))) =
        z (Sum.inl (b, i - 1))
    let w := z (Sum.inl (b, i))
    have hww : w + w = 0 := by
      calc
        w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel w
    calc
      z (Sum.inl (b, i)) +
          (z (Sum.inl (b, i)) + z (Sum.inl (b, i - 1))) =
        (w + w) + z (Sum.inl (b, i - 1)) := by
          dsimp [w]
          abel
      _ = z (Sum.inl (b, i - 1)) := by rw [hww, zero_add]
  · rw [translateBundleWord_apply_inr]
    change verticalFiber
      (oneStepSlide baseSample twistSample z
        (horizontalComponent z)) a j =
      z (Sum.inr (a, j - 1))
    have hj := congrFun hzZero (a, j)
    rw [boundary1_apply_eq_horizontal_add_vertical] at hj
    have hVertical :
        (∑ k : ZMod (ell * ell),
          D.fiberBoundary j k * z (Sum.inr (a, k))) =
        z (Sum.inr (a, j)) + z (Sum.inr (a, j - 1)) := by
      change cycleFiberChainBoundary (ell * ell)
        (verticalFiber z a) j =
          verticalFiber z a j + verticalFiber z a (j - 1)
      have hEll : 2 ≤ ell := by
        have hne : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
        omega
      exact cycleFiberChainBoundary_apply
        (ell * ell) (by nlinarith) _ j
    rw [oneStepSlide, show verticalFiber
        (z +
          boundary2 D (oneStepSlideTwoChain (horizontalComponent z))) a j =
        verticalFiber z a j +
          verticalFiber
            (boundary2 D
              (oneStepSlideTwoChain (horizontalComponent z))) a j by rfl]
    rw [verticalFiber_boundary2_oneStepSlideTwoChain]
    have hHorizontal :
        (∑ b : Fin (4 * r),
          RandomBase.boundary baseSample a b *
            horizontalComponent z
              (b, (((D.connection b a).onOne.symm) j))) =
          z (Sum.inr (a, j)) + z (Sum.inr (a, j - 1)) := by
      rw [← hVertical]
      have hj' := hj
      change
        (∑ b : Fin (4 * r),
          D.baseBoundary a b *
            z (Sum.inl
              (b, (((D.connection b a).onZero.symm) j)))) +
        (∑ k : ZMod (ell * ell),
          D.fiberBoundary j k * z (Sum.inr (a, k))) = 0 at hj'
      have hneg :
          (∑ b : Fin (4 * r),
            D.baseBoundary a b *
              z (Sum.inl
                (b, (((D.connection b a).onZero.symm) j)))) =
            -(∑ k : ZMod (ell * ell),
              D.fiberBoundary j k * z (Sum.inr (a, k))) :=
        eq_neg_of_add_eq_zero_left hj'
      rw [show
        (∑ b : Fin (4 * r),
          RandomBase.boundary baseSample a b *
            horizontalComponent z
              (b, (((D.connection b a).onOne.symm) j))) =
        (∑ b : Fin (4 * r),
          D.baseBoundary a b *
            z (Sum.inl
              (b, (((D.connection b a).onZero.symm) j)))) by rfl]
      rw [hneg, ZMod.neg_eq_self_mod_two]
    rw [hHorizontal]
    let w := z (Sum.inr (a, j))
    have hww : w + w = 0 := by
      calc
        w + w = w + (-w) := by rw [ZMod.neg_eq_self_mod_two]
        _ = 0 := add_neg_cancel w
    change w + (w + z (Sum.inr (a, j - 1))) =
      z (Sum.inr (a, j - 1))
    calc
      w + (w + z (Sum.inr (a, j - 1))) =
          (w + w) + z (Sum.inr (a, j - 1)) := by abel
      _ = z (Sum.inr (a, j - 1)) := by rw [hww, zero_add]

/-- A global one-step slide of a cycle preserves its weight exactly. -/
theorem hammingWeight_oneStepSlide_horizontalComponent
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
        ).middleCycleCode.carrier) :
    HammingWeight
        (oneStepSlide baseSample twistSample z
          (horizontalComponent z)) =
      HammingWeight z := by
  rw [oneStepSlide_horizontalComponent_eq_translateBundleWord
    baseSample twistSample z hz]
  exact hammingWeight_translateBundleWord (ell * ell) 1 z

/-! ## Finite global translation of a connected horizontal support -/

/-- Fiber translations compose by adding their translation parameters. -/
theorem translateBundleWord_add
    {baseZero baseOne : Type u}
    (n : Nat) [NeZero n] (s t : ZMod n)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n))) :
    translateBundleWord n s (translateBundleWord n t z) =
      translateBundleWord n (s + t) z := by
  funext q
  rcases q with ⟨b, i⟩ | ⟨a, j⟩
  · simp only [translateBundleWord_apply_inl]
    congr 2
    abel
  · simp only [translateBundleWord_apply_inr]
    congr 2
    abel

/--
Iterate the canonical global one-step slide.  At every stage the chosen
horizontal subchain is the entire current horizontal sector.
-/
noncomputable def globalSlideIterate
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Nat → Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))
  | 0 => z
  | k + 1 =>
      oneStepSlide baseSample twistSample
        (globalSlideIterate baseSample twistSample z k)
        (horizontalComponent
          (globalSlideIterate baseSample twistSample z k))

/-- Every finite global-slide iterate remains a bundle cycle. -/
theorem globalSlideIterate_mem_middleCycleCode
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
        ).middleCycleCode.carrier) :
    ∀ k, globalSlideIterate baseSample twistSample z k ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier := by
  intro k
  induction k with
  | zero => simpa [globalSlideIterate] using hz
  | succ k ih =>
      rw [globalSlideIterate]
      exact oneStepSlide_mem_middleCycleCode
        baseSample twistSample
        (globalSlideIterate baseSample twistSample z k)
        (horizontalComponent
          (globalSlideIterate baseSample twistSample z k)) ih

/-- A finite global-slide iterate is translation by the corresponding natural number. -/
theorem globalSlideIterate_eq_translateBundleWord
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
        ).middleCycleCode.carrier) :
    ∀ k,
      globalSlideIterate baseSample twistSample z k =
        translateBundleWord (ell * ell)
          (k : ZMod (ell * ell)) z := by
  intro k
  induction k with
  | zero =>
      funext q
      rcases q with ⟨b, i⟩ | ⟨a, j⟩ <;>
        simp [globalSlideIterate]
  | succ k ih =>
      rw [globalSlideIterate]
      rw [oneStepSlide_horizontalComponent_eq_translateBundleWord
        baseSample twistSample
        (globalSlideIterate baseSample twistSample z k)
        (globalSlideIterate_mem_middleCycleCode
          baseSample twistSample z hz k)]
      rw [ih, translateBundleWord_add]
      have hcast :
          (1 : ZMod (ell * ell)) + (k : ZMod (ell * ell)) =
            ((k + 1 : Nat) : ZMod (ell * ell)) := by
        rw [Nat.cast_add, Nat.cast_one]
        abel
      rw [hcast]

/-- Finite global sliding preserves total Hamming weight exactly. -/
theorem hammingWeight_globalSlideIterate
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
        ).middleCycleCode.carrier)
    (k : Nat) :
    HammingWeight (globalSlideIterate baseSample twistSample z k) =
      HammingWeight z := by
  rw [globalSlideIterate_eq_translateBundleWord
    baseSample twistSample z hz k]
  exact hammingWeight_translateBundleWord
    (ell * ell) (k : ZMod (ell * ell)) z

/--
Every global-slide iterate differs from the original cycle by a degree-two
boundary, so it is genuinely homologous to the original representative.
-/
theorem globalSlideIterate_add_mem_middleBoundaryCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    ∀ k,
      globalSlideIterate baseSample twistSample z k + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier := by
  intro k
  induction k with
  | zero =>
      have hzz : z + z = 0 := by
        funext q
        calc
          z q + z q = z q + (-z q) := by
            rw [ZMod.neg_eq_self_mod_two]
          _ = 0 := add_neg_cancel _
      rw [globalSlideIterate, hzz]
      exact Submodule.zero_mem _
  | succ k ih =>
      let D := RandomTwist.fiberBundleData baseSample twistSample
      let current := globalSlideIterate baseSample twistSample z k
      let c := oneStepSlideTwoChain (horizontalComponent current)
      have hc : boundary2 D c ∈
          (chainComplex D).middleBoundaryCode.carrier :=
        ((chainComplex D).mem_middleBoundaryCode_iff
          (boundary2 D c)).2 ⟨c, rfl⟩
      have heq :
          globalSlideIterate baseSample twistSample z (k + 1) + z =
            (current + z) + boundary2 D c := by
        rw [globalSlideIterate]
        change (current + boundary2 D c) + z =
          (current + z) + boundary2 D c
        funext q
        change (current q + boundary2 D c q) + z q =
          (current q + z q) + boundary2 D c q
        abel
      rw [heq]
      exact Submodule.add_mem _ ih hc

/--
If every supported horizontal cell belongs to one support-induced cluster,
a finite global slide places the entire horizontal support at residue zero
without changing weight.
-/
theorem exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected
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
        ).middleCycleCode.carrier)
    (root : Fin (4 * r) × ZMod (ell * ell))
    (hConnected :
      ∀ x, z (Sum.inl x) ≠ 0 →
        InSameSupportedHorizontalCluster
          baseSample twistSample z root x) :
    ∃ k,
      HammingWeight
          (globalSlideIterate baseSample twistSample z k) =
        HammingWeight z ∧
      globalSlideIterate baseSample twistSample z k + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized
        (globalSlideIterate baseSample twistSample z k) := by
  let k : Nat := (-root.2).val
  refine ⟨k, hammingWeight_globalSlideIterate
    baseSample twistSample z hz k,
    globalSlideIterate_add_mem_middleBoundaryCode
      baseSample twistSample z k, ?_⟩
  intro b i hi
  have hk : (k : ZMod (ell * ell)) = -root.2 := by
    exact ZMod.natCast_zmod_val (-root.2)
  rw [globalSlideIterate_eq_translateBundleWord
    baseSample twistSample z hz k,
    translateBundleWord_apply_inl] at hi
  let x : Fin (4 * r) × ZMod (ell * ell) :=
    (b, i - (k : ZMod (ell * ell)))
  have hxSupport : z (Sum.inl x) ≠ 0 := by
    simpa [x] using hi
  have hResidue :=
    fiberResidue_eq_of_inSameSupportedHorizontalCluster
      baseSample twistSample z
      (hConnected x hxSupport)
  change fiberResidue ell root.2 =
    fiberResidue ell (i - (k : ZMod (ell * ell))) at hResidue
  rw [hk, sub_neg_eq_add, map_add] at hResidue
  apply add_right_cancel (b := fiberResidue ell root.2)
  simpa using hResidue.symm

/--
The one-cluster terminal case of HHO20 Lemma `sliding`: a cycle with nonzero
base projection and cluster count one has a homologous, equal-weight
representative whose horizontal support is at residue zero.
-/
theorem exists_homologous_isHorizontallyResidueNormalized_of_clusterCount_eq_one
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
        ).middleCycleCode.carrier)
    (hProjection : homologyBaseProjection z ≠ 0)
    (hCount :
      horizontalClusterCount baseSample twistSample z = 1) :
    ∃ z',
      HammingWeight z' = HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized z' := by
  let root : SupportedHorizontalCell z :=
    Classical.choice
      (nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
        z hProjection)
  have hConnected :
      ∀ x, z (Sum.inl x) ≠ 0 →
        InSameSupportedHorizontalCluster
          baseSample twistSample z root.1 x := by
    intro x hx
    exact connected_of_horizontalClusterCount_eq_one
      baseSample twistSample z root hCount ⟨x, hx⟩
  rcases
      exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected
        baseSample twistSample z hz root.1 hConnected with
    ⟨k, hWeight, hHomologous, hNormalized⟩
  exact ⟨globalSlideIterate baseSample twistSample z k,
    hWeight, hHomologous, hNormalized⟩

end QEC.Coding.FiberBundle
