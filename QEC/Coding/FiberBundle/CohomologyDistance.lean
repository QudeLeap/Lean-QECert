import QEC.Coding.FiberBundle.Distance
import QEC.Coding.FiberBundle.RandomBase.Expansion
import QEC.Coding.FiberBundle.RandomTwist

/-!
# Representative support for the HHO20 cohomology-distance argument

This module formalizes the horizontal/vertical decomposition and the shadow
weights from HHO20, Section 3.2 (`def:shadow` and `cohomweight`).  The total
degree-one coordinates are a disjoint sum, so their Hamming weight splits
exactly into the two sectors and then into fiberwise weights.
-/

namespace QEC.Coding.FiberBundle

universe u

/-- Restrict a bundle one-chain to its horizontal coordinates. -/
def horizontalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) (baseOne × fiberZero) :=
  fun bi => x (Sum.inl bi)

@[simp]
theorem horizontalComponent_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x y : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    horizontalComponent (x + y) =
      horizontalComponent x + horizontalComponent y := by
  rfl

/-- Restrict a bundle one-chain to its vertical coordinates. -/
def verticalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) (baseZero × fiberOne) :=
  fun aj => x (Sum.inr aj)

/-- Lift a base one-cochain to the all-one horizontal fiber word. -/
def horizontalBaseLift
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) baseOne) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)
  | Sum.inl (b, _i) => x b
  | Sum.inr _ => 0

@[simp]
theorem horizontalBaseLift_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x y : Word (ZMod 2) baseOne) :
    horizontalBaseLift
        (baseZero := baseZero) (fiberZero := fiberZero)
        (fiberOne := fiberOne) (x + y) =
      horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x +
        horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) y := by
  funext q
  rcases q with bi | aj
  · rfl
  · rfl

@[simp]
theorem verticalComponent_horizontalBaseLift_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) baseOne)
    (y : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    verticalComponent
        (horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x + y) =
      verticalComponent y := by
  funext aj
  simp [verticalComponent, horizontalBaseLift]

/-- The horizontal fiber word over a selected base one-cell. -/
def horizontalFiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) : Word (ZMod 2) fiberZero :=
  fun i => x (Sum.inl (b, i))

@[simp]
theorem horizontalFiber_horizontalBaseLift
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) baseOne) (b : baseOne) :
    horizontalFiber
      (horizontalBaseLift
        (baseZero := baseZero) (fiberZero := fiberZero)
        (fiberOne := fiberOne) x) b =
      fun _i => x b := by
  rfl

/-- The vertical fiber word over a selected base zero-cell. -/
def verticalFiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) : Word (ZMod 2) fiberOne :=
  fun j => x (Sum.inr (a, j))

/-- The fiber word of a total-degree-zero bundle word over one base zero-cell. -/
def c0Fiber
    {baseZero fiberZero : Type u}
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) : Word (ZMod 2) fiberZero :=
  fun i => u (a, i)

/-- Base zero-cells supporting a nonzero total-degree-zero fiber word. -/
noncomputable def c0Shadow
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Finset baseZero :=
  Finset.univ.filter fun a => c0Fiber u a ≠ 0

/-- Outside its zero-cell shadow, a total-degree-zero fiber word vanishes. -/
theorem c0Fiber_eq_zero_of_not_mem_c0Shadow
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a : baseZero} (ha : a ∉ c0Shadow u) :
    c0Fiber u a = 0 := by
  by_contra hne
  exact ha (by simp [c0Shadow, hne])

/-- An empty zero-cell shadow means that the entire degree-zero word vanishes. -/
theorem eq_zero_of_c0Shadow_eq_empty
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (hShadow : c0Shadow u = ∅) :
    u = 0 := by
  funext ai
  rcases ai with ⟨a, i⟩
  have ha : a ∉ c0Shadow u := by
    rw [hShadow]
    simp
  exact congrFun (c0Fiber_eq_zero_of_not_mem_c0Shadow u ha) i

/-- Base one-cells supporting a nonzero horizontal fiber word. -/
noncomputable def horizontalShadow
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Finset baseOne :=
  Finset.univ.filter fun b => horizontalFiber x b ≠ 0

/-- Base zero-cells supporting a nonzero vertical fiber word. -/
noncomputable def verticalShadow
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Finset baseZero :=
  Finset.univ.filter fun a => verticalFiber x a ≠ 0

/-- Hamming weight as a sum of coordinatewise nonzero indicators. -/
theorem hammingWeight_eq_sum_indicator
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    HammingWeight x = ∑ i : ι, if x i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]

/--
A nonzero binary word with zero total parity has at least two nonzero
coordinates.
-/
theorem two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
    {ι : Type u} [Fintype ι]
    (x : Word (ZMod 2) ι)
    (hsum : (∑ i : ι, x i) = 0)
    (hx : x ≠ 0) :
    2 ≤ HammingWeight x := by
  by_contra hlt
  have hweightPos : 0 < HammingWeight x := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hx ((HammingWeight_eq_zero_iff x).mp hzero)
  have hweightOne : HammingWeight x = 1 := by omega
  have hsupportCard : (hammingSupport x).card = 1 := by
    simpa [HammingWeight] using hweightOne
  rcases Finset.card_eq_one.mp hsupportCard with ⟨i, hiSupport⟩
  have hiMem : i ∈ hammingSupport x := by
    rw [hiSupport]
    simp
  have hiNe : x i ≠ 0 := by
    simpa [hammingSupport] using hiMem
  have hiOne : x i = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero (x i) hiNe
  have hsumSingle : (∑ j : ι, x j) = x i := by
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      by_contra hjNe
      have hjMem : j ∈ hammingSupport x := by
        simp [hammingSupport, hjNe]
      rw [hiSupport] at hjMem
      exact hj (by simpa using hjMem)
    · simp
  rw [hsumSingle, hiOne] at hsum
  exact one_ne_zero hsum

/-- A cycle of length at least two has distinct consecutive vertices. -/
theorem zmod_ne_add_one
    (n : Nat) [NeZero n] (hn : 2 ≤ n) (j : ZMod n) :
    j ≠ j + 1 := by
  intro h
  have hzeroOne : (0 : ZMod n) = 1 := by
    simpa [add_comm] using congrArg (fun z => z - j) h
  have hone : (1 : ZMod n) ≠ 0 := by
    rw [ne_eq, ZMod.one_eq_zero_iff]
    omega
  exact hone hzeroOne.symm

/-- The cochain coboundary on the explicit length-`n` cycle fiber. -/
def cycleFiberCoboundary
    (n : Nat) [NeZero n]
    (f : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun j => ∑ i : ZMod n, f i * cycleBoundary n i j

/-- On a nondegenerate cycle, an edge coboundary is the sum of its endpoints. -/
theorem cycleFiberCoboundary_apply
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n)) (j : ZMod n) :
    cycleFiberCoboundary n f j = f j + f (j + 1) := by
  classical
  have hj : j ≠ j + 1 := zmod_ne_add_one n hn j
  have hfilter :
      (Finset.univ.filter fun i : ZMod n => i = j ∨ i = j + 1) =
        {j, j + 1} := by
    ext i
    simp [eq_comm]
  rw [cycleFiberCoboundary]
  simp_rw [cycleBoundary, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hfilter]
  simp [hj]

/-- Every cycle-fiber coboundary has zero total binary parity. -/
theorem sum_cycleFiberCoboundary_eq_zero
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n)) :
    (∑ j : ZMod n, cycleFiberCoboundary n f j) = 0 := by
  simp_rw [cycleFiberCoboundary_apply n hn]
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ j : ZMod n, f (j + 1)) = ∑ j : ZMod n, f j := by
    exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod n))
      (fun j => f (j + 1)) f (by intro j; rfl)
  rw [hshift]
  let s := ∑ j : ZMod n, f j
  change s + s = 0
  calc
    s + s = s + (-s) := by rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel s

/-- A nonzero cycle-fiber coboundary has Hamming weight at least two. -/
theorem two_le_hammingWeight_cycleFiberCoboundary
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : cycleFiberCoboundary n f ≠ 0) :
    2 ≤ HammingWeight (cycleFiberCoboundary n f) :=
  two_le_hammingWeight_of_sum_eq_zero_of_ne_zero
    (cycleFiberCoboundary n f)
    (sum_cycleFiberCoboundary_eq_zero n hn f)
    hf

/-- A cycle-fiber word with zero coboundary is constant. -/
theorem cycleFiberCoboundary_eq_zero_implies_constant
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : cycleFiberCoboundary n f = 0) :
    ∀ j, f j = f 0 := by
  have hstep (j : ZMod n) : f (j + 1) = f j := by
    have hj := congrFun hf j
    rw [cycleFiberCoboundary_apply n hn] at hj
    simp only [Pi.zero_apply] at hj
    have hneg : f (j + 1) = -f j :=
      eq_neg_of_add_eq_zero_right hj
    simpa [ZMod.neg_eq_self_mod_two] using hneg
  have hcast (k : Nat) : f (k : ZMod n) = f 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.cast_succ]
        exact (hstep (k : ZMod n)).trans ih
  intro j
  rw [← j.natCast_zmod_val]
  exact hcast j.val

/--
A nonzero cycle-fiber word normalized to at most half the cycle cannot have
zero coboundary.
-/
theorem cycleFiberCoboundary_ne_zero_of_normalized
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : f ≠ 0)
    (hhalf : 2 * HammingWeight f ≤ Fintype.card (ZMod n)) :
    cycleFiberCoboundary n f ≠ 0 := by
  intro hcoboundary
  have hconstant :=
    cycleFiberCoboundary_eq_zero_implies_constant n hn f hcoboundary
  have hfZeroNe : f 0 ≠ 0 := by
    intro hf0
    apply hf
    funext j
    rw [hconstant j, hf0]
    rfl
  have hfZeroOne : f 0 = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero (f 0) hfZeroNe
  have hfOne : f = fun _ => 1 := by
    funext j
    rw [hconstant j, hfZeroOne]
  have hweight : HammingWeight f = Fintype.card (ZMod n) := by
    rw [hfOne]
    simp [HammingWeight, hammingSupport]
  rw [hweight, ZMod.card] at hhalf
  omega

/-- Every nonzero normalized cycle-fiber word has coboundary weight at least two. -/
theorem two_le_hammingWeight_cycleFiberCoboundary_of_normalized
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (f : Word (ZMod 2) (ZMod n))
    (hf : f ≠ 0)
    (hhalf : 2 * HammingWeight f ≤ Fintype.card (ZMod n)) :
    2 ≤ HammingWeight (cycleFiberCoboundary n f) :=
  two_le_hammingWeight_cycleFiberCoboundary n hn f
    (cycleFiberCoboundary_ne_zero_of_normalized n hn f hf hhalf)

/-- Reindex a word along a coordinate equivalence. -/
def reindexWord
    {ι κ : Type u} (e : ι ≃ κ) (x : Word (ZMod 2) ι) :
    Word (ZMod 2) κ :=
  fun k => x (e.symm k)

/-- Coordinate reindexing preserves Hamming weight exactly. -/
theorem hammingWeight_reindexWord
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : Word (ZMod 2) ι) :
    HammingWeight (reindexWord e x) = HammingWeight x := by
  rw [hammingWeight_eq_sum_indicator, hammingWeight_eq_sum_indicator]
  exact (Fintype.sum_equiv e
    (fun i => if x i ≠ 0 then 1 else 0)
    (fun k => if reindexWord e x k ≠ 0 then 1 else 0)
    (by intro i; simp [reindexWord])).symm

/-- Toggle every binary coordinate by the all-one word. -/
def binaryComplement
    {ι : Type u} (x : Word (ZMod 2) ι) : Word (ZMod 2) ι :=
  fun i => 1 + x i

/-- A binary word and its complement partition the coordinate set. -/
theorem hammingWeight_add_hammingWeight_binaryComplement
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    HammingWeight x + HammingWeight (binaryComplement x) =
      Fintype.card ι := by
  rw [hammingWeight_eq_sum_indicator, hammingWeight_eq_sum_indicator,
    Fintype.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i = 0
  · simp [binaryComplement, hi]
  · have hiOne : x i = 1 :=
      RandomBase.zmod2_eq_one_of_ne_zero (x i) hi
    simp [binaryComplement, hiOne]
    exact ZMod.natCast_self 2

/--
If a binary fiber word occupies at most half the coordinates (in doubled
integer form), its complement occupies at least half.
-/
theorem card_le_twice_hammingWeight_binaryComplement
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι)
    (hx : 2 * HammingWeight x ≤ Fintype.card ι) :
    Fintype.card ι ≤ 2 * HammingWeight (binaryComplement x) := by
  have hpartition := hammingWeight_add_hammingWeight_binaryComplement x
  omega

/--
Choose the lighter representative of a binary word modulo the all-one word.
Ties are resolved by keeping the original word.
-/
def normalizeBinaryWord
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    Word (ZMod 2) ι :=
  if 2 * HammingWeight x ≤ Fintype.card ι then x else binaryComplement x

/-- The normalized binary representative occupies at most half the coordinates. -/
theorem twice_hammingWeight_normalizeBinaryWord_le_card
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    2 * HammingWeight (normalizeBinaryWord x) ≤ Fintype.card ι := by
  by_cases hx : 2 * HammingWeight x ≤ Fintype.card ι
  · rw [normalizeBinaryWord, if_pos hx]
    exact hx
  · rw [normalizeBinaryWord, if_neg hx]
    have hpartition := hammingWeight_add_hammingWeight_binaryComplement x
    omega

/-- Normalization either keeps the word or toggles it by the all-one word. -/
theorem normalizeBinaryWord_eq_self_or_complement
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι) :
    normalizeBinaryWord x = x ∨ normalizeBinaryWord x = binaryComplement x := by
  unfold normalizeBinaryWord
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Normalize every fiber word of a total-degree-zero bundle word independently. -/
def normalizeC0Fibers
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => normalizeBinaryWord (fun i => u (ai.1, i)) ai.2

/-- The binary choice recording whether normalization toggles one fiber. -/
def normalizationToggle
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) : ZMod 2 :=
  if 2 * HammingWeight (fun i => u (a, i)) ≤ Fintype.card fiberZero
  then 0
  else 1

/-- The total-degree-zero word which is constant on every normalized fiber. -/
def normalizationToggleWord
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => normalizationToggle u ai.1

/-- The ordinary base coboundary of a base zero-cochain. -/
def baseCoboundary
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    Word (ZMod 2) (Fin (4 * r)) :=
  fun b =>
    ∑ a : Fin (3 * r), t a * RandomBase.boundary baseSample a b

/-- A lifted base cochain represents a nontrivial base cohomology class. -/
def IsNontrivialBaseCohomology
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (x : Word (ZMod 2) (Fin (4 * r))) : Prop :=
  ∀ t : Word (ZMod 2) (Fin (3 * r)), x ≠ baseCoboundary baseSample t

/-- The base one-cochain induced by the constant-fiber normalization toggle. -/
def normalizationBaseShift
    {r ell : Nat}
    [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    Word (ZMod 2) (Fin (4 * r)) :=
  baseCoboundary baseSample (normalizationToggle u)

/-- Adding any base coboundary to a nontrivial base class cannot produce zero. -/
theorem IsNontrivialBaseCohomology.add_baseCoboundary_ne_zero
    {r : Nat}
    (baseSample : RandomBase.Sample r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    x + baseCoboundary baseSample t ≠ 0 := by
  intro hzero
  apply hx t
  funext b
  have hb :
      x b + baseCoboundary baseSample t b = 0 :=
    congrFun hzero b
  calc
    x b = -(baseCoboundary baseSample t b) :=
      eq_neg_of_add_eq_zero_left hb
    _ = baseCoboundary baseSample t b :=
      ZMod.neg_eq_self_mod_two _

/-- The single-fiber correction which cancels the fiber over `a`. -/
def eraseC0FiberCorrection
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => if ai.1 = a then -u ai else 0

/-- Erase one selected total-degree-zero fiber word. -/
def eraseC0Fiber
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  u + eraseC0FiberCorrection u a

@[simp]
theorem c0Fiber_eraseC0Fiber_same
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    c0Fiber (eraseC0Fiber u a) a = 0 := by
  funext i
  simp only [c0Fiber, eraseC0Fiber, Pi.add_apply, eraseC0FiberCorrection,
    Pi.zero_apply]
  exact add_neg_cancel _

theorem c0Fiber_eraseC0Fiber_of_ne
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a a' : baseZero} (ha : a' ≠ a) :
    c0Fiber (eraseC0Fiber u a) a' = c0Fiber u a' := by
  funext i
  simp [c0Fiber, eraseC0Fiber, eraseC0FiberCorrection, ha]

/-- Erasing one fiber deletes exactly that point from the zero-cell shadow. -/
theorem c0Shadow_eraseC0Fiber
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [DecidableEq baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    c0Shadow (eraseC0Fiber u a) = (c0Shadow u).erase a := by
  ext a'
  by_cases ha : a' = a
  · subst a'
    simp [c0Shadow]
  · simp only [c0Shadow, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [c0Fiber_eraseC0Fiber_of_ne (a := a) u ha]
    constructor
    · intro h
      exact ⟨ha, h⟩
    · intro h
      exact h.2

/-- Erasing a supported fiber strictly decreases the shadow cardinality. -/
theorem card_c0Shadow_eraseC0Fiber_lt
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [DecidableEq baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a : baseZero} (ha : a ∈ c0Shadow u) :
    (c0Shadow (eraseC0Fiber u a)).card < (c0Shadow u).card := by
  rw [c0Shadow_eraseC0Fiber, Finset.card_erase_of_mem ha]
  have hpos : 0 < (c0Shadow u).card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- Fiberwise normalization is addition of its explicit constant-fiber toggle word. -/
theorem normalizeC0Fibers_eq_add_normalizationToggleWord
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    normalizeC0Fibers u = u + normalizationToggleWord u := by
  funext ai
  rcases ai with ⟨a, i⟩
  change
    normalizeBinaryWord (fun j => u (a, j)) i =
      u (a, i) + normalizationToggle u a
  by_cases hlight :
      2 * HammingWeight (fun j => u (a, j)) ≤ Fintype.card fiberZero
  · rw [normalizeBinaryWord, normalizationToggle, if_pos hlight, if_pos hlight]
    simp
  · rw [normalizeBinaryWord, normalizationToggle, if_neg hlight, if_neg hlight]
    change 1 + u (a, i) = u (a, i) + 1
    exact add_comm 1 (u (a, i))

/-- Each independently normalized zero-cell fiber has weight at most half. -/
theorem twice_hammingWeight_normalizeC0Fibers_le_card
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    2 * HammingWeight (fun i => normalizeC0Fibers u (a, i)) ≤
      Fintype.card fiberZero := by
  simpa only [normalizeC0Fibers] using
    twice_hammingWeight_normalizeBinaryWord_le_card
      (fun i => u (a, i))

/--
A total-degree-zero bundle word is fiberwise normalized when every fiber
occupies at most half of the fiber coordinates.  This is the invariant used
throughout the repeated shadow-erasure argument.
-/
def C0FibersNormalized
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) : Prop :=
  ∀ a, 2 * HammingWeight (c0Fiber u a) ≤ Fintype.card fiberZero

/-- Explicit fiberwise normalization establishes the normalization invariant. -/
theorem c0FibersNormalized_normalizeC0Fibers
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    C0FibersNormalized (normalizeC0Fibers u) := by
  intro a
  exact twice_hammingWeight_normalizeC0Fibers_le_card u a

/-- Erasing a fiber preserves fiberwise normalization. -/
theorem C0FibersNormalized.eraseC0Fiber
    {baseZero fiberZero : Type u}
    [DecidableEq baseZero] [Fintype fiberZero]
    {u : Word (ZMod 2) (C0Index baseZero fiberZero)}
    (hu : C0FibersNormalized u) (a : baseZero) :
    C0FibersNormalized (eraseC0Fiber u a) := by
  intro a'
  by_cases ha : a' = a
  · subst a'
    rw [c0Fiber_eraseC0Fiber_same, HammingWeight_zero]
    exact Nat.zero_le _
  · rw [c0Fiber_eraseC0Fiber_of_ne u ha]
    exact hu a'

/-- The bundle coboundary of a total-degree-zero word. -/
noncomputable def bundleCoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  wordLinearMapTranspose (boundary1 D) u

/-- Coordinate formula for the transpose of the first bundle boundary. -/
theorem bundleCoboundary_apply
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (q : QubitIndex baseZero baseOne fiberZero fiberOne) :
    bundleCoboundary D u q =
      ∑ ai : C0Index baseZero fiberZero,
        u ai * boundary1Matrix D ai q := by
  classical
  unfold bundleCoboundary wordLinearMapTranspose
  dsimp
  apply Finset.sum_congr rfl
  intro ai _
  congr 1
  simp [boundary1, Matrix.toLin'_apply, Matrix.mulVec]

/-- Bundle coboundaries respect the explicit normalization decomposition. -/
theorem bundleCoboundary_normalizeC0Fibers
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    bundleCoboundary D (normalizeC0Fibers u) =
      bundleCoboundary D u +
        bundleCoboundary D (normalizationToggleWord u) := by
  rw [normalizeC0Fibers_eq_add_normalizationToggleWord]
  exact map_add (wordLinearMapTranspose (boundary1 D)) u
    (normalizationToggleWord u)

/-- Erasing one zero-cell fiber changes its bundle coboundary by the explicit correction. -/
theorem bundleCoboundary_eraseC0Fiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    bundleCoboundary D (eraseC0Fiber u a) =
      bundleCoboundary D u +
        bundleCoboundary D (eraseC0FiberCorrection u a) := by
  rw [eraseC0Fiber]
  exact map_add (wordLinearMapTranspose (boundary1 D)) u
    (eraseC0FiberCorrection u a)

/--
Dropping one shadow fiber produces a cohomologous representative by adding
one explicit bundle coboundary.
-/
theorem horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (x : Word (ZMod 2) baseOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x +
        bundleCoboundary D (eraseC0Fiber u a) =
      (horizontalBaseLift
            (baseZero := baseZero) (fiberZero := fiberZero)
            (fiberOne := fiberOne) x +
          bundleCoboundary D u) +
        bundleCoboundary D (eraseC0FiberCorrection u a) := by
  rw [bundleCoboundary_eraseC0Fiber]
  exact (add_assoc
    (horizontalBaseLift
      (baseZero := baseZero) (fiberZero := fiberZero)
      (fiberOne := fiberOne) x)
    (bundleCoboundary D u)
    (bundleCoboundary D (eraseC0FiberCorrection u a))).symm

/--
The horizontal fiber of a bundle coboundary is the sum of the incident base
zero-cell fiber words, each reindexed by its selected connection.
-/
theorem horizontalFiber_bundleCoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (b : baseOne) (j : fiberZero) :
    horizontalFiber (bundleCoboundary D u) b j =
      ∑ a : baseZero,
        u (a, (D.connection b a).onZero j) * D.baseBoundary a b := by
  classical
  rw [horizontalFiber, bundleCoboundary_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp [boundary1Matrix]

/--
The horizontal effect of erasing one zero-cell fiber is either zero or one
connection-reindexed copy of that fiber, according to the sampled incidence.
-/
theorem horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    horizontalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (eraseC0FiberCorrection u a)) b =
      if baseSample (a, b) then
        reindexWord
          ((RandomTwist.fiberBundleData baseSample twistSample).connection b a).onZero.symm
          (c0Fiber u a)
      else 0 := by
  funext j
  rw [horizontalFiber_bundleCoboundary]
  rw [Finset.sum_eq_single a]
  · by_cases hab : baseSample (a, b)
    · simp [RandomTwist.fiberBundleData, multipleRotationCycleData,
        cycleData, RandomBase.boundary, hab, eraseC0FiberCorrection,
        reindexWord, c0Fiber, ZMod.neg_eq_self_mod_two]
    · simp [RandomTwist.fiberBundleData, multipleRotationCycleData,
        cycleData, RandomBase.boundary, hab]
  · intro a' _ ha'
    simp [eraseC0FiberCorrection, ha']
  · simp

/-- Exact Hamming cost of the single-fiber erasure correction over one variable. -/
theorem hammingWeight_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a)) b) =
      if baseSample (a, b) then HammingWeight (c0Fiber u a) else 0 := by
  rw [horizontalFiber_bundleCoboundary_eraseC0FiberCorrection]
  by_cases hab : baseSample (a, b)
  · rw [if_pos hab, if_pos hab, hammingWeight_reindexWord]
  · rw [if_neg hab, if_neg hab, HammingWeight_zero]

/--
Over a counique base variable, the horizontal coboundary fiber is a single
connection-reindexed fiber word.  All other selected checks are absent, while
fiber words outside `S` vanish by the stated support condition.
-/
theorem exists_horizontalFiber_bundleCoboundary_eq_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample S)
    (hu : ∀ a, a ∉ S → c0Fiber u a = 0) :
    ∃ a ∈ S,
      baseSample (a, b) = true ∧
        horizontalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b =
          reindexWord
            ((RandomTwist.fiberBundleData baseSample twistSample).connection b a).onZero.symm
            (c0Fiber u a) := by
  rcases
      (RandomBase.mem_couniqueNeighbors_iff_exists_unique
        baseSample S b).mp hb with
    ⟨a, haS, haEdge, haUnique⟩
  refine ⟨a, haS, haEdge, ?_⟩
  funext j
  rw [horizontalFiber_bundleCoboundary]
  rw [Finset.sum_eq_single a]
  · simp [RandomTwist.fiberBundleData, multipleRotationCycleData,
      cycleData, RandomBase.boundary, haEdge, reindexWord, c0Fiber]
  · intro a' _ ha'ne
    by_cases ha'S : a' ∈ S
    · have ha'False : baseSample (a', b) = false := by
        apply Bool.eq_false_iff.mpr
        intro ha'True
        exact ha'ne (haUnique a' ha'S ha'True)
      simp [RandomTwist.fiberBundleData, multipleRotationCycleData,
        cycleData, RandomBase.boundary, ha'False]
    · have huZero := hu a' ha'S
      have huApply (i : ZMod (ell * ell)) : u (a', i) = 0 := by
        exact congrFun huZero i
      simp [huApply]
  · simp

/--
At a counique variable incident to the erased check and disjoint from the base
support, the old horizontal fiber has exactly the erased-fiber weight and the
new horizontal fiber vanishes.
-/
theorem hammingWeight_horizontalFiber_before_after_erase_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) (b : Fin (4 * r))
    (ha : a ∈ c0Shadow u)
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hab : baseSample (a, b) = true)
    (hxb : x b = 0) :
    HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b) =
        HammingWeight (c0Fiber u a) ∧
      HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a)) b) = 0 := by
  have huOutside :
      ∀ a', a' ∉ c0Shadow u → c0Fiber u a' = 0 := by
    intro a' ha'
    exact c0Fiber_eq_zero_of_not_mem_c0Shadow u ha'
  rcases
      exists_horizontalFiber_bundleCoboundary_eq_of_counique
        baseSample twistSample u (c0Shadow u) b hb huOutside with
    ⟨a', ha'Shadow, ha'Edge, hCoboundary⟩
  rcases
      (RandomBase.mem_couniqueNeighbors_iff_exists_unique
        baseSample (c0Shadow u) b).mp hb with
    ⟨aUnique, _haUniqueShadow, _haUniqueEdge, hUnique⟩
  have ha'eq : a' = a := by
    exact (hUnique a' ha'Shadow ha'Edge).trans
      (hUnique a ha hab).symm
  subst a'
  let f :=
    reindexWord
      ((RandomTwist.fiberBundleData baseSample twistSample).connection b a).onZero.symm
      (c0Fiber u a)
  have hOldFiber :
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b =
        f := by
    funext i
    change x b + horizontalFiber
      (bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u) b i = f i
    rw [hxb, zero_add, hCoboundary]
  have hCorrection :
      horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a)) b =
        f := by
    rw [horizontalFiber_bundleCoboundary_eraseC0FiberCorrection,
      if_pos hab]
  constructor
  · rw [hOldFiber, hammingWeight_reindexWord]
  · have hRepresentative :=
      horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
        (RandomTwist.fiberBundleData baseSample twistSample) x u a
    apply (HammingWeight_eq_zero_iff _).2
    rw [hRepresentative]
    funext i
    change
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b i +
        horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a)) b i = 0
    rw [hOldFiber, hCorrection]
    calc
      f i + f i = f i + (-f i) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel _

/--
At a counique base variable, any fiberwise-normalized zero-cell word produces
a horizontal coboundary fiber of weight at most half the fiber size.
-/
theorem twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u)) :
    2 * HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) b) ≤
      Fintype.card (ZMod (ell * ell)) := by
  have huOutside :
      ∀ a, a ∉ c0Shadow u → c0Fiber u a = 0 := by
    intro a ha
    exact c0Fiber_eq_zero_of_not_mem_c0Shadow u ha
  rcases
      exists_horizontalFiber_bundleCoboundary_eq_of_counique
        baseSample twistSample u (c0Shadow u) b hb huOutside with
    ⟨a, _ha, _haEdge, hfiber⟩
  rw [hfiber, hammingWeight_reindexWord]
  exact hu a

/--
A counique base variable sees at most half a fiber of the coboundary of the
explicitly normalized zero-cell word.
-/
theorem twice_hammingWeight_horizontalFiber_normalizedCoboundary_le_card_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u))) :
    2 * HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u)) b) ≤
      Fintype.card (ZMod (ell * ell)) := by
  exact
    twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
      baseSample twistSample (normalizeC0Fibers u)
      (c0FibersNormalized_normalizeC0Fibers u) b hb

/--
If a counique variable is in the lifted base support, adding the lift
complements the light coboundary fiber.  This generic form is stable under
any number of shadow erasures.
-/
theorem card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b) := by
  let f :=
    horizontalFiber
      (bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u) b
  have hfLight : 2 * HammingWeight f ≤ Fintype.card (ZMod (ell * ell)) := by
    exact
      twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
        baseSample twistSample u hu b hb
  have hxbOne : x b = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero (x b) hxb
  have hfiber :
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b =
        binaryComplement f := by
    funext i
    change x b + f i = 1 + f i
    rw [hxbOne]
  rw [hfiber]
  exact card_le_twice_hammingWeight_binaryComplement f hfLight

/--
If the counique variable also belongs to the support of the lifted base
one-cochain, adding that lift complements the normalized coboundary fiber.
Consequently the resulting horizontal fiber occupies at least half the fiber.
-/
theorem card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u)))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u)) b) := by
  let f :=
    horizontalFiber
      (bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (normalizeC0Fibers u)) b
  have hfLight : 2 * HammingWeight f ≤ Fintype.card (ZMod (ell * ell)) := by
    exact
      twice_hammingWeight_horizontalFiber_normalizedCoboundary_le_card_of_counique
        baseSample twistSample u b hb
  have hxbOne : x b = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero (x b) hxb
  have hfiber :
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u)) b =
        binaryComplement f := by
    funext i
    change x b + f i = 1 + f i
    rw [hxbOne]
  rw [hfiber]
  exact card_le_twice_hammingWeight_binaryComplement f hfLight

/--
The vertical fiber of a bundle coboundary is the ordinary fiber coboundary of
the word over that base zero-cell.
-/
theorem verticalFiber_bundleCoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) (j : fiberOne) :
    verticalFiber (bundleCoboundary D u) a j =
      ∑ i : fiberZero, u (a, i) * D.fiberBoundary i j := by
  classical
  rw [verticalFiber, bundleCoboundary_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [boundary1Matrix]
  · intro a' _ ha'
    simp [boundary1Matrix, ha']
  · simp

/-- For the construction's cycle fiber, the vertical formula is the cycle coboundary. -/
theorem verticalFiber_bundleCoboundary_fiberBundleData
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u) a =
      cycleFiberCoboundary (ell * ell) (c0Fiber u a) := by
  funext j
  rw [verticalFiber_bundleCoboundary]
  rfl

/--
The coboundary of the constant-fiber normalization toggle is exactly a
horizontal lift of its induced base coboundary; its vertical component
vanishes on the cycle fiber.
-/
theorem bundleCoboundary_normalizationToggleWord_eq_horizontalBaseLift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (normalizationToggleWord u) =
      horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (normalizationBaseShift baseSample u) := by
  funext q
  rcases q with ⟨bi⟩ | ⟨aj⟩
  · rcases bi with ⟨b, i⟩
    change
      horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizationToggleWord u)) b i =
        normalizationBaseShift baseSample u b
    rw [horizontalFiber_bundleCoboundary]
    simp only [normalizationToggleWord, RandomTwist.fiberBundleData,
      multipleRotationCycleData, cycleData, RandomBase.boundary,
      normalizationBaseShift, baseCoboundary]
  · rcases aj with ⟨a, j⟩
    change
      verticalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizationToggleWord u)) a j = 0
    rw [verticalFiber_bundleCoboundary_fiberBundleData]
    have hEll : 2 ≤ ell := by
      have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
      omega
    have hCycle : 2 ≤ ell * ell := by nlinarith
    rw [cycleFiberCoboundary_apply (ell * ell) hCycle]
    change normalizationToggle u a + normalizationToggle u a = 0
    calc
      normalizationToggle u a + normalizationToggle u a =
          normalizationToggle u a + (-normalizationToggle u a) := by
        rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel _

/--
Normalizing degree-zero fibers and shifting the lifted base cochain preserves
the full degree-one representative exactly.
-/
theorem horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell))
          (x + normalizationBaseShift baseSample u) +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (normalizeC0Fibers u) =
      horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u := by
  rw [horizontalBaseLift_add, bundleCoboundary_normalizeC0Fibers,
    bundleCoboundary_normalizationToggleWord_eq_horizontalBaseLift]
  funext q
  simp only [Pi.add_apply]
  let a : ZMod 2 :=
    horizontalBaseLift
      (baseZero := Fin (3 * r))
      (fiberZero := ZMod (ell * ell))
      (fiberOne := ZMod (ell * ell)) x q
  let b : ZMod 2 :=
    horizontalBaseLift
      (baseZero := Fin (3 * r))
      (fiberZero := ZMod (ell * ell))
      (fiberOne := ZMod (ell * ell))
      (normalizationBaseShift baseSample u) q
  let c : ZMod 2 :=
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample) u q
  change a + b + (c + b) = a + c
  have hb : b + b = 0 := by
    calc
      b + b = b + (-b) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel b
  calc
    a + b + (c + b) = a + c + (b + b) := by abel
    _ = a + c := by rw [hb, add_zero]

/--
The same base shift converts any correction on the normalized side to the
correction obtained by adding the constant-fiber toggle on the original side.
-/
theorem horizontalBaseLift_add_bundleCoboundary_baseShift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell))
          (x + normalizationBaseShift baseSample u) +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) v =
      horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (v + normalizationToggleWord u) := by
  have hCoboundaryAdd :
      bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (v + normalizationToggleWord u) =
        bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizationToggleWord u) := by
    exact map_add
      (wordLinearMapTranspose
        (boundary1 (RandomTwist.fiberBundleData baseSample twistSample)))
      v (normalizationToggleWord u)
  rw [horizontalBaseLift_add]
  rw [hCoboundaryAdd]
  rw [bundleCoboundary_normalizationToggleWord_eq_horizontalBaseLift]
  abel

/--
Every supported fiber of a fiberwise-normalized zero-cell word contributes at
least two vertical cells.
-/
theorem two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u) :
    2 ≤ HammingWeight
      (verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u) a) := by
  rw [verticalFiber_bundleCoboundary_fiberBundleData]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  have hCycle : 2 ≤ ell * ell := by nlinarith
  have hfNe : c0Fiber u a ≠ 0 := by
    simpa [c0Shadow] using ha
  exact
    two_le_hammingWeight_cycleFiberCoboundary_of_normalized
      (ell * ell) hCycle (c0Fiber u a) hfNe (hu a)

/--
Every base zero-cell in the normalized shadow contributes at least two
vertical cells.
-/
theorem two_le_hammingWeight_verticalFiber_normalizedCoboundary_of_mem_shadow
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow (normalizeC0Fibers u)) :
    2 ≤ HammingWeight
      (verticalFiber
        (bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample)
          (normalizeC0Fibers u)) a) := by
  exact
    two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
      baseSample twistSample (normalizeC0Fibers u)
      (c0FibersNormalized_normalizeC0Fibers u) a ha

/-- A constructed bundle coboundary belongs to the trivial cohomology sector. -/
theorem bundleCoboundary_mem_firstCoboundaryCheckCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    bundleCoboundary D u ∈
      (chainComplex D).firstCoboundaryCheckCode.carrier := by
  rw [ChainComplexData.mem_firstCoboundaryCheckCode_iff]
  exact ⟨u, rfl⟩

/-- Adding a bundle coboundary preserves the cocycle condition. -/
theorem add_bundleCoboundary_mem_middleCocycleCode_iff
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    x + bundleCoboundary D u ∈ (chainComplex D).middleCocycleCode.carrier ↔
      x ∈ (chainComplex D).middleCocycleCode.carrier := by
  apply Submodule.add_mem_iff_left
  exact (chainComplex D).firstCoboundaryCheckCode_le_middleCocycleCode
    (bundleCoboundary_mem_firstCoboundaryCheckCode D u)

/-- Adding a bundle coboundary preserves nontriviality of a cohomology class. -/
theorem add_bundleCoboundary_not_mem_firstCoboundaryCheckCode_iff
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    x + bundleCoboundary D u ∉
        (chainComplex D).firstCoboundaryCheckCode.carrier ↔
      x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier := by
  exact not_congr
    ((chainComplex D).firstCoboundaryCheckCode.carrier.add_mem_iff_left
      (bundleCoboundary_mem_firstCoboundaryCheckCode D u))

/-- Total Hamming weight is the exact sum of horizontal and vertical weights. -/
theorem hammingWeight_eq_horizontal_add_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight x =
      HammingWeight (horizontalComponent x) +
        HammingWeight (verticalComponent x) := by
  classical
  rw [hammingWeight_eq_sum_indicator, Fintype.sum_sum_type,
    hammingWeight_eq_sum_indicator, hammingWeight_eq_sum_indicator]
  rfl

/-- Horizontal weight is the sum of the weights of its fiber words. -/
theorem hammingWeight_horizontalComponent_eq_sum_fibers
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (horizontalComponent x) =
      ∑ b : baseOne, HammingWeight (horizontalFiber x b) := by
  classical
  rw [hammingWeight_eq_sum_indicator, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [hammingWeight_eq_sum_indicator]
  rfl

/-- The total horizontal cost of erasing one fiber is degree times fiber weight. -/
theorem hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    HammingWeight
        (horizontalComponent
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a))) =
      RandomBase.checkDegree baseSample a * HammingWeight (c0Fiber u a) := by
  rw [hammingWeight_horizontalComponent_eq_sum_fibers]
  simp_rw [
    hammingWeight_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection]
  classical
  rw [RandomBase.checkDegree, Finset.card_eq_sum_ones, Finset.sum_mul]
  simp only [one_mul]
  rw [Finset.sum_filter]

/-- A one-fiber erasure can increase horizontal weight by at most its exact cost. -/
theorem hammingWeight_horizontalComponent_eraseC0Fiber_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) ≤
      HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) +
        RandomBase.checkDegree baseSample a * HammingWeight (c0Fiber u a) := by
  rw [horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber,
    horizontalComponent_add]
  refine (HammingWeight_add_le _ _).trans_eq ?_
  rw [hammingWeight_horizontalComponent_bundleCoboundary_eraseC0FiberCorrection]

/--
Finite-sum descent principle used by the `> 4/5` counique argument: the erased
set contributes a fixed positive saving, while all remaining coordinates pay
strictly less total correction cost.
-/
theorem sum_strictly_decreases_of_erased_savings
    {β : Type u} [Fintype β] [DecidableEq β]
    (C : Finset β) (old new cost : β → Nat) (w : Nat)
    (hNewZero : ∀ b ∈ C, new b = 0)
    (hOldWeight : ∀ b ∈ C, old b = w)
    (hOutside : ∀ b ∈ (Finset.univ \ C), new b ≤ old b + cost b)
    (hCost :
      (∑ b ∈ (Finset.univ \ C), cost b) < C.card * w) :
    (∑ b : β, new b) < ∑ b : β, old b := by
  classical
  let R : Finset β := Finset.univ \ C
  have hDisjoint : Disjoint C R := by
    rw [Finset.disjoint_left]
    intro b hbC hbR
    exact (Finset.mem_sdiff.mp hbR).2 hbC
  have hUnion : C ∪ R = Finset.univ := by
    ext b
    simp [R]
  have hNewC : (∑ b ∈ C, new b) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    exact hNewZero b hb
  have hOldC : (∑ b ∈ C, old b) = C.card * w := by
    calc
      (∑ b ∈ C, old b) = ∑ _b ∈ C, w := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hOldWeight b hb
      _ = C.card * w := by simp
  have hNewPartition :
      (∑ b : β, new b) = (∑ b ∈ C, new b) + ∑ b ∈ R, new b := by
    rw [← Finset.sum_union hDisjoint, hUnion]
  have hOldPartition :
      (∑ b : β, old b) = (∑ b ∈ C, old b) + ∑ b ∈ R, old b := by
    rw [← Finset.sum_union hDisjoint, hUnion]
  calc
    (∑ b : β, new b) = ∑ b ∈ R, new b := by
      rw [hNewPartition, hNewC, zero_add]
    _ ≤ (∑ b ∈ R, old b) + ∑ b ∈ R, cost b := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun b hb => hOutside b hb
    _ < (∑ b ∈ R, old b) + C.card * w := by
      exact Nat.add_lt_add_left hCost _
    _ = ∑ b : β, old b := by
      rw [hOldPartition, hOldC, add_comm]

/--
For a `> 4/5` counique check, correction cost outside its counique variables
is strictly smaller than the saving on those variables.
-/
theorem erasureCorrection_cost_outside_counique_lt
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (S : Finset (Fin (3 * r))) (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample S a) :
    let C :=
      (RandomBase.couniqueNeighbors baseSample S).filter
        fun b => baseSample (a, b)
    (∑ b ∈ (Finset.univ \ C),
        HammingWeight
          (horizontalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0FiberCorrection u a)) b)) <
      C.card * HammingWeight (c0Fiber u a) := by
  classical
  let C :=
    (RandomBase.couniqueNeighbors baseSample S).filter
      fun b => baseSample (a, b)
  let N := (Finset.univ : Finset (Fin (4 * r))).filter
    fun b => baseSample (a, b)
  have hCsubsetN : C ⊆ N := by
    intro b hb
    have hbEdge := (Finset.mem_filter.mp hb).2
    simp [N, hbEdge]
  have hfilter :
      (Finset.univ \ C).filter (fun b => baseSample (a, b)) = N \ C := by
    ext b
    simp [N, and_comm]
  have hCcard :
      C.card = RandomBase.couniqueDegree baseSample S a := by
    rfl
  have hNcard : N.card = RandomBase.checkDegree baseSample a := by
    rfl
  have hwPos : 0 < HammingWeight (c0Fiber u a) := by
    have hne : c0Fiber u a ≠ 0 := by
      simpa [c0Shadow] using ha
    have : HammingWeight (c0Fiber u a) ≠ 0 := by
      intro hzero
      exact hne ((HammingWeight_eq_zero_iff (c0Fiber u a)).mp hzero)
    omega
  simp_rw [
    hammingWeight_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection]
  rw [← Finset.sum_filter, hfilter]
  calc
    (∑ _b ∈ N \ C, HammingWeight (c0Fiber u a)) =
        (N \ C).card * HammingWeight (c0Fiber u a) := by simp
    _ = (RandomBase.checkDegree baseSample a -
      RandomBase.couniqueDegree baseSample S a) *
        HammingWeight (c0Fiber u a) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hCsubsetN,
        hNcard, hCcard]
    _ < RandomBase.couniqueDegree baseSample S a *
        HammingWeight (c0Fiber u a) := by
      exact (Nat.mul_lt_mul_right hwPos).2 (by omega)
    _ = C.card * HammingWeight (c0Fiber u a) := by rw [hCcard]

/--
The HHO20 `C ∩ x = ∅` move strictly decreases total horizontal weight after
erasing the selected `> 4/5` counique fiber.
-/
theorem hammingWeight_horizontalComponent_eraseC0Fiber_lt_of_four_fifths
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a)
    (hDisjoint :
      ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
        x b = 0) :
    HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) <
      HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  let C :=
    (RandomBase.couniqueNeighbors baseSample (c0Shadow u)).filter
      fun b => baseSample (a, b)
  let oldRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u
  let newRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (eraseC0Fiber u a)
  let correction :=
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample)
      (eraseC0FiberCorrection u a)
  rw [hammingWeight_horizontalComponent_eq_sum_fibers,
    hammingWeight_horizontalComponent_eq_sum_fibers]
  apply sum_strictly_decreases_of_erased_savings
    C
    (fun b => HammingWeight (horizontalFiber oldRepresentative b))
    (fun b => HammingWeight (horizontalFiber newRepresentative b))
    (fun b => HammingWeight (horizontalFiber correction b))
    (HammingWeight (c0Fiber u a))
  · intro b hbC
    have hbCounique := (Finset.mem_filter.mp hbC).1
    have hab := (Finset.mem_filter.mp hbC).2
    exact
      (hammingWeight_horizontalFiber_before_after_erase_of_counique
        baseSample twistSample x u a b ha hbCounique hab
        (hDisjoint b hbCounique)).2
  · intro b hbC
    have hbCounique := (Finset.mem_filter.mp hbC).1
    have hab := (Finset.mem_filter.mp hbC).2
    exact
      (hammingWeight_horizontalFiber_before_after_erase_of_counique
        baseSample twistSample x u a b ha hbCounique hab
        (hDisjoint b hbCounique)).1
  · intro b _hbOutside
    have hRepresentative :=
      horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
        (RandomTwist.fiberBundleData baseSample twistSample) x u a
    have hFiber :
        horizontalFiber newRepresentative b =
          horizontalFiber oldRepresentative b + horizontalFiber correction b := by
      exact congrArg (fun y => horizontalFiber y b) hRepresentative
    rw [hFiber]
    exact HammingWeight_add_le _ _
  · exact erasureCorrection_cost_outside_counique_lt
      baseSample twistSample u (c0Shadow u) a ha hCounique

/-- One horizontal fiber contributes no more weight than the whole horizontal sector. -/
theorem hammingWeight_horizontalFiber_le_horizontalComponent
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) :
    HammingWeight (horizontalFiber x b) ≤
      HammingWeight (horizontalComponent x) := by
  rw [hammingWeight_horizontalComponent_eq_sum_fibers]
  exact Finset.single_le_sum
    (f := fun b' => HammingWeight (horizontalFiber x b'))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

/--
The generic counique-support case forces the whole horizontal sector to
occupy at least half a fiber.
-/
theorem card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  let representative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u
  have hfiber :
      Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight (horizontalFiber representative b) := by
    exact
      card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique_of_normalized
        baseSample twistSample x u hu b hb hxb
  have hsector :
      HammingWeight (horizontalFiber representative b) ≤
        HammingWeight (horizontalComponent representative) :=
    hammingWeight_horizontalFiber_le_horizontalComponent representative b
  exact hfiber.trans (Nat.mul_le_mul_left 2 hsector)

/--
When the zero-cell shadow is empty, a nonzero lifted base cochain contributes
an entire horizontal fiber.
-/
theorem card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hx : x ≠ 0)
    (hShadow : c0Shadow u = ∅) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  have hu : u = 0 := eq_zero_of_c0Shadow_eq_empty u hShadow
  subst u
  have hExists : ∃ b, x b ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (by funext b; exact h b)
  rcases hExists with ⟨b, hxb⟩
  have hxbOne : x b = 1 :=
    RandomBase.zmod2_eq_one_of_ne_zero (x b) hxb
  let representative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) 0
  have hCoboundaryZero :
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) 0 = 0 := by
    exact map_zero
      (wordLinearMapTranspose
        (boundary1 (RandomTwist.fiberBundleData baseSample twistSample)))
  have hFiber :
      horizontalFiber representative b =
        (fun _i : ZMod (ell * ell) => 1) := by
    funext i
    rw [show representative =
      horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x by
        simp [representative, hCoboundaryZero]]
    exact congrFun (horizontalFiber_horizontalBaseLift
      (baseZero := Fin (3 * r)) (fiberOne := ZMod (ell * ell)) x b) i |>.trans
        hxbOne
  have hFiberWeight :
      HammingWeight (horizontalFiber representative b) =
        Fintype.card (ZMod (ell * ell)) := by
    rw [hFiber, hammingWeight_eq_sum_indicator]
    simp
  have hSector :=
    hammingWeight_horizontalFiber_le_horizontalComponent representative b
  rw [hFiberWeight] at hSector
  exact hSector.trans (Nat.le_mul_of_pos_left _ (by omega))

/--
The preceding counique-support case already forces the whole horizontal
sector to occupy at least half a fiber.
-/
theorem card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample
      (c0Shadow (normalizeC0Fibers u)))
    (hxb : x b ≠ 0) :
    Fintype.card (ZMod (ell * ell)) ≤
      2 * HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u))) := by
  let representative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (normalizeC0Fibers u)
  have hfiber :
      Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight (horizontalFiber representative b) := by
    exact
      card_le_twice_hammingWeight_horizontalFiber_add_lift_of_counique
        baseSample twistSample x u b hb hxb
  have hsector :
      HammingWeight (horizontalFiber representative b) ≤
        HammingWeight (horizontalComponent representative) :=
    hammingWeight_horizontalFiber_le_horizontalComponent representative b
  exact hfiber.trans (Nat.mul_le_mul_left 2 hsector)

/-- Vertical weight is the sum of the weights of its fiber words. -/
theorem hammingWeight_verticalComponent_eq_sum_fibers
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (verticalComponent x) =
      ∑ a : baseZero, HammingWeight (verticalFiber x a) := by
  classical
  rw [hammingWeight_eq_sum_indicator, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [hammingWeight_eq_sum_indicator]
  rfl

/-- Erasing one degree-zero fiber cannot increase any vertical fiber weight. -/
theorem hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a a' : Fin (3 * r)) :
    HammingWeight
        (verticalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0Fiber u a)) a') ≤
      HammingWeight
        (verticalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) a') := by
  by_cases ha : a' = a
  · subst a'
    have hFiberZero :
        verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a)) a = 0 := by
      rw [verticalFiber_bundleCoboundary_fiberBundleData,
        c0Fiber_eraseC0Fiber_same]
      funext j
      simp [cycleFiberCoboundary]
    rw [hFiberZero, HammingWeight_zero]
    exact Nat.zero_le _
  · have hFiberEq :
        verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a)) a' =
          verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) a' := by
      rw [verticalFiber_bundleCoboundary_fiberBundleData,
        verticalFiber_bundleCoboundary_fiberBundleData,
        c0Fiber_eraseC0Fiber_of_ne u ha]
    rw [hFiberEq]

/-- Erasing one degree-zero fiber cannot increase total vertical weight. -/
theorem hammingWeight_verticalComponent_eraseC0Fiber_le
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r)) :
    HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  rw [verticalComponent_horizontalBaseLift_add,
    verticalComponent_horizontalBaseLift_add,
    hammingWeight_verticalComponent_eq_sum_fibers,
    hammingWeight_verticalComponent_eq_sum_fibers]
  exact Finset.sum_le_sum fun a' _ =>
    hammingWeight_verticalFiber_bundleCoboundary_eraseC0Fiber_le
      baseSample twistSample u a a'

/--
The HHO20 `C ∩ x = ∅` erasure move strictly decreases the full representative
weight, not only its horizontal sector.
-/
theorem hammingWeight_eraseC0Fiber_lt_of_four_fifths
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a)
    (hDisjoint :
      ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
        x b = 0) :
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0Fiber u a)) <
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by
  rw [hammingWeight_eq_horizontal_add_vertical,
    hammingWeight_eq_horizontal_add_vertical]
  have hHorizontal :=
    hammingWeight_horizontalComponent_eraseC0Fiber_lt_of_four_fifths
      baseSample twistSample x u a ha hCounique hDisjoint
  have hVertical :=
    hammingWeight_verticalComponent_eraseC0Fiber_le
      baseSample twistSample x u a
  omega

/-- A fiberwise-normalized shadow gives a doubled lower bound on vertical weight. -/
theorem twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u) :
    2 * (c0Shadow u).card ≤
      HammingWeight
        (verticalComponent
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  rw [hammingWeight_verticalComponent_eq_sum_fibers]
  calc
    2 * (c0Shadow u).card =
        ∑ _a ∈ c0Shadow u, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ c0Shadow u,
        HammingWeight
          (verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) a) := by
      exact Finset.sum_le_sum fun a ha =>
        two_le_hammingWeight_verticalFiber_coboundary_of_mem_shadow_of_normalized
          baseSample twistSample u hu a ha
    _ ≤ ∑ a : Fin (3 * r),
        HammingWeight
          (verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) a) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- The normalized shadow gives a doubled lower bound on total vertical weight. -/
theorem twice_card_c0Shadow_le_hammingWeight_verticalComponent_normalizedCoboundary
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    2 * (c0Shadow (normalizeC0Fibers u)).card ≤
      HammingWeight
        (verticalComponent
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u))) := by
  rw [hammingWeight_verticalComponent_eq_sum_fibers]
  calc
    2 * (c0Shadow (normalizeC0Fibers u)).card =
        ∑ _a ∈ c0Shadow (normalizeC0Fibers u), 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ c0Shadow (normalizeC0Fibers u),
        HammingWeight
          (verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u)) a) := by
      apply Finset.sum_le_sum
      intro a ha
      exact
        two_le_hammingWeight_verticalFiber_normalizedCoboundary_of_mem_shadow
          baseSample twistSample u a ha
    _ ≤ ∑ a : Fin (3 * r),
        HammingWeight
          (verticalFiber
            (bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u)) a) := by
      exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/--
The generic normalized-shadow lower bound is unchanged after adding a
horizontal base lift.
-/
theorem twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift_of_normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u) :
    2 * (c0Shadow u).card ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  rw [verticalComponent_horizontalBaseLift_add]
  exact
    twice_card_c0Shadow_le_hammingWeight_verticalComponent_coboundary_of_normalized
      baseSample twistSample u hu

/--
The same large-shadow lower bound holds for the full normalized representative,
because the lifted base cochain has no vertical coordinates.
-/
theorem twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    2 * (c0Shadow (normalizeC0Fibers u)).card ≤
      HammingWeight
        (verticalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (normalizeC0Fibers u))) := by
  rw [verticalComponent_horizontalBaseLift_add]
  exact
    twice_card_c0Shadow_le_hammingWeight_verticalComponent_normalizedCoboundary
      baseSample twistSample u

/--
The large-shadow lower bound for an arbitrary fiberwise-normalized
representative.
-/
theorem large_shadow_vertical_weight_of_normalized
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (hLarge : 3 * r < 100000 * Delta * (c0Shadow u).card) :
    6 * r <
      100000 * Delta *
        HammingWeight
          (verticalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  have hvertical :=
    twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift_of_normalized
      baseSample twistSample x u hu
  nlinarith

/--
In the paper's large-shadow case, the vertical sector already has the stated
inverse-degree scale, with all constants kept as integer inequalities.
-/
theorem large_shadow_vertical_weight
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hLarge :
      3 * r < 100000 * Delta * (c0Shadow (normalizeC0Fibers u)).card) :
    6 * r <
      100000 * Delta *
        HammingWeight
          (verticalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample)
                (normalizeC0Fibers u))) := by
  have hvertical :=
    twice_card_c0Shadow_le_hammingWeight_verticalComponent_add_lift
      baseSample twistSample x u
  nlinarith

/--
The chosen degree-zero correction has minimum horizontal weight among all
corrections of the same lifted base cochain.
-/
def IsHorizontalWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) : Prop :=
  ∀ v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
    HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) ≤
      HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) v))

/-- The chosen correction has minimum full Hamming weight for the lifted class. -/
def IsWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) : Prop :=
  ∀ v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) ≤
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v)

/-- A full-weight-minimal correction exists because the correction space is finite. -/
theorem exists_isWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      IsWeightMinimal baseSample twistSample x u := by
  classical
  let weight := fun u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
    HammingWeight
      (horizontalBaseLift
          (baseZero := Fin (3 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) x +
        bundleCoboundary
          (RandomTwist.fiberBundleData baseSample twistSample) u)
  obtain ⟨u, _hu, hleast⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset
        (Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell)))))
      weight Finset.univ_nonempty
  refine ⟨u, ?_⟩
  intro v
  exact hleast v (Finset.mem_univ v)

/-- A horizontal-weight-minimal correction exists because the correction space is finite. -/
theorem exists_isHorizontalWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      IsHorizontalWeightMinimal baseSample twistSample x u := by
  classical
  let weight := fun u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
    HammingWeight
      (horizontalComponent
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u))
  obtain ⟨u, _hu, hleast⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset
        (Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell)))))
      weight Finset.univ_nonempty
  refine ⟨u, ?_⟩
  intro v
  exact hleast v (Finset.mem_univ v)

/--
Fiberwise normalization preserves horizontal minimality after applying the
explicit induced base shift.
-/
theorem IsHorizontalWeightMinimal.normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hMinimal : IsHorizontalWeightMinimal baseSample twistSample x u) :
    IsHorizontalWeightMinimal baseSample twistSample
      (x + normalizationBaseShift baseSample u)
      (QEC.Coding.FiberBundle.normalizeC0Fibers u) := by
  intro v
  let weight := fun representative :
      Word (ZMod 2)
        (QubitIndex (Fin (3 * r)) (Fin (4 * r))
          (ZMod (ell * ell)) (ZMod (ell * ell))) =>
    HammingWeight (horizontalComponent representative)
  calc
    weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (QEC.Coding.FiberBundle.normalizeC0Fibers u)) =
      weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by
        exact congrArg weight
          (horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
            baseSample twistSample x u)
    _ ≤
      weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (v + normalizationToggleWord u)) :=
        hMinimal (v + normalizationToggleWord u)
    _ =
      weight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v) := by
        exact congrArg weight
          (horizontalBaseLift_add_bundleCoboundary_baseShift
            baseSample twistSample x u v).symm

/-- Full-weight minimality is preserved by normalization and its base shift. -/
theorem IsWeightMinimal.normalized
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hMinimal : IsWeightMinimal baseSample twistSample x u) :
    IsWeightMinimal baseSample twistSample
      (x + normalizationBaseShift baseSample u)
      (normalizeC0Fibers u) := by
  intro v
  calc
    HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (normalizeC0Fibers u)) =
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) := by
        exact congrArg HammingWeight
          (horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
            baseSample twistSample x u)
    _ ≤
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (v + normalizationToggleWord u)) :=
        hMinimal (v + normalizationToggleWord u)
    _ =
      HammingWeight
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell))
            (x + normalizationBaseShift baseSample u) +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) v) := by
        exact congrArg HammingWeight
          (horizontalBaseLift_add_bundleCoboundary_baseShift
            baseSample twistSample x u v).symm

/--
Every nontrivial lifted base class admits a correction whose normalized,
base-shifted presentation is simultaneously nonzero in the base direction,
fiberwise normalized, and horizontal-weight minimal.
-/
theorem exists_normalized_horizontalWeightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      x + normalizationBaseShift baseSample u ≠ 0 ∧
      C0FibersNormalized (normalizeC0Fibers u) ∧
      IsHorizontalWeightMinimal baseSample twistSample
        (x + normalizationBaseShift baseSample u)
        (normalizeC0Fibers u) := by
  rcases exists_isHorizontalWeightMinimal baseSample twistSample x with
    ⟨u, hMinimal⟩
  refine ⟨u, ?_, c0FibersNormalized_normalizeC0Fibers u, ?_⟩
  · simpa [normalizationBaseShift] using
      (IsNontrivialBaseCohomology.add_baseCoboundary_ne_zero
        baseSample x hx (normalizationToggle u))
  · exact hMinimal.normalized baseSample twistSample x u

/--
Every nontrivial lifted base class admits a fiberwise-normalized presentation
which is nonzero in the base direction and minimizes full Hamming weight over
all degree-zero corrections.
-/
theorem exists_normalized_weightMinimal
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      x + normalizationBaseShift baseSample u ≠ 0 ∧
      C0FibersNormalized (normalizeC0Fibers u) ∧
      IsWeightMinimal baseSample twistSample
        (x + normalizationBaseShift baseSample u)
        (normalizeC0Fibers u) := by
  rcases exists_isWeightMinimal baseSample twistSample x with
    ⟨u, hMinimal⟩
  refine ⟨u, ?_, c0FibersNormalized_normalizeC0Fibers u, ?_⟩
  · simpa [normalizationBaseShift] using
      (IsNontrivialBaseCohomology.add_baseCoboundary_ne_zero
        baseSample x hx (normalizationToggle u))
  · exact hMinimal.normalized baseSample twistSample x u

/--
For a nonempty small shadow of any fiberwise-normalized representative,
either a supported counique variable forces half-fiber horizontal weight or
the selected `> 4/5` counique check is disjoint from the lifted base support.
-/
theorem horizontal_half_or_exists_descent_check_of_normalized
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hShadowNonempty : (c0Shadow u).Nonempty)
    (hSmall : 100000 * Delta * (c0Shadow u).card ≤ 3 * r) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) ∨
      ∃ a ∈ c0Shadow u,
        4 * RandomBase.checkDegree baseSample a <
          5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a ∧
        ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
          x b = 0 := by
  rcases RandomBase.exists_check_four_fifths_counique
      hDelta hDegree hExpansion (c0Shadow u) hShadowNonempty hSmall with
    ⟨a, haShadow, haCounique⟩
  by_cases hSupported :
      ∃ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u), x b ≠ 0
  · rcases hSupported with ⟨b, hbCounique, hxb⟩
    exact Or.inl
      (card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique_of_normalized
        baseSample twistSample x u hu b hbCounique hxb)
  · right
    refine ⟨a, haShadow, haCounique, ?_⟩
    intro b hbCounique
    by_contra hxb
    exact hSupported ⟨b, hbCounique, hxb⟩

/--
For a normalized horizontal-weight-minimal representative with nonzero base
cochain, the strict-descent branch is impossible.  Hence either the
horizontal sector occupies at least half a fiber or the vertical sector
satisfies the large-shadow inverse-degree bound.
-/
theorem horizontal_or_vertical_weight_of_normalized_horizontal_minimal
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hx : x ≠ 0)
    (hu : C0FibersNormalized u)
    (hMinimal : IsHorizontalWeightMinimal baseSample twistSample x u)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) ∨
      6 * r <
        100000 * Delta *
          HammingWeight
            (verticalComponent
              (horizontalBaseLift
                  (baseZero := Fin (3 * r))
                  (fiberZero := ZMod (ell * ell))
                  (fiberOne := ZMod (ell * ell)) x +
                bundleCoboundary
                  (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  by_cases hShadowEmpty : c0Shadow u = ∅
  · exact Or.inl
      (card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
        baseSample twistSample x u hx hShadowEmpty)
  · have hShadowNonempty : (c0Shadow u).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hShadowEmpty
    by_cases hLarge : 3 * r < 100000 * Delta * (c0Shadow u).card
    · exact Or.inr
        (large_shadow_vertical_weight_of_normalized
          baseSample twistSample x u hu hLarge)
    · have hSmall :
          100000 * Delta * (c0Shadow u).card ≤ 3 * r :=
        Nat.le_of_not_gt hLarge
      rcases
          horizontal_half_or_exists_descent_check_of_normalized
            baseSample twistSample x u hu hDelta hDegree hExpansion
            hShadowNonempty hSmall with
        hHorizontal | ⟨a, haShadow, haCounique, hDisjoint⟩
      · exact Or.inl hHorizontal
      · have hStrict :=
          hammingWeight_horizontalComponent_eraseC0Fiber_lt_of_four_fifths
            baseSample twistSample x u a haShadow haCounique hDisjoint
        have hLeast := hMinimal (eraseC0Fiber u a)
        exact (Nat.not_lt_of_ge hLeast hStrict).elim

/--
For a normalized full-weight-minimal representative with nonzero base
cochain, the strict total-weight descent branch is impossible.  Thus the
representative obeys either the horizontal half-fiber bound or the vertical
large-shadow bound.
-/
theorem horizontal_or_vertical_weight_of_normalized_weight_minimal
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hx : x ≠ 0)
    (hu : C0FibersNormalized u)
    (hMinimal : IsWeightMinimal baseSample twistSample x u)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) ∨
      6 * r <
        100000 * Delta *
          HammingWeight
            (verticalComponent
              (horizontalBaseLift
                  (baseZero := Fin (3 * r))
                  (fiberZero := ZMod (ell * ell))
                  (fiberOne := ZMod (ell * ell)) x +
                bundleCoboundary
                  (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  by_cases hShadowEmpty : c0Shadow u = ∅
  · exact Or.inl
      (card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
        baseSample twistSample x u hx hShadowEmpty)
  · have hShadowNonempty : (c0Shadow u).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hShadowEmpty
    by_cases hLarge : 3 * r < 100000 * Delta * (c0Shadow u).card
    · exact Or.inr
        (large_shadow_vertical_weight_of_normalized
          baseSample twistSample x u hu hLarge)
    · have hSmall :
          100000 * Delta * (c0Shadow u).card ≤ 3 * r :=
        Nat.le_of_not_gt hLarge
      rcases
          horizontal_half_or_exists_descent_check_of_normalized
            baseSample twistSample x u hu hDelta hDegree hExpansion
            hShadowNonempty hSmall with
        hHorizontal | ⟨a, haShadow, haCounique, hDisjoint⟩
      · exact Or.inl hHorizontal
      · have hStrict :=
          hammingWeight_eraseC0Fiber_lt_of_four_fifths
            baseSample twistSample x u a haShadow haCounique hDisjoint
        have hLeast := hMinimal (eraseC0Fiber u a)
        exact (Nat.not_lt_of_ge hLeast hStrict).elim

/--
Every correction of a nontrivial lifted base class obeys the HHO20
cohomology-weight alternative.  The proof selects a full-weight-minimal
correction, normalizes it without changing its representative, applies the
shadow dichotomy, and transfers the resulting lower bound back to the
arbitrary correction.
-/
theorem weight_bound_for_all_corrections_of_nontrivial_base
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (hx : IsNontrivialBaseCohomology baseSample x)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (v : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell)))) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) v) ∨
      6 * r <
        100000 * Delta *
          HammingWeight
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) v) := by
  rcases exists_isWeightMinimal baseSample twistSample x with
    ⟨u, hMinimal⟩
  let shiftedX := x + normalizationBaseShift baseSample u
  let normalizedU := normalizeC0Fibers u
  let normalizedRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) shiftedX +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) normalizedU
  let arbitraryRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) v
  have hShiftedNonzero : shiftedX ≠ 0 := by
    simpa [shiftedX, normalizationBaseShift] using
      (IsNontrivialBaseCohomology.add_baseCoboundary_ne_zero
        baseSample x hx (normalizationToggle u))
  have hNormalized : C0FibersNormalized normalizedU := by
    exact c0FibersNormalized_normalizeC0Fibers u
  have hNormalizedMinimal :
      IsWeightMinimal baseSample twistSample shiftedX normalizedU := by
    exact hMinimal.normalized baseSample twistSample x u
  have hRepresentativeEq :
      normalizedRepresentative =
        horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u := by
    exact horizontalBaseLift_add_bundleCoboundary_normalizeC0Fibers
      baseSample twistSample x u
  have hWeightLe :
      HammingWeight normalizedRepresentative ≤
        HammingWeight arbitraryRepresentative := by
    rw [hRepresentativeEq]
    exact hMinimal v
  rcases
      horizontal_or_vertical_weight_of_normalized_weight_minimal
        baseSample twistSample shiftedX normalizedU hShiftedNonzero
        hNormalized hNormalizedMinimal hDelta hDegree hExpansion with
    hHorizontal | hVertical
  · left
    have hSector :
        HammingWeight (horizontalComponent normalizedRepresentative) ≤
          HammingWeight normalizedRepresentative := by
      rw [hammingWeight_eq_horizontal_add_vertical]
      omega
    exact hHorizontal.trans
      ((Nat.mul_le_mul_left 2 hSector).trans
        (Nat.mul_le_mul_left 2 hWeightLe))
  · right
    have hSector :
        HammingWeight (verticalComponent normalizedRepresentative) ≤
          HammingWeight normalizedRepresentative := by
      rw [hammingWeight_eq_horizontal_add_vertical]
      omega
    exact hVertical.trans_le
      ((Nat.mul_le_mul_left (100000 * Delta) hSector).trans
        (Nat.mul_le_mul_left (100000 * Delta) hWeightLe))

/--
For a nonempty small normalized shadow, either a supported counique variable
already forces half-fiber horizontal weight, or the selected `> 4/5`
counique check is disjoint from the lifted base support.  The latter is the
strict-descent branch of HHO20's proof.
-/
theorem horizontal_half_or_exists_descent_check
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hShadowNonempty : (c0Shadow (normalizeC0Fibers u)).Nonempty)
    (hSmall :
      100000 * Delta * (c0Shadow (normalizeC0Fibers u)).card ≤ 3 * r) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample)
                (normalizeC0Fibers u))) ∨
      ∃ a ∈ c0Shadow (normalizeC0Fibers u),
        4 * RandomBase.checkDegree baseSample a <
          5 * RandomBase.couniqueDegree baseSample
            (c0Shadow (normalizeC0Fibers u)) a ∧
        ∀ b ∈ RandomBase.couniqueNeighbors baseSample
            (c0Shadow (normalizeC0Fibers u)),
          x b = 0 := by
  rcases RandomBase.exists_check_four_fifths_counique
      hDelta hDegree hExpansion
      (c0Shadow (normalizeC0Fibers u)) hShadowNonempty hSmall with
    ⟨a, haShadow, haCounique⟩
  by_cases hSupported :
      ∃ b ∈ RandomBase.couniqueNeighbors baseSample
        (c0Shadow (normalizeC0Fibers u)), x b ≠ 0
  · rcases hSupported with ⟨b, hbCounique, hxb⟩
    exact Or.inl
      (card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
        baseSample twistSample x u b hbCounique hxb)
  · right
    refine ⟨a, haShadow, haCounique, ?_⟩
    intro b hbCounique
    by_contra hxb
    exact hSupported ⟨b, hbCounique, hxb⟩

/-- Every base cell in the horizontal shadow contributes at least one cell. -/
theorem card_horizontalShadow_le_hammingWeight
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseOne] [Fintype fiberZero]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    (horizontalShadow x).card ≤ HammingWeight (horizontalComponent x) := by
  rw [hammingWeight_horizontalComponent_eq_sum_fibers]
  classical
  calc
    (horizontalShadow x).card =
        ∑ b : baseOne, if horizontalFiber x b ≠ 0 then 1 else 0 := by
      rw [horizontalShadow, Finset.card_filter]
    _ ≤ ∑ b : baseOne, HammingWeight (horizontalFiber x b) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : horizontalFiber x b = 0
      · rw [if_neg (by simpa using hb), hb, HammingWeight_zero]
      · rw [if_pos hb]
        have hweight : HammingWeight (horizontalFiber x b) ≠ 0 := by
          intro hzero
          exact hb ((HammingWeight_eq_zero_iff (horizontalFiber x b)).mp hzero)
        omega

/-- Every base cell in the vertical shadow contributes at least one cell. -/
theorem card_verticalShadow_le_hammingWeight
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype fiberOne]
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    (verticalShadow x).card ≤ HammingWeight (verticalComponent x) := by
  rw [hammingWeight_verticalComponent_eq_sum_fibers]
  classical
  calc
    (verticalShadow x).card =
        ∑ a : baseZero, if verticalFiber x a ≠ 0 then 1 else 0 := by
      rw [verticalShadow, Finset.card_filter]
    _ ≤ ∑ a : baseZero, HammingWeight (verticalFiber x a) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : verticalFiber x a = 0
      · rw [if_neg (by simpa using ha), ha, HammingWeight_zero]
      · rw [if_pos ha]
        have hweight : HammingWeight (verticalFiber x a) ≠ 0 := by
          intro hzero
          exact ha ((HammingWeight_eq_zero_iff (verticalFiber x a)).mp hzero)
        omega

end QEC.Coding.FiberBundle
