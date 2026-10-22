import QEC.Coding.FiberBundle.RandomTwist

/-!
# The HHO20 twist graph code

This module formalizes the deterministic graph and parity-check layer from
`hastings-haah-odonnell-2020-fiber-bundle/bundle.tex:1049-1093`.

For every check type `τ`, the sampled nonzero twist gives one directed edge
of type `τ` out of, and one directed edge of type `τ` into, every layer.
The parity check on the edge `u → v` reads tail incidences at `u` and head
incidences at `v`.  The quantitative light/heavy good events and their
probability bounds are proved in later closure modules; they are not fields
of this construction.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators

/-- Multiplication by `ell` from integers into the cycle of length `ell²`. -/
def scaleIntHom (ell : Nat) [NeZero ell] :
    ℤ →+ ZMod (ell * ell) where
  toFun z := (z : ZMod (ell * ell)) * (ell : Nat)
  map_zero' := by simp
  map_add' x y := by
    push_cast
    ring

/-- Multiplication by `ell` kills the defining relation of `ZMod ell`. -/
theorem scaleIntHom_ell_eq_zero (ell : Nat) [NeZero ell] :
    scaleIntHom ell ell = 0 := by
  simp only [scaleIntHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.cast_natCast]
  rw [← Nat.cast_mul, ZMod.natCast_self]

/--
The additive embedding of the `ell` twist-graph layers as the residue-zero
positions of the length-`ell²` bundle fiber.
-/
def layerEmbedding (ell : Nat) [NeZero ell] :
    ZMod ell →+ ZMod (ell * ell) :=
  ZMod.lift ell ⟨scaleIntHom ell, scaleIntHom_ell_eq_zero ell⟩

@[simp]
theorem layerEmbedding_natCast
    (ell k : Nat) [NeZero ell] :
    layerEmbedding ell (k : ZMod ell) =
      (k * ell : Nat) := by
  rw [show (k : ZMod ell) = ((k : ℤ) : ZMod ell) by norm_num]
  rw [layerEmbedding, ZMod.lift_coe]
  simp only [scaleIntHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.cast_natCast, Nat.cast_mul]

@[simp]
theorem layerEmbedding_eq_val_mul
    (ell : Nat) [NeZero ell] (u : ZMod ell) :
    layerEmbedding ell u =
      (u.val * ell : Nat) := by
  calc
    layerEmbedding ell u =
        layerEmbedding ell (u.val : ZMod ell) := by
          rw [ZMod.natCast_zmod_val]
    _ = (u.val * ell : Nat) :=
      layerEmbedding_natCast ell u.val

/-- Distinct twist-graph layers embed at distinct residue-zero fiber cells. -/
theorem layerEmbedding_injective
    (ell : Nat) [NeZero ell] :
    Function.Injective (layerEmbedding ell) := by
  by_cases hOne : ell = 1
  · subst ell
    intro u v _huv
    exact Subsingleton.elim u v
  intro u v huv
  apply ZMod.val_injective ell
  have hnat :
      (u.val : ZMod (ell * ell)) * (ell : ZMod (ell * ell)) =
        (v.val : ZMod (ell * ell)) * (ell : ZMod (ell * ell)) := by
    simpa only [layerEmbedding_eq_val_mul, Nat.cast_mul] using huv
  have hell : 0 < ell := NeZero.pos ell
  have htwo : 2 ≤ ell := by omega
  have huCast :
      (u.val : ZMod (ell * ell)).val = u.val := by
    rw [ZMod.val_natCast_of_lt]
    nlinarith [u.val_lt]
  have hvCast :
      (v.val : ZMod (ell * ell)).val = v.val := by
    rw [ZMod.val_natCast_of_lt]
    nlinarith [v.val_lt]
  have hellCast :
      (ell : ZMod (ell * ell)).val = ell := by
    rw [ZMod.val_natCast_of_lt]
    nlinarith
  have huBound : u.val * ell < ell * ell := by
    nlinarith [u.val_lt]
  have hvBound : v.val * ell < ell * ell := by
    nlinarith [v.val_lt]
  have huMulBound :
      (u.val : ZMod (ell * ell)).val *
          (ell : ZMod (ell * ell)).val < ell * ell := by
    simpa only [huCast, hellCast] using huBound
  have hvMulBound :
      (v.val : ZMod (ell * ell)).val *
          (ell : ZMod (ell * ell)).val < ell * ell := by
    simpa only [hvCast, hellCast] using hvBound
  have hval := congrArg ZMod.val hnat
  rw [ZMod.val_mul_of_lt huMulBound,
    ZMod.val_mul_of_lt hvMulBound,
    huCast, hvCast, hellCast] at hval
  exact Nat.eq_of_mul_eq_mul_right hell hval

/-- The fine fiber coordinate in layer `u` at block offset `k`. -/
def blockPosition
    (ell : Nat) [NeZero ell]
    (uk : ZMod ell × Fin ell) : ZMod (ell * ell) :=
  layerEmbedding ell uk.1 + (uk.2.val : Nat)

@[simp]
theorem blockPosition_val
    (ell : Nat) [NeZero ell]
    (u : ZMod ell) (k : Fin ell) :
    (blockPosition ell (u, k)).val = u.val * ell + k.val := by
  have hell : 0 < ell := NeZero.pos ell
  have huBound : u.val * ell < ell * ell := by
    nlinarith [u.val_lt]
  have hkBound : k.val < ell * ell := by
    nlinarith [k.isLt]
  have hsum : u.val * ell + k.val < ell * ell := by
    nlinarith [u.val_lt, k.isLt]
  rw [blockPosition, layerEmbedding_eq_val_mul, ZMod.val_add,
    ZMod.val_natCast_of_lt huBound, ZMod.val_natCast_of_lt hkBound,
    Nat.mod_eq_of_lt hsum]

/-- The layer/offset coordinates of a fine fiber position are unique. -/
theorem blockPosition_injective
    (ell : Nat) [NeZero ell] :
    Function.Injective (blockPosition ell) := by
  rintro ⟨u, k⟩ ⟨v, l⟩ huv
  have hval := congrArg ZMod.val huv
  rw [blockPosition_val, blockPosition_val] at hval
  have hkval : k.val = l.val := by
    have hmod := congrArg (fun n : Nat => n % ell) hval
    simpa [Nat.add_mod, Nat.mul_mod,
      Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt l.isLt] using hmod
  have hmul : u.val * ell = v.val * ell := by
    rw [hkval] at hval
    exact Nat.add_right_cancel hval
  have huval : u.val = v.val :=
    Nat.eq_of_mul_eq_mul_right (NeZero.pos ell) hmul
  exact Prod.ext
    (ZMod.val_injective ell huval)
    (Fin.ext hkval)

/--
The length-`ell²` fiber is exactly the product of `ell` coarse layers and
`ell` positions inside each layer block.
-/
noncomputable def blockEquiv
    (ell : Nat) [NeZero ell] :
    (ZMod ell × Fin ell) ≃ ZMod (ell * ell) :=
  Equiv.ofBijective (blockPosition ell)
    ((Fintype.bijective_iff_injective_and_card
      (blockPosition ell)).2
      ⟨blockPosition_injective ell, by simp [ZMod.card]⟩)

@[simp]
theorem blockEquiv_apply
    (ell : Nat) [NeZero ell]
    (uk : ZMod ell × Fin ell) :
    blockEquiv ell uk = blockPosition ell uk := by
  rfl

/-- The last position of the preceding block is the preceding fine cell. -/
theorem blockPosition_previous
    (ell : Nat) [NeZero ell] [NeZero (ell - 1)]
    (u : ZMod ell) :
    blockPosition ell
        (u - 1, ⟨ell - 1,
          Nat.sub_lt (NeZero.pos ell) Nat.zero_lt_one⟩) =
      layerEmbedding ell u - 1 := by
  have hEllPos : 0 < ell := NeZero.pos ell
  rw [blockPosition]
  change
    layerEmbedding ell (u - 1) +
        ((ell - 1 : Nat) : ZMod (ell * ell)) =
      layerEmbedding ell u - 1
  rw [map_sub]
  have hOne :
      layerEmbedding ell (1 : ZMod ell) =
        (ell : Nat) := by
    simpa using layerEmbedding_natCast ell 1
  rw [hOne]
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

/-- The nonzero layer displacement `φ_τ / ell` of a sampled type twist. -/
def step
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) : ZMod ell :=
  ((RandomTwist.typeTwist sample τ).val + 1 : Nat)

/-- The canonical representative of a type step lies in `1, ..., ell - 1`. -/
theorem step_val
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    (step sample τ).val =
      (RandomTwist.typeTwist sample τ).val + 1 := by
  rw [step, ZMod.val_natCast_of_lt]
  have h :=
    (RandomTwist.typeTwist sample τ).isLt
  omega

/-- Sampled type steps are genuinely nonzero modulo `ell`. -/
theorem step_ne_zero
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    step sample τ ≠ 0 := by
  intro hzero
  have hval := congrArg ZMod.val hzero
  rw [step_val, ZMod.val_zero] at hval
  omega

/-- A reduced graph step embeds as the corresponding full bundle rotation. -/
theorem layerEmbedding_step
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) :
    layerEmbedding ell (step sample τ) =
      multipleRotation ell
        ⟨(RandomTwist.typeTwist sample τ).val + 1, by
          have h := (RandomTwist.typeTwist sample τ).isLt
          omega⟩ := by
  rw [step, layerEmbedding_natCast]
  rfl

/--
Every incidence connection is either the identity (a head) or the embedded
nonzero step of its check type (a tail).
-/
theorem multipleRotation_connectionIndex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (sample : RandomTwist.Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r)) :
    multipleRotation ell (RandomTwist.connectionIndex sample b a) =
      if RandomTwist.isTail sample a b then
        layerEmbedding ell
          (step sample (RandomTwist.checkType typeCount a))
      else
        0 := by
  cases htail : RandomTwist.isTail sample a b with
  | true =>
    simp only [RandomTwist.connectionIndex, htail, if_true]
    rw [layerEmbedding_step]
  | false =>
    simp [RandomTwist.connectionIndex, htail, multipleRotation]

/-- Translation by the type-`τ` displacement, as a permutation of layers. -/
def typeTranslation
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) : Equiv.Perm (ZMod ell) :=
  Equiv.addRight (step sample τ)

/-- The unique type-`τ` out-neighbor of a layer. -/
def outNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) : ZMod ell :=
  typeTranslation sample τ u

/-- The unique type-`τ` in-neighbor of a layer. -/
def inNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) : ZMod ell :=
  (typeTranslation sample τ).symm u

@[simp]
theorem outNeighbor_eq_add
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    outNeighbor sample τ u = u + step sample τ := by
  rfl

@[simp]
theorem inNeighbor_eq_sub
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    inNeighbor sample τ u = u - step sample τ := by
  simp [inNeighbor, typeTranslation, sub_eq_add_neg]

@[simp]
theorem inNeighbor_outNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    inNeighbor sample τ (outNeighbor sample τ u) = u := by
  exact (typeTranslation sample τ).symm_apply_apply u

@[simp]
theorem outNeighbor_inNeighbor
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    outNeighbor sample τ (inNeighbor sample τ u) = u := by
  exact (typeTranslation sample τ).apply_symm_apply u

/-- The sampled directed twist graph has no self-loop. -/
theorem outNeighbor_ne
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount) (u : ZMod ell) :
    outNeighbor sample τ u ≠ u := by
  intro hloop
  apply step_ne_zero sample τ
  apply add_left_cancel (a := u)
  simpa using hloop

/--
At the target of a type edge, the inverse bundle connection reads a tail at
the source layer and a head at the target layer.
-/
theorem connection_onOne_symm_layerEmbedding_outNeighbor
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : ZMod ell) (b : Fin (4 * r)) (a : Fin (3 * r)) :
    ((((RandomTwist.fiberBundleData baseSample twistSample
      ).connection b a).onOne.symm)
        (layerEmbedding ell
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u))) =
      if RandomTwist.isTail twistSample a b then
        layerEmbedding ell u
      else
        layerEmbedding ell
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u) := by
  cases htail : RandomTwist.isTail twistSample a b with
  | true =>
    simp only [if_true]
    simp only [RandomTwist.fiberBundleData, multipleRotationCycleData,
      cycleData, cycleRotationAutomorphism]
    rw [Equiv.symm_apply_eq]
    change
      layerEmbedding ell
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u) =
        layerEmbedding ell u +
          multipleRotation ell
            (RandomTwist.connectionIndex twistSample b a)
    rw [multipleRotation_connectionIndex]
    simp only [htail, if_true, outNeighbor_eq_add, map_add,
      layerEmbedding_step]
  | false =>
    simp [RandomTwist.fiberBundleData, multipleRotationCycleData,
      cycleData, cycleRotationAutomorphism, RandomTwist.connectionIndex,
      htail, multipleRotation]
    rw [Equiv.symm_apply_eq]
    rfl

/--
The type-`τ` parity check attached to the directed edge
`u → outNeighbor τ u`.

Tail incidences read the word at the source layer and head incidences read it
at the target layer, exactly as in equation `eqn:ht-check` of HHO20.
-/
noncomputable def checkSyndrome
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) : ZMod 2 :=
  ∑ b : Fin (4 * r),
    RandomBase.boundary baseSample a b *
      if RandomTwist.isTail twistSample a b then
        w (u, b)
      else
        w
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u, b)

/-- The finite set of violated twist-graph checks. -/
noncomputable def violationSet
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell × Fin (3 * r)) := by
  classical
  exact Finset.univ.filter fun ua =>
    checkSyndrome baseSample twistSample w ua.1 ua.2 ≠ 0

/-- The number of violated twist-graph parity checks. -/
noncomputable def violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) : Nat :=
  (violationSet baseSample twistSample w).card

/-- All twist checks over one fixed base check, indexed by source layer. -/
noncomputable def checkColumn
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (a : Fin (3 * r)) :
    Word (ZMod 2) (ZMod ell) :=
  fun u => checkSyndrome baseSample twistSample w u a

/-- Violation count is the sum of the per-base-check column weights. -/
theorem violationCount_eq_sum_checkColumn
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    violationCount baseSample twistSample w =
      ∑ a : Fin (3 * r),
        HammingWeight (checkColumn baseSample twistSample w a) := by
  classical
  simp only [violationCount, violationSet, Finset.card_filter,
    HammingWeight, hammingSupport, checkColumn, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  exact (Finset.card_filter _ _).symm

theorem mem_violationSet_iff
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) :
    (u, a) ∈ violationSet baseSample twistSample w ↔
      checkSyndrome baseSample twistSample w u a ≠ 0 := by
  classical
  simp [violationSet]

/-- The subword seen at one twist-graph layer. -/
def layerWord
    {r ell : Nat}
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) : Word (ZMod 2) (Fin (4 * r)) :=
  fun b => w (u, b)

/-- The twist word restricted to one base variable across all layers. -/
def variableWord
    {r ell : Nat}
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (b : Fin (4 * r)) : Word (ZMod 2) (ZMod ell) :=
  fun u => w (u, b)

/-- Total twist-word weight is the sum of its layer weights. -/
theorem hammingWeight_eq_sum_layerWord
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      ∑ u : ZMod ell, HammingWeight (layerWord w u) := by
  classical
  simp only [HammingWeight, hammingSupport, Finset.card_filter,
    layerWord, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _hu
  exact (Finset.card_filter _ _).symm

/-- Total twist-word weight is also the sum over base-variable columns. -/
theorem hammingWeight_eq_sum_variableWord
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      ∑ b : Fin (4 * r), HammingWeight (variableWord w b) := by
  classical
  simp only [HammingWeight, hammingSupport, Finset.card_filter,
    variableWord, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  exact (Finset.card_filter _ _).symm

/--
The exact integer-cleared conclusion of HHO20 Theorem `thm:ltc`.

The small-weight threshold is `|w| ≤ ell * n / (5000 * Delta)` and the
soundness is `violations ≥ |w| / 250`, with `n = 4r`.  This proposition is an
internal good event to be proved for a construction-selected sample; it is
not a certificate accepted by the final fiber-bundle family theorem.
-/
def HasHHO20LocalTestability
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ w : Word (ZMod 2) (ZMod ell × Fin (4 * r)),
    5000 * Delta * HammingWeight w ≤ ell * (4 * r) →
      HammingWeight w ≤
        250 * violationCount baseSample twistSample w

end QEC.Coding.FiberBundle.TwistGraph
