import QEC.Coding.Stabilizer.PauliSemantics
import QEC.Distillation.Universality.OneQubitPhase
import QEC.Distillation.Core.TransversalGate
/-!
# BH12 triorthogonal CSS codes

Generic binary row families, the algebraic consequences of pairwise
triorthogonality, and the normalized CSS encoding used by the BH12
transversal-gate construction.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace Triorthogonal

open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

universe uR uM uI

private theorem quotientMkFiber_natCard
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) (q : M ⧸ S) :
    Nat.card {x : M // S.mkQ x = q} = Nat.card S := by
  classical
  have hcard := AddMonoidHom.card_fiber_eq_of_mem_range S.mkQ
    (S.mkQ_surjective q) (S.mkQ_surjective 0)
  let ezero : {x : M // S.mkQ x = 0} ≃ S :=
    { toFun := fun x => ⟨x, (Submodule.Quotient.mk_eq_zero S).mp x.2⟩
      invFun := fun x => ⟨x, (Submodule.Quotient.mk_eq_zero S).mpr x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  change Nat.card {x : M // S.mkQ x = q} = Nat.card S
  calc
    _ = Fintype.card {x : M // S.mkQ x = q} := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun x : M => S.mkQ x = q).card := Fintype.card_subtype _
    _ = (Finset.univ.filter fun x : M => S.mkQ x = 0).card := hcard
    _ = Fintype.card {x : M // S.mkQ x = 0} := (Fintype.card_subtype _).symm
    _ = Nat.card {x : M // S.mkQ x = 0} := Nat.card_eq_fintype_card.symm
    _ = Nat.card S := Nat.card_congr ezero

private theorem sum_quotientMk_eq_natCard_mul
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) (f : (M ⧸ S) → Complex) :
    (∑ x : M, f (Submodule.Quotient.mk x)) =
      (Nat.card S : Complex) * ∑ q : M ⧸ S, f q := by
  classical
  change (∑ x : M, f (S.mkQ x)) = _
  rw [← Fintype.sum_fiberwise (fun x : M => S.mkQ x)]
  simp_rw [show ∀ q : M ⧸ S,
      (∑ x : {x : M // S.mkQ x = q}, f (S.mkQ x)) =
          (Nat.card S : Complex) * f q by
    intro q
    simp_rw [show ∀ x : {x : M // S.mkQ x = q},
      f (S.mkQ x) = f q from fun x => congrArg f x.2]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    rw [quotientMkFiber_natCard S q]]
  exact (Finset.mul_sum Finset.univ f (Nat.card S : Complex)).symm

private theorem sum_dite_submodule
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) [Fintype S]
    [DecidablePred fun x : M => x ∈ S] (f : S → Complex) :
    (∑ x : M, if hx : x ∈ S then f ⟨x, hx⟩ else 0) = ∑ x : S, f x := by
  classical
  let g : M → Complex := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have h := Finset.sum_subtype (p := fun x : M => x ∈ S) (F := inferInstance)
    (Finset.univ.filter fun x : M => x ∈ S) (by simp) g
  have hsub :
      ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ S), g x = ∑ x : S, f x := by
    simpa [g] using h
  have hall :
      ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ S), g x =
        ∑ x ∈ Finset.univ, g x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _hx hxnot
    have hxS : x ∉ S := by simpa using hxnot
    simp [g, hxS]
  exact hall.symm.trans hsub

/-- The unnormalized CSS quotient reconstruction has the uniform coset-size norm. -/
theorem binaryCSSLogicalBasisQuotientToCarrier_inner
    {I : Type uI} [Fintype I] [DecidableEq I]
    (xCode zCode : LinearCode (ZMod 2) I)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (phi chi : EuclideanSpace Complex
      (binaryCSSLogicalBasisQuotient xCode zCode)) :
    inner Complex (binaryCSSLogicalBasisQuotientToCarrier xCode zCode hdual phi)
        (binaryCSSLogicalBasisQuotientToCarrier xCode zCode hdual chi) =
      (Nat.card xCode.carrier : Complex) * inner Complex phi chi := by
  letI : Fintype zCode.dual.carrier := Fintype.ofFinite _
  letI : Fintype (binaryCSSLogicalBasisQuotient xCode zCode) := inferInstance
  change inner Complex
      (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode phi)
      (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode chi) = _
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  classical
  calc
    _ = ∑ w : Word (ZMod 2) I,
        (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode chi)
            ((bitstringWordEquiv I).symm w) *
          starRingEnd Complex
            ((binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode phi)
              ((bitstringWordEquiv I).symm w)) := by
      exact ((bitstringWordEquiv I).symm.sum_comp fun bits =>
        (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode chi) bits *
          starRingEnd Complex
            ((binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode phi) bits)).symm
    _ = ∑ w : Word (ZMod 2) I,
        if hw : w ∈ zCode.dual.carrier then
          chi (Submodule.Quotient.mk ⟨w, hw⟩) *
            starRingEnd Complex (phi (Submodule.Quotient.mk ⟨w, hw⟩))
        else 0 := by
      apply Fintype.sum_congr _ _
      intro w
      by_cases hw : w ∈ zCode.dual.carrier
      · have hbits :
            bitstringWordEquiv I ((bitstringWordEquiv I).symm w) ∈
              zCode.dual.carrier := by simpa using hw
        rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
          xCode zCode chi hbits,
          binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
            xCode zCode phi hbits, dif_pos hw]
        simp
      · have hbits :
            bitstringWordEquiv I ((bitstringWordEquiv I).symm w) ∉
              zCode.dual.carrier := by simpa using hw
        rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
          xCode zCode chi hbits,
          binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
            xCode zCode phi hbits, dif_neg hw]
        simp
    _ = ∑ u : zCode.dual.carrier,
        chi (Submodule.Quotient.mk u) *
          starRingEnd Complex (phi (Submodule.Quotient.mk u)) := by
      exact sum_dite_submodule (R := ZMod 2) (M := Word (ZMod 2) I)
        zCode.dual.carrier fun u =>
          chi (Submodule.Quotient.mk u) *
            starRingEnd Complex (phi (Submodule.Quotient.mk u))
    _ = (Nat.card (binaryCSSXCodeInZDual xCode zCode) : Complex) *
        ∑ q : binaryCSSLogicalBasisQuotient xCode zCode,
          chi q * starRingEnd Complex (phi q) := by
      exact sum_quotientMk_eq_natCard_mul
        (R := ZMod 2) (M := zCode.dual.carrier)
        (binaryCSSXCodeInZDual xCode zCode)
        (fun q => chi q * starRingEnd Complex (phi q))
    _ = (Nat.card xCode.carrier : Complex) *
        ∑ q : binaryCSSLogicalBasisQuotient xCode zCode,
          chi q * starRingEnd Complex (phi q) := by
      rw [Nat.card_congr (binaryCSSXCodeInZDualEquiv xCode zCode hdual).toEquiv]

universe u v w

variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]

/-- A binary row presentation partitioned by declared odd and even rows. -/
structure BinaryRowFamily (OddRow : Type u) (EvenRow : Type v) (Col : Type w) where
  oddRow : OddRow → Word (ZMod 2) Col
  evenRow : EvenRow → Word (ZMod 2) Col

namespace BinaryRowFamily

/-- The tagged complete row family, without imposing a `Fin` ordering. -/
def row (R : BinaryRowFamily OddRow EvenRow Col) :
    Sum OddRow EvenRow → Word (ZMod 2) Col
  | .inl a => R.oddRow a
  | .inr b => R.evenRow b

/-- Natural-number overlap of two binary words. -/
def pairOverlap (x y : Word (ZMod 2) Col) : Nat :=
  ∑ j, (x j * y j).val

/-- Natural-number overlap of three binary words. -/
def tripleOverlap (x y z : Word (ZMod 2) Col) : Nat :=
  ∑ j, (x j * y j * z j).val

/-- Casting an exact pair-overlap count to `F₂` gives the binary pairing. -/
theorem pairOverlap_cast (x y : Word (ZMod 2) Col) :
    (pairOverlap x y : ZMod 2) = wordPairing x y := by
  classical
  simp [pairOverlap, wordPairing_apply, dotProduct]

/-- A row's self-overlap is exactly its Hamming weight. -/
theorem pairOverlap_self_eq_hammingWeight (x : Word (ZMod 2) Col) :
    pairOverlap x x = HammingWeight x := by
  classical
  simp only [pairOverlap, HammingWeight, hammingSupport]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hx : x j = 0
  · simp [hx]
  · rw [if_pos hx]
    have hmul : x j * x j ≠ 0 := mul_ne_zero hx hx
    have hpos : 0 < (x j * x j).val :=
      Nat.pos_of_ne_zero ((ZMod.val_eq_zero (x j * x j)).not.mpr hmul)
    have hlt : (x j * x j).val < 2 := ZMod.val_lt (x j * x j)
    omega

/-- Casting an exact triple-overlap count gives its cubic `F₂` sum. -/
theorem tripleOverlap_cast (x y z : Word (ZMod 2) Col) :
    (tripleOverlap x y z : ZMod 2) = ∑ j, x j * y j * z j := by
  classical
  simp [tripleOverlap]

/--
The inspectable BH12 predicate: the declared row parities are correct and
every distinct pair and triple of tagged rows has even overlap.
-/
structure IsTriorthogonal (R : BinaryRowFamily OddRow EvenRow Col) : Prop where
  odd_weight : ∀ a, Odd (HammingWeight (R.oddRow a))
  even_weight : ∀ b, Even (HammingWeight (R.evenRow b))
  pair_even : ∀ a b : Sum OddRow EvenRow, a ≠ b →
    Even (pairOverlap (R.row a) (R.row b))
  triple_even : ∀ a b c : Sum OddRow EvenRow,
    a ≠ b → a ≠ c → b ≠ c →
      Even (tripleOverlap (R.row a) (R.row b) (R.row c))

/-- The span of the odd rows (`G₁`). -/
def oddCode (R : BinaryRowFamily OddRow EvenRow Col) : LinearCode (ZMod 2) Col where
  carrier := Submodule.span (ZMod 2) (Set.range R.oddRow)

/-- The span of the even rows (`G₀`). -/
def evenCode (R : BinaryRowFamily OddRow EvenRow Col) : LinearCode (ZMod 2) Col where
  carrier := Submodule.span (ZMod 2) (Set.range R.evenRow)

/-- The span of every tagged row (`G`). -/
def rowCode (R : BinaryRowFamily OddRow EvenRow Col) : LinearCode (ZMod 2) Col where
  carrier := Submodule.span (ZMod 2) (Set.range R.row)

@[simp] theorem oddRow_mem_oddCode (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow) :
    R.oddRow a ∈ R.oddCode.carrier :=
  Submodule.subset_span ⟨a, rfl⟩

@[simp] theorem evenRow_mem_evenCode (R : BinaryRowFamily OddRow EvenRow Col) (b : EvenRow) :
    R.evenRow b ∈ R.evenCode.carrier :=
  Submodule.subset_span ⟨b, rfl⟩

@[simp] theorem row_mem_rowCode (R : BinaryRowFamily OddRow EvenRow Col)
    (a : Sum OddRow EvenRow) : R.row a ∈ R.rowCode.carrier :=
  Submodule.subset_span ⟨a, rfl⟩

private theorem cast_even_eq_zero {n : Nat} (h : Even n) : (n : ZMod 2) = 0 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_add, ← two_mul]
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [htwo, zero_mul]

private theorem cast_odd_eq_one {n : Nat} (h : Odd n) : (n : ZMod 2) = 1 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_add, Nat.cast_mul]
  have htwo : ((2 : Nat) : ZMod 2) = 0 := ZMod.natCast_self 2
  have hone : ((1 : Nat) : ZMod 2) = 1 := Nat.cast_one
  rw [htwo, zero_mul, zero_add, hone]

/-- Odd rows have unit self-pairing. -/
@[simp] theorem oddRow_self_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a : OddRow) :
    wordPairing (R.oddRow a) (R.oddRow a) = 1 := by
  rw [← pairOverlap_cast, pairOverlap_self_eq_hammingWeight]
  exact cast_odd_eq_one (hR.odd_weight a)

/-- Even rows have zero self-pairing. -/
@[simp] theorem evenRow_self_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (b : EvenRow) :
    wordPairing (R.evenRow b) (R.evenRow b) = 0 := by
  rw [← pairOverlap_cast, pairOverlap_self_eq_hammingWeight]
  exact cast_even_eq_zero (hR.even_weight b)

/-- Distinct tagged rows have zero binary pairing. -/
theorem row_pairing_eq_zero_of_ne (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) {a b : Sum OddRow EvenRow} (hab : a ≠ b) :
    wordPairing (R.row a) (R.row b) = 0 := by
  rw [← pairOverlap_cast]
  exact cast_even_eq_zero (hR.pair_even a b hab)

/-- Odd rows form an orthonormal binary family. -/
@[simp] theorem oddRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a b : OddRow) :
    wordPairing (R.oddRow a) (R.oddRow b) = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [oddRow_self_pairing R hR]
  · rw [if_neg hab]
    exact R.row_pairing_eq_zero_of_ne hR
      (a := Sum.inl a) (b := Sum.inl b) (by simpa using hab)

/-- Every even row is orthogonal to every odd row. -/
@[simp] theorem evenRow_oddRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (b : EvenRow) (a : OddRow) :
    wordPairing (R.evenRow b) (R.oddRow a) = 0 :=
  R.row_pairing_eq_zero_of_ne hR
    (a := Sum.inr b) (b := Sum.inl a) (by simp)

/-- Every odd row is orthogonal to every even row. -/
@[simp] theorem oddRow_evenRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a : OddRow) (b : EvenRow) :
    wordPairing (R.oddRow a) (R.evenRow b) = 0 :=
  R.row_pairing_eq_zero_of_ne hR
    (a := Sum.inl a) (b := Sum.inr b) (by simp)

/-- Even rows are mutually orthogonal, including on the diagonal. -/
@[simp] theorem evenRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a b : EvenRow) :
    wordPairing (R.evenRow a) (R.evenRow b) = 0 := by
  by_cases hab : a = b
  · subst b
    exact evenRow_self_pairing R hR a
  · exact R.row_pairing_eq_zero_of_ne hR
      (a := Sum.inr a) (b := Sum.inr b) (by simpa using hab)

private theorem wordPairing_span_right
    {Index : Type*} [Fintype Index]
    (v : Index → Word (ZMod 2) Col) (x : Word (ZMod 2) Col)
    (h : ∀ i, wordPairing x (v i) = 0)
    {y : Word (ZMod 2) Col} (hy : y ∈ Submodule.span (ZMod 2) (Set.range v)) :
    wordPairing x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      exact h i
  | zero => exact (wordPairing x).map_zero
  | add y z _ _ hy hz =>
      rw [(wordPairing x).map_add, hy, hz, add_zero]
  | smul c y _ hy =>
      rw [(wordPairing x).map_smul, hy, smul_zero]

private theorem wordPairing_span_left
    {Index : Type*} [Fintype Index]
    (v : Index → Word (ZMod 2) Col) (y : Word (ZMod 2) Col)
    (h : ∀ i, wordPairing (v i) y = 0)
    {x : Word (ZMod 2) Col} (hx : x ∈ Submodule.span (ZMod 2) (Set.range v)) :
    wordPairing x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact h i
  | zero => simp
  | add x z _ _ hx hz =>
      rw [wordPairing.map_add]
      change wordPairing x y + wordPairing z y = 0
      rw [hx, hz, add_zero]
  | smul c x _ hx =>
      rw [wordPairing.map_smul]
      change c * wordPairing x y = 0
      rw [hx, mul_zero]

/-- Pairing a finite odd-row combination with one odd row recovers its coefficient. -/
theorem wordPairing_sum_oddRow (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (c : OddRow → ZMod 2) (a : OddRow) :
    wordPairing (∑ i, c i • R.oddRow i) (R.oddRow a) = c a := by
  classical
  simp [R.oddRow_pairing hR]

/-- BH12 Lemma 1(i): the odd rows are linearly independent. -/
theorem oddRows_linearIndependent (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) : LinearIndependent (ZMod 2) R.oddRow := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hp := congrArg (fun x => wordPairing x (R.oddRow a)) hc
  have hp' : wordPairing (∑ i, c i • R.oddRow i) (R.oddRow a) = 0 := by
    simpa using hp
  rw [R.wordPairing_sum_oddRow hR c a] at hp'
  exact hp'

/-- A word in the odd span is zero when all its odd-row pairings vanish. -/
theorem eq_zero_of_mem_oddCode_of_pairing_eq_zero
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.oddCode.carrier)
    (hpair : ∀ a, wordPairing x (R.oddRow a) = 0) : x = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hx
  have hc0 : ∀ a, c a = 0 := by
    intro a
    rw [← R.wordPairing_sum_oddRow hR c a, hc]
    exact hpair a
  calc
    x = ∑ a, c a • R.oddRow a := hc.symm
    _ = 0 := by simp [hc0]

/-- The even span is orthogonal to the odd span. -/
theorem wordPairing_evenCode_oddCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x y : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    (hy : y ∈ R.oddCode.carrier) : wordPairing x y = 0 := by
  apply wordPairing_span_left R.evenRow y (fun b => ?_) hx
  exact wordPairing_span_right R.oddRow (R.evenRow b)
    (fun a => R.evenRow_oddRow_pairing hR b a) hy

/-- The even span is orthogonal to the entire row span. -/
theorem wordPairing_evenCode_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x y : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    (hy : y ∈ R.rowCode.carrier) : wordPairing x y = 0 := by
  apply wordPairing_span_left R.evenRow y (fun b => ?_) hx
  apply wordPairing_span_right R.row (R.evenRow b) (fun a => ?_) hy
  rcases a with a | a
  · exact R.evenRow_oddRow_pairing hR b a
  · exact R.evenRow_pairing hR b a

/-- The total row span is exactly `G₀ + G₁`. -/
theorem rowCode_eq_evenCode_sup_oddCode (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.carrier = R.evenCode.carrier ⊔ R.oddCode.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨a, rfl⟩
    rcases a with a | b
    · exact Submodule.mem_sup_right (R.oddRow_mem_oddCode a)
    · exact Submodule.mem_sup_left (R.evenRow_mem_evenCode b)
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨b, rfl⟩
      exact R.row_mem_rowCode (.inr b)
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact R.row_mem_rowCode (.inl a)

/-- BH12 Lemma 1(ii): `G₀ ∩ G₁ = 0`. -/
theorem evenCode_inf_oddCode_eq_bot
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.carrier ⊓ R.oddCode.carrier = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxEven : x ∈ R.evenCode.carrier := hx.1
  have hxOdd : x ∈ R.oddCode.carrier := hx.2
  have hzero := R.eq_zero_of_mem_oddCode_of_pairing_eq_zero hR hxOdd (fun a =>
    R.wordPairing_evenCode_oddCode hR hxEven (R.oddRow_mem_oddCode a))
  simpa [hzero]

/-- Directness form of `G₀ ∩ G₁ = 0`. -/
theorem evenCode_disjoint_oddCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Disjoint R.evenCode.carrier R.oddCode.carrier := by
  rw [disjoint_iff]
  exact R.evenCode_inf_oddCode_eq_bot hR

/-- `G₀` is contained in `G⊥`. -/
theorem evenCode_le_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.carrier ≤ R.rowCode.dual.carrier := by
  intro x hx
  rw [LinearCode.mem_dual]
  intro y hy
  exact R.wordPairing_evenCode_rowCode hR hx hy

/-- BH12 Lemma 1(iii): `G₀ = G ∩ G⊥`. -/
theorem evenCode_eq_rowCode_inf_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.carrier = R.rowCode.carrier ⊓ R.rowCode.dual.carrier := by
  apply le_antisymm
  · intro x hx
    constructor
    · rw [R.rowCode_eq_evenCode_sup_oddCode]
      exact Submodule.mem_sup_left hx
    · exact R.evenCode_le_rowCode_dual hR hx
  · intro x hx
    have hxRow : x ∈ R.rowCode.carrier := hx.1
    have hxDual : x ∈ R.rowCode.dual.carrier := hx.2
    rw [R.rowCode_eq_evenCode_sup_oddCode] at hxRow
    rcases Submodule.mem_sup.mp hxRow with ⟨e, he, o, ho, rfl⟩
    have hopair : ∀ a, wordPairing o (R.oddRow a) = 0 := by
      intro a
      have htotal := R.rowCode.orthogonal_of_mem_dual hxDual (R.row_mem_rowCode (.inl a))
      have heo := R.wordPairing_evenCode_oddCode hR he (R.oddRow_mem_oddCode a)
      change wordPairing (e + o) (R.oddRow a) = 0 at htotal
      rw [wordPairing.map_add] at htotal
      change wordPairing e (R.oddRow a) + wordPairing o (R.oddRow a) = 0 at htotal
      rw [heo, zero_add] at htotal
      exact htotal
    have ho0 := R.eq_zero_of_mem_oddCode_of_pairing_eq_zero hR ho hopair
    simpa [ho0] using he

/-- The odd span meets `G⊥` only at zero. -/
theorem oddCode_inf_rowCode_dual_eq_bot
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.oddCode.carrier ⊓ R.rowCode.dual.carrier = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hzero := R.eq_zero_of_mem_oddCode_of_pairing_eq_zero hR hx.1 (fun a =>
    R.rowCode.orthogonal_of_mem_dual hx.2 (R.row_mem_rowCode (.inl a)))
  simpa [hzero]

/-- Directness form of `G₁ ∩ G⊥ = 0`. -/
theorem oddCode_disjoint_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Disjoint R.oddCode.carrier R.rowCode.dual.carrier := by
  rw [disjoint_iff]
  exact R.oddCode_inf_rowCode_dual_eq_bot hR

/-- Every odd-span word is in `G₀⊥`. -/
theorem oddCode_le_evenCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.oddCode.carrier ≤ R.evenCode.dual.carrier := by
  intro x hx
  rw [LinearCode.mem_dual]
  intro e he
  rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
  exact R.wordPairing_evenCode_oddCode hR he hx

/-- `G⊥` is contained in `G₀⊥`. -/
theorem rowCode_dual_le_evenCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.dual.carrier ≤ R.evenCode.dual.carrier := by
  intro x hx
  rw [LinearCode.mem_dual]
  intro e he
  exact R.rowCode.orthogonal_of_mem_dual hx (by
    rw [R.rowCode_eq_evenCode_sup_oddCode]
    exact Submodule.mem_sup_left he)

/-- The explicit odd-row pairing projection of an ambient binary word. -/
def oddProjection (R : BinaryRowFamily OddRow EvenRow Col)
    (x : Word (ZMod 2) Col) : Word (ZMod 2) Col :=
  ∑ a, wordPairing x (R.oddRow a) • R.oddRow a

theorem oddProjection_mem_oddCode (R : BinaryRowFamily OddRow EvenRow Col)
    (x : Word (ZMod 2) Col) : R.oddProjection x ∈ R.oddCode.carrier := by
  classical
  exact Submodule.sum_mem R.oddCode.carrier (fun a _ =>
    R.oddCode.carrier.smul_mem _ (R.oddRow_mem_oddCode a))

@[simp] theorem oddProjection_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (x : Word (ZMod 2) Col) (a : OddRow) :
    wordPairing (R.oddProjection x) (R.oddRow a) =
      wordPairing x (R.oddRow a) := by
  classical
  exact R.wordPairing_sum_oddRow hR (fun b => wordPairing x (R.oddRow b)) a

/-- Subtracting the odd projection of a `G₀⊥` word leaves a word in `G⊥`. -/
theorem sub_oddProjection_mem_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.dual.carrier) :
    x - R.oddProjection x ∈ R.rowCode.dual.carrier := by
  rw [LinearCode.mem_dual]
  intro y hy
  apply wordPairing_span_right R.row (x - R.oddProjection x) (fun a => ?_) hy
  rcases a with a | b
  · change wordPairing (x - R.oddProjection x) (R.oddRow a) = 0
    rw [sub_eq_add_neg, ZModModule.neg_eq_self, wordPairing.map_add]
    change wordPairing x (R.oddRow a) +
      wordPairing (R.oddProjection x) (R.oddRow a) = 0
    rw [R.oddProjection_pairing hR]
    exact ZModModule.add_self _
  · have hxEven := R.evenCode.orthogonal_of_mem_dual hx (R.evenRow_mem_evenCode b)
    have hpEven := R.wordPairing_evenCode_oddCode hR (R.evenRow_mem_evenCode b)
      (R.oddProjection_mem_oddCode x)
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply] at hpEven
    change wordPairing (x - R.oddProjection x) (R.evenRow b) = 0
    rw [sub_eq_add_neg, ZModModule.neg_eq_self, wordPairing.map_add]
    change wordPairing x (R.evenRow b) +
      wordPairing (R.oddProjection x) (R.evenRow b) = 0
    rw [hxEven, hpEven, add_zero]

/-- BH12 Lemma 1(iv): `G₀⊥ = G₁ + G⊥`. -/
theorem evenCode_dual_eq_oddCode_sup_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.dual.carrier = R.oddCode.carrier ⊔ R.rowCode.dual.carrier := by
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_sup.mpr ⟨R.oddProjection x, R.oddProjection_mem_oddCode x,
      x - R.oddProjection x, R.sub_oddProjection_mem_rowCode_dual hR hx, ?_⟩
    abel
  · exact sup_le (R.oddCode_le_evenCode_dual hR) R.rowCode_dual_le_evenCode_dual

/-- Dimension of the odd span is the number of declared odd rows. -/
theorem dimension_oddCode (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) : Dimension R.oddCode = Fintype.card OddRow := by
  change Module.finrank (ZMod 2) R.oddCode.carrier = _
  exact finrank_span_eq_card (R.oddRows_linearIndependent hR)

/-- The BH12 `Z`-check code `G⊥` lies in the dual of the `X`-check code `G₀`. -/
theorem cssDualContainment (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.dual.carrier ≤ R.evenCode.dual.carrier :=
  R.rowCode_dual_le_evenCode_dual

/-- The concrete semantic CSS code with `X` checks `G₀` and `Z` checks `G⊥`. -/
noncomputable def cssQuantumCode (R : BinaryRowFamily OddRow EvenRow Col) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister Col) :=
  PauliSymplectic.binaryCSSQuantumCodeOfDualLe
    R.evenCode R.rowCode.dual R.cssDualContainment

/-- The CSS logical exponent is exactly the number of declared odd rows. -/
theorem cssLogicalExponent_eq_card_oddRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Length (ZMod 2) Col - Dimension R.evenCode - Dimension R.rowCode.dual =
      Fintype.card OddRow := by
  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq
    R.oddCode.carrier R.rowCode.dual.carrier
  rw [(R.oddCode_disjoint_rowCode_dual hR).eq_bot, finrank_bot, add_zero] at hGrass
  have hSplit :
      Dimension R.evenCode.dual =
        Dimension R.oddCode + Dimension R.rowCode.dual := by
    rw [Dimension_eq_finrank_carrier, R.evenCode_dual_eq_oddCode_sup_rowCode_dual hR]
    exact hGrass
  rw [← R.evenCode.dual_dimension_eq_length_sub_dimension,
    hSplit, R.dimension_oddCode hR]
  omega

/-- The semantic CSS carrier has dimension `2^k`, where `k` is the odd-row count. -/
theorem cssQuantumCode_finrank_carrier
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Module.finrank Complex R.cssQuantumCode.carrier = 2 ^ Fintype.card OddRow := by
  rw [cssQuantumCode,
    PauliSymplectic.binaryCSSQuantumCodeOfDualLe_finrank_carrier,
    R.cssLogicalExponent_eq_card_oddRows hR]

/-- The inverse square-root normalization for a uniform `G₀` coset sum. -/
noncomputable def cssNormalizationScalar
    (R : BinaryRowFamily OddRow EvenRow Col) : Complex :=
  (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex)⁻¹

private theorem cssNormalizationScalar_identity
    (R : BinaryRowFamily OddRow EvenRow Col) :
    starRingEnd Complex R.cssNormalizationScalar * R.cssNormalizationScalar *
        (Nat.card R.evenCode.carrier : Complex) = 1 := by
  have hcard : 0 < Nat.card R.evenCode.carrier := Nat.card_pos
  have hsqrtPos :
      0 < Real.sqrt (Nat.card R.evenCode.carrier : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) *
          (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) =
        (Nat.card R.evenCode.carrier : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Nat.card R.evenCode.carrier)
  simp only [cssNormalizationScalar, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) =
        (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]

/-- The explicitly normalized quotient-amplitude reconstruction map. -/
noncomputable def normalizedLogicalQuotientToCarrierLinearMap
    (R : BinaryRowFamily OddRow EvenRow Col) :
    EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) →ₗ[Complex] R.cssQuantumCode.carrier :=
  R.cssNormalizationScalar •
    PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
      R.evenCode R.rowCode.dual R.cssDualContainment

@[simp] theorem normalizedLogicalQuotientToCarrierLinearMap_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (phi : EuclideanSpace Complex
      (PauliSymplectic.binaryCSSLogicalBasisQuotient
        R.evenCode R.rowCode.dual)) :
    R.normalizedLogicalQuotientToCarrierLinearMap phi =
      R.cssNormalizationScalar •
        PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
          R.evenCode R.rowCode.dual R.cssDualContainment phi :=
  rfl

theorem normalizedLogicalQuotientToCarrierLinearMap_inner
    (R : BinaryRowFamily OddRow EvenRow Col)
    (phi chi : EuclideanSpace Complex
      (PauliSymplectic.binaryCSSLogicalBasisQuotient
        R.evenCode R.rowCode.dual)) :
    inner Complex (R.normalizedLogicalQuotientToCarrierLinearMap phi)
        (R.normalizedLogicalQuotientToCarrierLinearMap chi) =
      inner Complex phi chi := by
  rw [normalizedLogicalQuotientToCarrierLinearMap_apply,
    normalizedLogicalQuotientToCarrierLinearMap_apply]
  calc
    inner Complex
          (R.cssNormalizationScalar •
            PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
              R.evenCode R.rowCode.dual R.cssDualContainment phi)
          (R.cssNormalizationScalar •
            PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
              R.evenCode R.rowCode.dual R.cssDualContainment chi) =
        starRingEnd Complex R.cssNormalizationScalar *
          inner Complex
            (PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
              R.evenCode R.rowCode.dual R.cssDualContainment phi)
            (R.cssNormalizationScalar •
              PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
                R.evenCode R.rowCode.dual R.cssDualContainment chi) :=
      inner_smul_left _ _ _
    _ = starRingEnd Complex R.cssNormalizationScalar *
          (R.cssNormalizationScalar *
            inner Complex
              (PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
                R.evenCode R.rowCode.dual R.cssDualContainment phi)
              (PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
                R.evenCode R.rowCode.dual R.cssDualContainment chi)) := by
      rw [inner_smul_right]
    _ = starRingEnd Complex R.cssNormalizationScalar *
          (R.cssNormalizationScalar *
            ((Nat.card R.evenCode.carrier : Complex) * inner Complex phi chi)) := by
      rw [binaryCSSLogicalBasisQuotientToCarrier_inner]
    _ = (starRingEnd Complex R.cssNormalizationScalar * R.cssNormalizationScalar *
          (Nat.card R.evenCode.carrier : Complex)) * inner Complex phi chi := by ring
    _ = inner Complex phi chi := by rw [R.cssNormalizationScalar_identity, one_mul]

/-- The normalized reconstruction as a linear isometry. -/
noncomputable def normalizedLogicalQuotientToCarrierLinearIsometry
    (R : BinaryRowFamily OddRow EvenRow Col) :
    EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) →ₗᵢ[Complex] R.cssQuantumCode.carrier :=
  R.normalizedLogicalQuotientToCarrierLinearMap.isometryOfInner
    R.normalizedLogicalQuotientToCarrierLinearMap_inner

/-- The normalized quotient-amplitude reconstruction is onto the actual CSS carrier. -/
noncomputable def normalizedLogicalQuotientToCarrier
    (R : BinaryRowFamily OddRow EvenRow Col) :
    EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) ≃ₗᵢ[Complex] R.cssQuantumCode.carrier := by
  let L := R.normalizedLogicalQuotientToCarrierLinearIsometry
  have hdim :
      Module.finrank Complex
          (EuclideanSpace Complex
            (PauliSymplectic.binaryCSSLogicalBasisQuotient
              R.evenCode R.rowCode.dual)) =
        Module.finrank Complex R.cssQuantumCode.carrier := by
    exact (PauliSymplectic.binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
      R.evenCode R.rowCode.dual R.cssDualContainment).finrank_eq.symm
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp L.injective
  exact LinearIsometryEquiv.ofSurjective L hsurj

@[simp] theorem normalizedLogicalQuotientToCarrier_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (phi : EuclideanSpace Complex
      (PauliSymplectic.binaryCSSLogicalBasisQuotient
        R.evenCode R.rowCode.dual)) :
    R.normalizedLogicalQuotientToCarrier phi =
      R.normalizedLogicalQuotientToCarrierLinearMap phi :=
  rfl

/-- The linear combination of odd rows with coefficients indexed by `OddRow`. -/
def oddCombination (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) OddRow →ₗ[ZMod 2] Word (ZMod 2) Col :=
  Fintype.linearCombination (ZMod 2) R.oddRow

@[simp] theorem oddCombination_apply
    (R : BinaryRowFamily OddRow EvenRow Col) (c : Word (ZMod 2) OddRow) :
    R.oddCombination c = ∑ a, c a • R.oddRow a := by
  exact Fintype.linearCombination_apply (ZMod 2) R.oddRow c

theorem oddCombination_mem_oddCode
    (R : BinaryRowFamily OddRow EvenRow Col) (c : Word (ZMod 2) OddRow) :
    R.oddCombination c ∈ R.oddCode.carrier := by
  rw [oddCombination_apply]
  exact Submodule.sum_mem R.oddCode.carrier (fun a _ =>
    R.oddCode.carrier.smul_mem _ (R.oddRow_mem_oddCode a))

theorem oddCombination_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (c : Word (ZMod 2) OddRow) :
    R.oddCombination c ∈ R.rowCode.carrier := by
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.mem_sup_right (R.oddCombination_mem_oddCode c)

/-- Odd-row combinations viewed in the logical ambient space `(G⊥)⊥`. -/
def oddCombinationInRowDoubleDual (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) OddRow →ₗ[ZMod 2] R.rowCode.dual.dual.carrier :=
  R.oddCombination.codRestrict R.rowCode.dual.dual.carrier fun c => by
    rw [LinearCode.mem_dual]
    intro y hy
    exact R.rowCode.dual_orthogonal (R.oddCombination_mem_rowCode c) hy

/-- The odd-row coefficient word mapped to its CSS logical coset. -/
noncomputable def oddWordToLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) OddRow →ₗ[ZMod 2]
      PauliSymplectic.binaryCSSLogicalBasisQuotient R.evenCode R.rowCode.dual :=
  (PauliSymplectic.binaryCSSXCodeInZDual R.evenCode R.rowCode.dual).mkQ.comp
    R.oddCombinationInRowDoubleDual

theorem oddWordToLogicalQuotient_injective
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Function.Injective R.oddWordToLogicalQuotient := by
  refine (injective_iff_map_eq_zero R.oddWordToLogicalQuotient).mpr ?_
  intro c hc
  have hmem :
      R.oddCombinationInRowDoubleDual c ∈
        PauliSymplectic.binaryCSSXCodeInZDual R.evenCode R.rowCode.dual := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hc
  have heven : R.oddCombination c ∈ R.evenCode.carrier := by
    exact hmem
  have hinter :
      R.oddCombination c ∈ R.evenCode.carrier ⊓ R.oddCode.carrier :=
    ⟨heven, R.oddCombination_mem_oddCode c⟩
  have hcomb : R.oddCombination c = 0 := by
    rw [R.evenCode_inf_oddCode_eq_bot hR] at hinter
    simpa using hinter
  apply funext
  intro a
  exact (Fintype.linearIndependent_iff.mp (R.oddRows_linearIndependent hR))
    c (by simpa using hcomb) a

theorem finrank_logicalQuotient_eq_card_oddRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Module.finrank (ZMod 2)
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) = Fintype.card OddRow := by
  rw [PauliSymplectic.finrank_binaryCSSLogicalBasisQuotient_eq
    R.evenCode R.rowCode.dual R.cssDualContainment,
    R.cssLogicalExponent_eq_card_oddRows hR]

/-- Odd-row coefficient words are exactly the logical CSS quotient classes. -/
noncomputable def oddWordLinearEquivLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Word (ZMod 2) OddRow ≃ₗ[ZMod 2]
      PauliSymplectic.binaryCSSLogicalBasisQuotient R.evenCode R.rowCode.dual :=
  R.oddWordToLogicalQuotient.linearEquivOfInjective
    (R.oddWordToLogicalQuotient_injective hR) (by
      rw [finrank_word_eq_length, Length,
        R.finrank_logicalQuotient_eq_card_oddRows hR])

@[simp] theorem oddWordLinearEquivLogicalQuotient_apply
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) OddRow) :
    R.oddWordLinearEquivLogicalQuotient hR c =
      R.oddWordToLogicalQuotient c :=
  rfl

/-- Computational labels on the odd-row qubits are the CSS logical quotient labels. -/
noncomputable def logicalBasisEquivLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Qubit.Bitstring OddRow ≃
      PauliSymplectic.binaryCSSLogicalBasisQuotient R.evenCode R.rowCode.dual :=
  (PauliSymplectic.bitstringWordEquiv OddRow).trans
    (R.oddWordLinearEquivLogicalQuotient hR).toEquiv

/-- Reindex logical computational amplitudes by their CSS quotient classes. -/
noncomputable def logicalBasisReindex
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Qubit.QubitRegister OddRow ≃ₗᵢ[Complex]
      EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (R.logicalBasisEquivLogicalQuotient hR)

/-- The concrete normalized encoding of the odd-row logical register. -/
noncomputable def encoding
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Qubit.QubitRegister OddRow ≃ₗᵢ[Complex] R.cssQuantumCode.carrier :=
  (R.logicalBasisReindex hR).trans R.normalizedLogicalQuotientToCarrier

/-- Exact computational-basis amplitudes of the normalized CSS encoding on `G⊥⊥`. -/
theorem encoding_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encoding hR psi : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar *
        psi ((R.logicalBasisEquivLogicalQuotient hR).symm
          (Submodule.Quotient.mk
            ⟨bitstringWordEquiv Col bits, hbits⟩)) := by
  change R.cssNormalizationScalar *
      PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister
        R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) bits = _
  rw [PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) hbits]
  rfl

/-- Exact computational-basis amplitudes of the normalized CSS encoding off `G⊥⊥`. -/
theorem encoding_apply_of_not_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∉ R.rowCode.dual.dual.carrier) :
    (R.encoding hR psi : Qubit.QubitRegister Col) bits = 0 := by
  change R.cssNormalizationScalar *
      PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister
        R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) bits = 0
  rw [PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
    R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) hbits]
  simp

/-- The BH12 triorthogonal CSS code as an actual `k`-qubit `EncodedCode`. -/
noncomputable def encodedCode
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    EncodedCode (Qubit.QubitRegister LogicalRow)
      (Qubit.QubitRegister PhysicalCol) where
  code := R.cssQuantumCode
  encoding := R.encoding hR

@[simp] theorem encodedCode_code
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    (R.encodedCode hR).code = R.cssQuantumCode :=
  rfl

@[simp] theorem encodedCode_encoding
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    (R.encodedCode hR).encoding = R.encoding hR :=
  rfl

/-- The source-stated physical representative of logical `X` on odd row `a`. -/
def logicalXPauli (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow) :
    PauliSymplectic.Binary Col :=
  PauliSymplectic.cssXCheck (R.oddRow a)

/-- The source-stated physical representative of logical `Z` on odd row `a`. -/
def logicalZPauli (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow) :
    PauliSymplectic.Binary Col :=
  PauliSymplectic.cssZCheck (R.oddRow a)

/-- Logical `X_a` commutes with every `X`-type stabilizer. -/
theorem logicalXPauli_commutes_cssXCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    (x : Word (ZMod 2) Col) :
    PauliSymplectic.Commutes (R.logicalXPauli a)
      (PauliSymplectic.cssXCheck x) :=
  PauliSymplectic.cssXCheck_commutes_cssXCheck _ _

/-- Logical `X_a` commutes with every `Z`-type stabilizer. -/
theorem logicalXPauli_commutes_cssZCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    {z : Word (ZMod 2) Col} (hz : z ∈ R.rowCode.dual.carrier) :
    PauliSymplectic.Commutes (R.logicalXPauli a)
      (PauliSymplectic.cssZCheck z) :=
  PauliSymplectic.cssXCheck_commutes_cssZCheck_of_mem_dual R.rowCode
    (R.row_mem_rowCode (.inl a)) hz

/-- Logical `Z_a` commutes with every `Z`-type stabilizer. -/
theorem logicalZPauli_commutes_cssZCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow)
    (z : Word (ZMod 2) Col) :
    PauliSymplectic.Commutes (R.logicalZPauli a)
      (PauliSymplectic.cssZCheck z) :=
  PauliSymplectic.cssZCheck_commutes_cssZCheck _ _

/-- Logical `Z_a` commutes with every `X`-type stabilizer. -/
theorem logicalZPauli_commutes_cssXCheck
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a : OddRow) {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier) :
    PauliSymplectic.Commutes (R.logicalZPauli a)
      (PauliSymplectic.cssXCheck x) :=
  PauliSymplectic.cssZCheck_commutes_cssXCheck_of_mem_dual R.evenCode hx
    (R.oddCode_le_evenCode_dual hR (R.oddRow_mem_oddCode a))

/-- The chosen logical Pauli representatives commute exactly off the diagonal. -/
theorem logicalXPauli_commutes_logicalZPauli_iff
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a b : OddRow) :
    PauliSymplectic.Commutes (R.logicalXPauli a) (R.logicalZPauli b) ↔ a ≠ b := by
  classical
  simp only [logicalXPauli, logicalZPauli, PauliSymplectic.Commutes,
    symplecticForm_x_zero_zero_z_eq_wordPairing, R.oddRow_pairing hR]
  by_cases hab : a = b <;> simp [hab]

/-- Concrete logical Pauli operators obey `X_a Z_b = (-1)^(δ_ab) Z_b X_a`. -/
theorem logicalPauli_operator_relation
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a b : OddRow) :
    PauliSymplectic.toQubitOperator (R.logicalXPauli a) *
        PauliSymplectic.toQubitOperator (R.logicalZPauli b) =
      if a = b then
        -(PauliSymplectic.toQubitOperator (R.logicalZPauli b) *
          PauliSymplectic.toQubitOperator (R.logicalXPauli a))
      else
        PauliSymplectic.toQubitOperator (R.logicalZPauli b) *
          PauliSymplectic.toQubitOperator (R.logicalXPauli a) := by
  classical
  by_cases hab : a = b
  · rw [if_pos hab]
    exact PauliSymplectic.toQubitOperator_anticommute_of_not_commutes _ _
      (by
        intro hcomm
        exact (R.logicalXPauli_commutes_logicalZPauli_iff hR a b).1 hcomm hab)
  · rw [if_neg hab]
    exact PauliSymplectic.toQubitOperator_commute_of_commutes _ _
      ((R.logicalXPauli_commutes_logicalZPauli_iff hR a b).2 hab)

/-- A logical computational-basis state on the odd-row register. -/
noncomputable def logicalComputationalState (label : Qubit.Bitstring OddRow) :
    Qubit.QubitRegister OddRow :=
  EuclideanSpace.basisFun (Qubit.Bitstring OddRow) Complex label

@[simp] theorem logicalComputationalState_apply
    (label bits : Qubit.Bitstring OddRow) :
    logicalComputationalState label bits = if label = bits then 1 else 0 := by
  classical
  simp [logicalComputationalState, EuclideanSpace.basisFun_apply, PiLp.single_apply,
    eq_comm]

/-- The normalized encoded computational state indexed by an odd-row bitstring. -/
noncomputable def encodedComputationalState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) : R.cssQuantumCode.carrier :=
  R.encoding hR (logicalComputationalState label)

/-- A computational codeword has the uniform coset amplitude on its logical class. -/
theorem encodedComputationalState_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedComputationalState hR label : Qubit.QubitRegister Col) bits =
      if label = (R.logicalBasisEquivLogicalQuotient hR).symm
          (Submodule.Quotient.mk ⟨bitstringWordEquiv Col bits, hbits⟩) then
        R.cssNormalizationScalar
      else
        0 := by
  rw [encodedComputationalState, R.encoding_apply_of_mem hR _ hbits]
  simp [logicalComputationalState_apply]
  rfl

/-- A computational codeword has zero amplitude off the CSS logical ambient space. -/
theorem encodedComputationalState_apply_of_not_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∉ R.rowCode.dual.dual.carrier) :
    (R.encodedComputationalState hR label : Qubit.QubitRegister Col) bits = 0 := by
  exact R.encoding_apply_of_not_mem hR (logicalComputationalState label) hbits

/-- Encoded computational states are an orthonormal basis of the CSS carrier. -/
theorem encodedComputationalState_inner
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (x y : Qubit.Bitstring OddRow) :
    inner Complex (R.encodedComputationalState hR x)
        (R.encodedComputationalState hR y) = if x = y then 1 else 0 := by
  rw [encodedComputationalState, encodedComputationalState,
    (R.encoding hR).inner_map_map]
  simp only [logicalComputationalState, EuclideanSpace.basisFun_apply]
  rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]

/-- The common normalized amplitude of a logical equal superposition. -/
noncomputable def logicalUniformScalar (Index : Type u) [Fintype Index] : Complex :=
  (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex)⁻¹

/-- The logical `|+⟩^⊗k` state on the odd-row register. -/
noncomputable def logicalPlusState (Index : Type u) [Fintype Index] :
    Qubit.QubitRegister Index :=
  WithLp.toLp 2 fun _ => logicalUniformScalar Index

@[simp] theorem logicalPlusState_apply
    (Index : Type u) [Fintype Index] (bits : Qubit.Bitstring Index) :
    logicalPlusState Index bits = logicalUniformScalar Index :=
  rfl

/-- The encoded logical `|+⟩^⊗k` state. -/
noncomputable def encodedPlusState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.cssQuantumCode.carrier :=
  R.encoding hR (logicalPlusState OddRow)

theorem encodedPlusState_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedPlusState hR : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar * logicalUniformScalar OddRow := by
  rw [encodedPlusState, R.encoding_apply_of_mem hR _ hbits]
  rfl

theorem encodedPlusState_apply_of_not_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∉ R.rowCode.dual.dual.carrier) :
    (R.encodedPlusState hR : Qubit.QubitRegister Col) bits = 0 := by
  exact R.encoding_apply_of_not_mem hR (logicalPlusState OddRow) hbits

/-- The primitive phase `exp(i π / 4)` used by the logical magic state. -/
noncomputable def piDivFourPhase : Complex :=
  OneQubitMagic.phaseAmplitude (Real.pi / 4)

/-- The logical `|A⟩^⊗k` state, with phase determined by Hamming weight. -/
noncomputable def logicalMagicState (Index : Type u) [Fintype Index] :
    Qubit.QubitRegister Index :=
  WithLp.toLp 2 fun bits =>
    logicalUniformScalar Index *
      piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits)

@[simp] theorem logicalMagicState_apply
    (Index : Type u) [Fintype Index] (bits : Qubit.Bitstring Index) :
    logicalMagicState Index bits =
      logicalUniformScalar Index *
        piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits) :=
  rfl

/-- The encoded logical `|A⟩^⊗k` magic state. -/
noncomputable def encodedMagicState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.cssQuantumCode.carrier :=
  R.encoding hR (logicalMagicState OddRow)

theorem encodedMagicState_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedMagicState hR : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar *
        (logicalUniformScalar OddRow *
          piDivFourPhase ^ HammingWeight
            (bitstringWordEquiv OddRow
              ((R.logicalBasisEquivLogicalQuotient hR).symm
                (Submodule.Quotient.mk
                  ⟨bitstringWordEquiv Col bits, hbits⟩)))) := by
  rw [encodedMagicState, R.encoding_apply_of_mem hR _ hbits]
  rfl

theorem encodedMagicState_apply_of_not_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∉ R.rowCode.dual.dual.carrier) :
    (R.encodedMagicState hR : Qubit.QubitRegister Col) bits = 0 := by
  exact R.encoding_apply_of_not_mem hR (logicalMagicState OddRow) hbits

/- Use the canonical finite-function-space instance in the normalization tail. -/
attribute [-instance] Fintype.ofFinite

private theorem logicalUniformScalar_identity
    (Index : Type u) [Fintype Index] :
    starRingEnd Complex (logicalUniformScalar Index) *
        logicalUniformScalar Index *
        (Nat.card (Qubit.Bitstring Index) : Complex) = 1 := by
  have hcard : 0 < Nat.card (Qubit.Bitstring Index) := Nat.card_pos
  have hsqrtPos :
      0 < Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) *
          (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) =
        (Nat.card (Qubit.Bitstring Index) : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Nat.card (Qubit.Bitstring Index))
  simp only [logicalUniformScalar, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) =
        (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]

/-- The declared logical equal superposition has unit norm. -/
theorem logicalPlusState_inner_self
    (Index : Type u) [Fintype Index] [DecidableEq Index] :
    @inner Complex (Qubit.QubitRegister Index)
        (PiLp.innerProductSpace fun _ : Qubit.Bitstring Index => Complex).toInner
        (logicalPlusState Index) (logicalPlusState Index) = 1 := by
  rw [PiLp.inner_apply]
  simp only [logicalPlusState_apply, RCLike.inner_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show Finset.univ.card = Nat.card (Qubit.Bitstring Index) by
    exact Nat.card_eq_fintype_card.symm]
  change (Nat.card (Qubit.Bitstring Index) : Complex) *
      (logicalUniformScalar Index *
        starRingEnd Complex (logicalUniformScalar Index)) = 1
  have h := logicalUniformScalar_identity Index
  calc
    (Nat.card (Qubit.Bitstring Index) : Complex) *
        (logicalUniformScalar Index *
          starRingEnd Complex (logicalUniformScalar Index)) =
      starRingEnd Complex (logicalUniformScalar Index) *
        logicalUniformScalar Index *
          (Nat.card (Qubit.Bitstring Index) : Complex) := by ring
    _ = 1 := h

private theorem piDivFourPhase_pow_mul_star (n : Nat) :
    piDivFourPhase ^ n * starRingEnd Complex (piDivFourPhase ^ n) = 1 := by
  rw [map_pow, ← mul_pow]
  rw [show piDivFourPhase * starRingEnd Complex piDivFourPhase = 1 by
    simpa [piDivFourPhase] using
      OneQubitMagic.phaseAmplitude_mul_conj (Real.pi / 4)]
  simp

/-- The declared logical magic state has unit norm. -/
theorem logicalMagicState_inner_self
    (Index : Type u) [Fintype Index] [DecidableEq Index] :
    @inner Complex (Qubit.QubitRegister Index)
        (PiLp.innerProductSpace fun _ : Qubit.Bitstring Index => Complex).toInner
        (logicalMagicState Index) (logicalMagicState Index) = 1 := by
  rw [PiLp.inner_apply]
  simp only [logicalMagicState_apply, RCLike.inner_apply, map_mul]
  calc
    ∑ bits, (logicalUniformScalar Index *
          piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits)) *
        (starRingEnd Complex (logicalUniformScalar Index) *
          starRingEnd Complex
            (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits))) =
      ∑ _bits : Qubit.Bitstring Index,
        logicalUniformScalar Index *
          starRingEnd Complex (logicalUniformScalar Index) := by
        apply Finset.sum_congr rfl
        intro bits _hbits
        rw [show
          (logicalUniformScalar Index *
              piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits)) *
            (starRingEnd Complex (logicalUniformScalar Index) *
              starRingEnd Complex
                (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits))) =
            (logicalUniformScalar Index *
              starRingEnd Complex (logicalUniformScalar Index)) *
            (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits) *
              starRingEnd Complex
                (piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits))) by ring]
        rw [piDivFourPhase_pow_mul_star]
        simp
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [show Finset.univ.card = Nat.card (Qubit.Bitstring Index) by
        exact Nat.card_eq_fintype_card.symm]
      change (Nat.card (Qubit.Bitstring Index) : Complex) *
          (logicalUniformScalar Index *
            starRingEnd Complex (logicalUniformScalar Index)) = 1
      have h := logicalUniformScalar_identity Index
      calc
        (Nat.card (Qubit.Bitstring Index) : Complex) *
            (logicalUniformScalar Index *
              starRingEnd Complex (logicalUniformScalar Index)) =
          starRingEnd Complex (logicalUniformScalar Index) *
            logicalUniformScalar Index *
              (Nat.card (Qubit.Bitstring Index) : Complex) := by ring
        _ = 1 := h

/-- The encoded logical equal superposition is explicitly normalized. -/
theorem encodedPlusState_inner_self
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    inner Complex (R.encodedPlusState hR) (R.encodedPlusState hR) = 1 := by
  rw [encodedPlusState, (R.encoding hR).inner_map_map]
  exact logicalPlusState_inner_self OddRow

/-- The encoded logical magic state is explicitly normalized. -/
theorem encodedMagicState_inner_self
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    inner Complex (R.encodedMagicState hR) (R.encodedMagicState hR) = 1 := by
  rw [encodedMagicState, (R.encoding hR).inner_map_map]
  exact logicalMagicState_inner_self OddRow

end BinaryRowFamily

end Triorthogonal
end Distillation
end QEC
