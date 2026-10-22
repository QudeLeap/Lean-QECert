import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.PairedDecoderChannel
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDimension
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.BoundedRateDavies
import QEC.Coding.Core.Duality

/-!
# Actual logical defects and the maximal full-syndrome protected sector

Project-derived internal finite consequences of CLBT10 arXiv.02.tex:778–792,
955–967,1195–1211,1235–1277 and BDL26 paper.tex:1237–1252,3383–3419.
The actual fixed decoder, original row labels, stored residual sign and Y=iXZ
are retained. This does not prove the zero-base stability criterion, a small
Gibbs tail, nonempty protection, geometry or a memory lifetime.
-/
noncomputable section
namespace QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators

variable (S : OddScale) (n : Nat)
local instance : Fintype (XSyndromeDomain S n) := Fintype.ofFinite _
local instance : Fintype (ZSyndromeDomain S n) := Fintype.ofFinite _

abbrev W := Word (ZMod 2) (Physical S (n+2))
abbrev xWord : W S n := (BDL26BareLogicalPair.canonicalGenerator S (n+2)).val
abbrev zWord : W S n := BDL26BareLogicalPair.partnerWord S (n+2)
abbrev xRows := (parityCheckRowCode (xSyndrome S (n+2))).carrier
abbrev zRows := (parityCheckRowCode (zSyndrome S (n+2))).carrier

private theorem pairing_comm (a b : W S n) : wordPairing a b = wordPairing b a := by
  simp only [wordPairing_apply, dotProduct_comm]

private theorem row_pairing_zero {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
    (a b : Word (ZMod 2) ι) (ha : a ∈ (parityCheckRowCode M).carrier)
    (hb : M b = 0) : wordPairing a b = 0 := by
  obtain ⟨c, rfl⟩ := (mem_parityCheckRowCode M a).mp ha
  rw [wordPairing_wordLinearMapTranspose, hb]
  simp

/-- The literal cohomology coordinate of an actual full cocycle. -/
def h1Coordinate (a : BDL26FiniteCohomology.Cocycle S (n+2)) : ZMod 2 :=
  BDL26FiniteCohomology.finiteH1Equiv S (n+2)
    (BDL26FiniteCohomology.classOf S (n+2) a)

private theorem generator_scalar (c : ZMod 2) :
    (BDL26FiniteCohomology.generator S (n+2) c).val = c • xWord S n := by
  let e : BDL26FiniteCohomology.Cocycle S 0 := BDL26SeedCohomology.seedElement
  have hlin : BDL26FiniteCohomology.prefixCocycle S (n+2) (c • e) =
      c • BDL26FiniteCohomology.prefixCocycle S (n+2) e :=
    map_smul (BDL26FiniteCohomology.prefixCocycle S (n+2)) c e
  have hx : (BDL26FiniteCohomology.prefixCocycle S (n+2) e).val = xWord S n := by
    have hu : e = (1 : ZMod 2) • e := (one_smul (ZMod 2) e).symm
    exact congrArg (fun w : BDL26FiniteCohomology.Cocycle S 0 =>
      (BDL26FiniteCohomology.prefixCocycle S (n+2) w).val) hu
  calc
    (BDL26FiniteCohomology.generator S (n+2) c).val =
        (BDL26FiniteCohomology.prefixCocycle S (n+2) (c • e)).val := rfl
    _ = c • (BDL26FiniteCohomology.prefixCocycle S (n+2) e).val :=
      congrArg (fun w : BDL26FiniteCohomology.Cocycle S (n+2) => w.val) hlin
    _ = c • xWord S n := congrArg (fun w : W S n => c • w) hx

/-- Full-word normal form, including every auxiliary coordinate. -/
theorem full_normal_form (a : BDL26FiniteCohomology.Cocycle S (n+2)) :
    ∃ g : W S n, g ∈ xRows S n ∧ a.val = g + h1Coordinate S n a • xWord S n := by
  obtain ⟨f, hf⟩ := BDL26FiniteCohomology.global_normal_form S (n+2) a
  refine ⟨BDL26RZMap1CoordinateBridge.tannerCoboundary0
    (BDL26DecodingGraph.state S (n+2)).presentation f, ?_, ?_⟩
  · rw [xRows, xRowCode]
    exact (BDL26RZCohomology.mem_boundary_iff _ _).mpr ⟨f, rfl⟩
  · exact hf.trans (congrArg (fun w : W S n =>
      BDL26RZMap1CoordinateBridge.tannerCoboundary0
        (BDL26DecodingGraph.state S (n+2)).presentation f + w) (generator_scalar S n _))

/-- The actual rank-one coordinate is exactly pairing with the derived partner. -/
theorem h1Coordinate_eq_pairing (a : BDL26FiniteCohomology.Cocycle S (n+2)) :
    h1Coordinate S n a = wordPairing a.val (zWord S n) := by
  obtain ⟨g, hg, ha⟩ := full_normal_form S n a
  have hz : wordPairing g (zWord S n) = 0 :=
    row_pairing_zero _ g _ hg (BDL26BareLogicalPair.partnerWord_kernel S (n+2))
  rw [ha]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    hz, BDL26BareLogicalPair.partnerWord_pairing, smul_eq_mul, mul_one, zero_add]

private theorem cocycle_of_kernel (a : W S n) (ha : zSyndrome S (n+2) a = 0) :
    a ∈ (BDL26FiniteCohomology.complex S (n+2)).middleCocycleCode.carrier :=
  (BDL26RZCohomology.mem_cocycle_iff _ _).mpr ha

/-- No boundary witness or rank certificate is supplied by the caller. -/
theorem x_row_iff (a : W S n) (ha : zSyndrome S (n+2) a = 0) :
    (∃ c, wordLinearMapTranspose (xSyndrome S (n+2)) c = a) ↔
      wordPairing a (zWord S n) = 0 := by
  constructor
  · intro h
    exact row_pairing_zero _ a _ ((mem_parityCheckRowCode _ _).mpr h)
      (BDL26BareLogicalPair.partnerWord_kernel S (n+2))
  · intro hz
    let v : BDL26FiniteCohomology.Cocycle S (n+2) := ⟨a, cocycle_of_kernel S n a ha⟩
    obtain ⟨g, hg, he⟩ := full_normal_form S n v
    have hc : h1Coordinate S n v = 0 := (h1Coordinate_eq_pairing S n v).trans hz
    have heq : a = g := by simpa only [hc, zero_smul, add_zero] using he
    exact (mem_parityCheckRowCode _ _).mp (heq.symm ▸ hg)

/-- The dual boundary classification follows from actual normal form and finite duality. -/
theorem z_row_iff (b : W S n) (hb : xSyndrome S (n+2) b = 0) :
    (∃ c, wordLinearMapTranspose (zSyndrome S (n+2)) c = b) ↔
      wordPairing (xWord S n) b = 0 := by
  constructor
  · intro h
    rw [pairing_comm]
    exact row_pairing_zero _ b _ ((mem_parityCheckRowCode _ _).mpr h)
      (BDL26BareLogicalPair.canonical_cocycle S (n+2))
  · intro hx
    have hd : b ∈ (parityCheckKernelCode (zSyndrome S (n+2))).dual.carrier := by
      apply (LinearCode.mem_dual _ b).mpr
      intro a ha
      have hak : zSyndrome S (n+2) a = 0 := (mem_parityCheckKernelCode _ _).mp ha
      let v : BDL26FiniteCohomology.Cocycle S (n+2) := ⟨a, cocycle_of_kernel S n a hak⟩
      obtain ⟨g, hg, he⟩ := full_normal_form S n v
      have hg0 : wordPairing g b = 0 := row_pairing_zero _ g b hg hb
      rw [pairing_comm S n b a]
      change wordPairing v.val b = 0
      rw [he]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        hg0, hx, smul_zero, add_zero]
    rw [← parityCheckRowCode_dual_eq_kernelCode, LinearCode.dual_dual_eq] at hd
    exact (mem_parityCheckRowCode _ _).mp hd

/-- The actual full residual's X logical coordinate, retaining the original binary object. -/
def dX (s : Visible S n) (E : Binary (Physical S (n+2))) : ZMod 2 :=
  wordPairing (residual S n s E).vector.xPart (zWord S n)
def dZ (s : Visible S n) (E : Binary (Physical S (n+2))) : ZMod 2 :=
  wordPairing (xWord S n) (residual S n s E).vector.zPart

theorem residual_x_boundary_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (∃ c, wordLinearMapTranspose (xSyndrome S (n+2)) c =
      (residual S n s E).vector.xPart) ↔ dX S n s E = 0 :=
  x_row_iff S n _ (pairedResidual_closed S n s.1 s.2 E).1

theorem residual_z_boundary_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (∃ c, wordLinearMapTranspose (zSyndrome S (n+2)) c =
      (residual S n s E).vector.zPart) ↔ dZ S n s E = 0 :=
  z_row_iff S n _ (pairedResidual_closed S n s.1 s.2 E).2

theorem residual_trivial_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (code S n).InGeneratedGroupUpToSign (residual S n s E) ↔
      dX S n s E = 0 ∧ dZ S n s E = 0 := by
  rw [inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff,
    mem_parityCheckRowCode, mem_parityCheckRowCode,
    residual_x_boundary_iff, residual_z_boundary_iff]

theorem residual_commutes_bare_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (Commutes (residual S n s E) (BDL26BareLogicalPair.logicalX S (n+2)) ∧
      Commutes (residual S n s E) (BDL26BareLogicalPair.logicalZ S (n+2))) ↔
      dX S n s E = 0 ∧ dZ S n s E = 0 := by
  simp only [Commutes, symplecticForm, BDL26BareLogicalPair.logicalX_xPart,
    BDL26BareLogicalPair.logicalX_zPart, BDL26BareLogicalPair.logicalZ_xPart,
    BDL26BareLogicalPair.logicalZ_zPart]
  simp only [Pi.zero_apply, mul_zero, zero_mul, sub_zero, zero_sub,
    Finset.sum_neg_distrib, Finset.sum_const_zero, neg_eq_zero]
  change (wordPairing (residual S n s E).vector.zPart (xWord S n) = 0 ∧
    wordPairing (residual S n s E).vector.xPart (zWord S n) = 0) ↔ _
  rw [pairing_comm S n _ (xWord S n)]
  exact and_comm

/-- Negating the stored sign does not alter either logical bit. -/
theorem signed_bits (phase : ZMod 2) (s : Visible S n) (E : Binary (Physical S (n+2))) :
    dX S n s (binaryMul (binarySign phase) E) = dX S n s E ∧
    dZ S n s (binaryMul (binarySign phase) E) = dZ S n s E := by
  simp only [dX, dZ, sign_residual_vector, and_self]

/-- The exact complex coefficient in the actual full commutator. -/
def coefficient (s : Visible S n) (E L : Binary (Physical S (n+2))) : ℂ :=
  commutationPhase E L * commutationPhase (correction S n s) L -
    commutationPhase (correction S n (translation S n E s)) L

/-- Only Pauli exchange is used; normalized Hermitian realization is not multiplicative. -/
theorem commutator_atom_formula (s : Visible S n) (E L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    (toHermitianQubitOperator E * dressed S n L - dressed S n L * toHermitianQubitOperator E) *
      atom S n s = coefficient S n s E L •
        (toHermitianQubitOperator L * toHermitianQubitOperator E * atom S n s) := by
  have hl : (toHermitianQubitOperator E * dressed S n L) * atom S n s =
      (commutationPhase E L * commutationPhase (correction S n s) L) •
        (toHermitianQubitOperator L * toHermitianQubitOperator E * atom S n s) := by
    rw [mul_assoc, dressed_mul_atom, mul_smul_comm, ← mul_assoc,
      toHermitianQubitOperator_mul_eq_commutationPhase_smul, smul_mul_assoc, smul_smul]
    congr 1
    exact mul_comm _ _
  have hr : (dressed S n L * toHermitianQubitOperator E) * atom S n s =
      commutationPhase (correction S n (translation S n E s)) L •
        (toHermitianQubitOperator L * toHermitianQubitOperator E * atom S n s) := by
    rw [mul_assoc, pauli_mul_atom, ← mul_assoc, dressed_mul_atom, smul_mul_assoc]
    simp only [mul_assoc]
    rw [← pauli_mul_atom S n E s]
  rw [sub_mul, hl, hr, ← sub_smul]
  rfl

private theorem pauli_atom_ne_zero (s : Visible S n) (E L : Binary (Physical S (n+2))) :
    toHermitianQubitOperator L * toHermitianQubitOperator E * atom S n s ≠ 0 := by
  intro h
  have he : toHermitianQubitOperator E * atom S n s = 0 := by
    have hh := congrArg (fun T => toHermitianQubitOperator L * T) h
    simpa only [← mul_assoc, toHermitianQubitOperator_square, one_mul, mul_zero] using hh
  have hh := congrArg (fun T => toHermitianQubitOperator E * T) he
  exact atom_ne_zero S n s (by
    simpa only [← mul_assoc, toHermitianQubitOperator_square, one_mul, mul_zero] using hh)

private theorem phase_coefficient (s : Visible S n) (E L : Binary (Physical S (n+2))) :
    coefficient S n s E L =
      (commutationPhase (residual S n s E) L - 1) *
        commutationPhase (correction S n (translation S n E s)) L := by
  rw [coefficient, residual_eq, commutationPhase_binaryMul_left, commutationPhase_binaryMul_left]
  have hb := commutationPhase_square (correction S n (translation S n E s)) L
  calc
    _ = ((commutationPhase (correction S n (translation S n E s)) L *
      commutationPhase (correction S n (translation S n E s)) L) *
      (commutationPhase E L * commutationPhase (correction S n s) L)) -
      commutationPhase (correction S n (translation S n E s)) L := by rw [hb, one_mul]
    _ = _ := by ring

private theorem coefficient_zero_iff (s : Visible S n) (E L : Binary (Physical S (n+2))) :
    coefficient S n s E L = 0 ↔ commutationPhase (residual S n s E) L = 1 := by
  have hb : commutationPhase (correction S n (translation S n E s)) L ≠ 0 := by
    intro h
    have hh := commutationPhase_square (correction S n (translation S n E s)) L
    rw [h, zero_mul] at hh
    exact zero_ne_one hh
  rw [phase_coefficient, mul_eq_zero, or_iff_left hb, sub_eq_zero]

private theorem protected_iff_phase (s : Visible S n) (E L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    (toHermitianQubitOperator E * dressed S n L - dressed S n L * toHermitianQubitOperator E) *
      atom S n s = 0 ↔ commutationPhase (residual S n s E) L = 1 := by
  rw [commutator_atom_formula S n s E L hL, smul_eq_zero,
    or_iff_left (pauli_atom_ne_zero S n s E L), coefficient_zero_iff]

private theorem phase_Z (s : Visible S n) (E : Binary (Physical S (n+2))) :
    commutationPhase (residual S n s E) (BDL26BareLogicalPair.logicalZ S (n+2)) =
      binaryPhaseScalar (dX S n s E) := by
  simp only [commutationPhase]
  congr 1
  simp [symplecticForm, BDL26BareLogicalPair.logicalZ,
    cssZCheck, dX, wordPairing_apply, dotProduct]

private theorem phase_X (s : Visible S n) (E : Binary (Physical S (n+2))) :
    commutationPhase (residual S n s E) (BDL26BareLogicalPair.logicalX S (n+2)) =
      binaryPhaseScalar (dZ S n s E) := by
  have hn (t : ZMod 2) : -t = t := ZMod.neg_eq_self_mod_two t
  simp only [commutationPhase]
  congr 1
  simp [symplecticForm, BDL26BareLogicalPair.logicalX, cssXCheck,
    dZ, wordPairing_apply, dotProduct, Finset.sum_neg_distrib, hn, mul_comm]

theorem protected_Z_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (toHermitianQubitOperator E * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * toHermitianQubitOperator E) * atom S n s = 0 ↔
        dX S n s E = 0 := by
  rw [protected_iff_phase S n s E _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2)),
    phase_Z, binaryPhaseScalar_eq_one_iff]

theorem protected_X_iff (s : Visible S n) (E : Binary (Physical S (n+2))) :
    (toHermitianQubitOperator E * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * toHermitianQubitOperator E) * atom S n s = 0 ↔
        dZ S n s E = 0 := by
  rw [protected_iff_phase S n s E _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2)),
    phase_X, binaryPhaseScalar_eq_one_iff]

/-- A one-bit defect gives exactly -2 times the post-correction sign. -/
theorem coefficient_Z_one (s : Visible S n) (E : Binary (Physical S (n+2)))
    (h : dX S n s E = 1) :
    coefficient S n s E (BDL26BareLogicalPair.logicalZ S (n+2)) =
      -2 * commutationPhase (correction S n (translation S n E s))
        (BDL26BareLogicalPair.logicalZ S (n+2)) := by
  rw [phase_coefficient, phase_Z, h, binaryPhaseScalar_one]
  ring

theorem coefficient_X_one (s : Visible S n) (E : Binary (Physical S (n+2)))
    (h : dZ S n s E = 1) :
    coefficient S n s E (BDL26BareLogicalPair.logicalX S (n+2)) =
      -2 * commutationPhase (correction S n (translation S n E s))
        (BDL26BareLogicalPair.logicalX S (n+2)) := by
  rw [phase_coefficient, phase_X, h, binaryPhaseScalar_one]
  ring

/-- Unrealisable raw labels contribute zero, with no false converse. -/
theorem raw_invalid (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (hw : w ∉ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2)))
    (E : Binary (Physical S (n+2))) (O : BDL26PairedDecoderChannel.Op S n) :
    (toHermitianQubitOperator E * O - O * toHermitianQubitOperator E) * projector S (n+2) w = 0 := by
  have hz : projector S (n+2) w = 0 :=
    CSSGibbs.projector_eq_zero_of_not_realizable _ _ _ _ hw
  rw [hz, mul_zero]

/-- Actual single-site differences on each original stopped decoder. -/
def deltaX (u : XSyndromeDomain S n) (q : Physical S (n+2)) : W S n :=
  xCorrection S n (translateX S n u (Pi.single q 1)) + Pi.single q 1 + xCorrection S n u
def deltaZ (v : ZSyndromeDomain S n) (q : Physical S (n+2)) : W S n :=
  zCorrection S n (translateZ S n v (Pi.single q 1)) + Pi.single q 1 + zCorrection S n v
def chiX (u : XSyndromeDomain S n) (q : Physical S (n+2)) : ZMod 2 :=
  wordPairing (deltaX S n u q) (zWord S n)
def chiZ (v : ZSyndromeDomain S n) (q : Physical S (n+2)) : ZMod 2 :=
  wordPairing (xWord S n) (deltaZ S n v q)

private theorem translateX_zero (u : XSyndromeDomain S n) : translateX S n u 0 = u := by
  apply Subtype.ext
  change u.val + zSyndrome S (n+2) 0 = u.val
  rw [map_zero, add_zero]
private theorem translateZ_zero (v : ZSyndromeDomain S n) : translateZ S n v 0 = v := by
  apply Subtype.ext
  change v.val + xSyndrome S (n+2) 0 = v.val
  rw [map_zero, add_zero]
private theorem word_add_self (a : W S n) : a + a = 0 := by
  funext q
  exact CharTwo.add_self_eq_zero (a q)

theorem residual_single_x (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .x)).vector.xPart = deltaX S n s.1 q ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .x)).vector.zPart = 0 := by
  constructor
  · exact pairedResidual_xPart S n s.1 s.2 _
  · rw [BDL26PairedDecoderPhase.residual, pairedResidual_zPart]
    change zCorrection S n (translateZ S n s.2 0) + 0 + zCorrection S n s.2 = 0
    rw [translateZ_zero, add_zero, word_add_self]

theorem residual_single_z (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .z)).vector.xPart = 0 ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .z)).vector.zPart = deltaZ S n s.2 q := by
  constructor
  · rw [BDL26PairedDecoderPhase.residual, pairedResidual_xPart]
    change xCorrection S n (translateX S n s.1 0) + 0 + xCorrection S n s.1 = 0
    rw [translateX_zero, add_zero, word_add_self]
  · exact pairedResidual_zPart S n s.1 s.2 _

/-- Direct same-residual Y proof, not multiplication of compressed commutators. -/
theorem residual_single_y (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .y)).vector.xPart = deltaX S n s.1 q ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .y)).vector.zPart = deltaZ S n s.2 q ∧
    BDL26CSSDaviesLocality.coupling S (n+2) q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) :=
  ⟨pairedResidual_xPart S n s.1 s.2 _, pairedResidual_zPart S n s.1 s.2 _,
    BDL26CSSDaviesLocality.coupling_y S (n+2) q⟩

private theorem single_bits (s : Visible S n) (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) :
    (dX S n s (CSSDaviesLocality.singlePauli q axis), dZ S n s (CSSDaviesLocality.singlePauli q axis)) =
      match axis with
      | .x => (chiX S n s.1 q, 0)
      | .y => (chiX S n s.1 q, chiZ S n s.2 q)
      | .z => (0, chiZ S n s.2 q) := by
  cases axis
  · simp only [dX, dZ, (residual_single_x S n s q).1,
      (residual_single_x S n s q).2, map_zero, chiX]
  · simp only [dX, dZ, (residual_single_y S n s q).1,
      (residual_single_y S n s q).2.1, chiX, chiZ]
  · simp only [dX, dZ, (residual_single_z S n s q).1,
      (residual_single_z S n s q).2, map_zero, LinearMap.zero_apply, chiZ]

/-- No stability or protection property is stored as construction data. -/
def goodX : Finset (XSyndromeDomain S n) := Finset.univ.filter (fun u => ∀ q, chiX S n u q = 0)
def goodZ : Finset (ZSyndromeDomain S n) := Finset.univ.filter (fun v => ∀ q, chiZ S n v q = 0)
def good : Finset (Visible S n) := goodX S n ×ˢ goodZ S n
def protectedProjector : BDL26PairedDecoderChannel.Op S n :=
  BDL26TwoSectorBadProjector.selected S (n+2) (good S n)

theorem good_iff (s : Visible S n) :
    s ∈ good S n ↔ (∀ q, chiX S n s.1 q = 0) ∧ (∀ q, chiZ S n s.2 q = 0) := by
  simp only [good, goodX, goodZ, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem good_iff_residuals (s : Visible S n) :
    s ∈ good S n ↔ ∀ q axis,
      (code S n).InGeneratedGroupUpToSign (residual S n s (CSSDaviesLocality.singlePauli q axis)) := by
  rw [good_iff]
  constructor
  · rintro ⟨hx, hz⟩ q axis
    rw [residual_trivial_iff]
    have h := single_bits S n s q axis
    cases axis <;> simp_all
  · intro h
    constructor
    · intro q
      have hh := (residual_trivial_iff S n s _).mp (h q .x)
      have hb := congrArg Prod.fst (single_bits S n s q .x)
      exact hb.symm.trans hh.1
    · intro q
      have hh := (residual_trivial_iff S n s _).mp (h q .z)
      have hb := congrArg Prod.snd (single_bits S n s q .z)
      exact hb.symm.trans hh.2

/-- Both logical generators, all actual sites and all three physical axes. -/
def Protects (A : Finset (Visible S n)) : Prop := ∀ q axis,
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        BDL26TwoSectorBadProjector.selected S (n+2) A = 0 ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        BDL26TwoSectorBadProjector.selected S (n+2) A = 0

private theorem atom_selected (A : Finset (Visible S n)) (s : Visible S n) :
    BDL26TwoSectorBadProjector.selected S (n+2) A * atom S n s =
      if s ∈ A then atom S n s else 0 := by
  change (∑ t ∈ A, atom S n t) * atom S n s = _
  rw [Finset.sum_mul]
  by_cases hs : s ∈ A
  · rw [if_pos hs, Finset.sum_eq_single s]
    · exact atom_square S n s
    · intro t _ hts
      exact atom_mul_of_ne S n t s hts
    · exact fun h => (h hs).elim
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro t ht
    apply atom_mul_of_ne
    intro h
    exact hs (h ▸ ht)

/-- Exact atom converse for the actual physical coupling family. -/
theorem good_iff_atom_protected (s : Visible S n) :
    s ∈ good S n ↔ ∀ q axis,
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) * atom S n s = 0 ∧
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) * atom S n s = 0 := by
  rw [good_iff_residuals]
  apply forall_congr'
  intro q
  apply forall_congr'
  intro axis
  rw [residual_trivial_iff, ← protected_X_iff, ← protected_Z_iff]
  exact and_comm

/-- The full selection theorem includes necessity; it is not a supplied-good-set wrapper. -/
theorem selection_protected_iff (A : Finset (Visible S n)) :
    Protects S n A ↔ A ⊆ good S n := by
  constructor
  · intro h s hs
    apply (good_iff_atom_protected S n s).mpr
    intro q axis
    obtain ⟨hx,hz⟩ := h q axis
    constructor
    · have hh := congrArg (fun T : BDL26PairedDecoderChannel.Op S n => T * atom S n s) hx
      simpa only [mul_assoc, atom_selected, if_pos hs, zero_mul] using hh
    · have hh := congrArg (fun T : BDL26PairedDecoderChannel.Op S n => T * atom S n s) hz
      simpa only [mul_assoc, atom_selected, if_pos hs, zero_mul] using hh
  · intro h q axis
    have hx := fun s hs => (good_iff_atom_protected S n s).mp (h hs) q axis
    constructor
    · change _ * (∑ s ∈ A, atom S n s) = 0
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun s hs => (hx s hs).1)
    · change _ * (∑ s ∈ A, atom S n s) = 0
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun s hs => (hx s hs).2)

theorem projector_projection : IsStarProjection (protectedProjector S n) :=
  CSSGibbs.selectedProjector_starProjection _ _ (row_orthogonal S (n+2)) _

theorem projector_hamiltonian : Commute (hamiltonian S (n+2)) (protectedProjector S n) :=
  BDL26TwoSectorBadProjector.hamiltonian_commute S (n+2) _

private theorem normalizer_selected (A : Finset (Visible S n)) (L : Binary (Physical S (n+2)))
    (hL : (code S n).InBinaryNormalizer L) :
    Commute (dressed S n L) (BDL26TwoSectorBadProjector.selected S (n+2) A) := by
  change Commute (dressed S n L) (∑ s ∈ A, atom S n s)
  apply Commute.sum_right
  intro s _
  have hc := normalizer_commute_atom S n L hL s
  have hp : Commute (phaseOperator S n L) (atom S n s) :=
    (phaseOperator_mul_atom S n L s).trans (atom_mul_phaseOperator S n L s).symm
  exact hc.mul_left hp

theorem projector_dressed_X : Commute (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) :=
  normalizer_selected S n _ _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))
theorem projector_dressed_Z : Commute (BDL26PairedDecoderChannel.dressedZ S n) (protectedProjector S n) :=
  normalizer_selected S n _ _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))

theorem maximal_product_iff (A : Finset (Visible S n)) :
    BDL26TwoSectorBadProjector.selected S (n+2) A * protectedProjector S n =
      BDL26TwoSectorBadProjector.selected S (n+2) A ↔ A ⊆ good S n := by
  constructor
  · intro h s hs
    by_contra hg
    have hh := congrArg (fun T : BDL26PairedDecoderChannel.Op S n => T * atom S n s) h
    simp only [mul_assoc, protectedProjector, atom_selected, if_neg hg,
      mul_zero, if_pos hs] at hh
    exact atom_ne_zero S n s hh.symm
  · intro h
    change CSSGibbs.selectedProjector _ _ _ A * CSSGibbs.selectedProjector _ _ _ (good S n) = _
    rw [CSSGibbs.selectedProjector_mul, Finset.inter_eq_left.mpr h]

theorem maximal_protection (A : Finset (Visible S n)) :
    Protects S n A ↔ BDL26TwoSectorBadProjector.selected S (n+2) A * protectedProjector S n =
      BDL26TwoSectorBadProjector.selected S (n+2) A :=
  (selection_protected_iff S n A).trans (maximal_product_iff S n A).symm

theorem actual_XYZ_protected : Protects S n (good S n) :=
  (selection_protected_iff S n _).mpr (Finset.Subset.refl _)

/-- Logical Y follows from logical invariance; no physical-error invariance is assumed. -/
theorem logical_Y_protected (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) :
    (BDL26CSSDaviesLocality.coupling S (n+2) q axis * BDL26PairedDecoderChannel.dressedY S n -
      BDL26PairedDecoderChannel.dressedY S n * BDL26CSSDaviesLocality.coupling S (n+2) q axis) *
        protectedProjector S n = 0 := by
  let J : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26PairedDecoderChannel.Op S n :=
    fun qa => BDL26CSSDaviesLocality.coupling S (n+2) qa.1 qa.2
  have hx : JumpProtected J (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) :=
    fun qa => (actual_XYZ_protected S n qa.1 qa.2).1
  have hz : JumpProtected J (BDL26PairedDecoderChannel.dressedZ S n) (protectedProjector S n) :=
    fun qa => (actual_XYZ_protected S n qa.1 qa.2).2
  exact ((hx.mul_of_commute_projector hz (projector_dressed_Z S n)).smul Complex.I) (q,axis)

/-- Actual same-H coherent grouped-frequency jumps consume derived XYZ protection. -/
theorem actual_jumps_X
    (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ) :
    JumpProtected (BDL26BoundedRateDavies.jump S (n+2) rate)
      (BDL26PairedDecoderChannel.dressedX S n) (protectedProjector S n) := by
  apply Davies.hamiltonianJump_protected
  · exact (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm
  · exact projector_hamiltonian S n
  · intro qa
    exact (actual_XYZ_protected S n qa.1 qa.2).1

theorem actual_jumps_Z
    (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+2) → BDL26CSSDaviesLocality.Frequency S (n+2) → ℝ) :
    JumpProtected (BDL26BoundedRateDavies.jump S (n+2) rate)
      (BDL26PairedDecoderChannel.dressedZ S n) (protectedProjector S n) := by
  apply Davies.hamiltonianJump_protected
  · exact (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))).symm
  · exact projector_hamiltonian S n
  · intro qa
    exact (actual_XYZ_protected S n qa.1 qa.2).2

/-- Original frequency sign and all real frequencies are inherited unchanged. -/
theorem actual_frequency_X (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) (omega : ℝ) :
    (Davies.actualFrequency (hamiltonian S (n+2)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * BDL26PairedDecoderChannel.dressedX S n -
      BDL26PairedDecoderChannel.dressedX S n * Davies.actualFrequency (hamiltonian S (n+2))
        (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
          (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * protectedProjector S n = 0 := by
  apply Davies.frequencyComponent_protected
  · simpa only [Davies.hamiltonian_diagonal] using
      (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalX_normalizer S (n+2))).symm
  · simpa only [Davies.hamiltonian_diagonal] using projector_hamiltonian S n
  · exact (actual_XYZ_protected S n q axis).1

/-- The second logical generator uses the same full-H frequency and original sign. -/
theorem actual_frequency_Z (q : Physical S (n+2)) (axis : CSSDaviesLocality.Axis) (omega : ℝ) :
    (Davies.actualFrequency (hamiltonian S (n+2)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
      (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega * BDL26PairedDecoderChannel.dressedZ S n -
      BDL26PairedDecoderChannel.dressedZ S n * Davies.actualFrequency (hamiltonian S (n+2))
        (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+2))
          (BDL26CSSDaviesLocality.coupling S (n+2) q axis) omega) * protectedProjector S n = 0 := by
  apply Davies.frequencyComponent_protected
  · simpa only [Davies.hamiltonian_diagonal] using
      (dressed_commute_hamiltonian S n _ (BDL26BareLogicalPair.logicalZ_normalizer S (n+2))).symm
  · simpa only [Davies.hamiltonian_diagonal] using projector_hamiltonian S n
  · exact (actual_XYZ_protected S n q axis).2

def badX : Finset (XSyndromeDomain S n) := (goodX S n)ᶜ
def badZ : Finset (ZSyndromeDomain S n) := (goodZ S n)ᶜ

theorem projector_eq_joint : protectedProjector S n = BDL26TwoSectorBadProjector.Pjoint S (n+2) (badX S n) (badZ S n) := by
  simp only [protectedProjector, BDL26TwoSectorBadProjector.Pjoint,
    BDL26TwoSectorBadProjector.goodJoint, badX, badZ, compl_compl, good]

theorem tail_exact (beta : ℝ) :
    clbtGibbsTailMass (protectedProjector S n) (gibbs S (n+2) beta) =
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) +
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) -
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) *
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) := by
  rw [projector_eq_joint]
  exact BDL26TwoSectorBadProjector.tail_exact S (n+2) beta _ _

theorem tail_union_bound (beta : ℝ) :
    clbtGibbsTailMass (protectedProjector S n) (gibbs S (n+2) beta) ≤
      BDL26TwoSectorBadProjector.pX S (n+2) beta (badX S n) +
      BDL26TwoSectorBadProjector.pZ S (n+2) beta (badZ S n) := by
  rw [projector_eq_joint]
  exact BDL26TwoSectorBadProjector.tail_union_bound S (n+2) beta _ _

theorem source_even (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j+2 = 2*k ∧ Protects S j (good S j) ∧
      IsStarProjection (protectedProjector S j) :=
  ⟨2*(k-1), source_even_level k hk, actual_XYZ_protected S _, projector_projection S _⟩

end QEC.Coding.BDL26LogicalDefectProtection
end
