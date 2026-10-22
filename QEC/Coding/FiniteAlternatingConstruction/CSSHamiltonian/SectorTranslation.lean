import QEC.Coding.CSS.GibbsSyndrome.Translation
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.TwoSectorBadProjector
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDimension
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.DaviesLocality

/-! # Actual XYZ sector translation and exact selection invariance

Project-derived finite algebra in the actual physical Hilbert register.
CLBT10 arXiv.02.tex:1195–1211,1234–1276 describes syndrome addition and
selected syndrome subspaces; the Hermitian XYZ convention is approved in #843.
Arbitrary selections are not asserted to be decoder-stable or protected.
-/
noncomputable section
namespace QEC.Coding.BDL26SectorTranslation
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26CSSDaviesLocality BDL26TwoSectorBadProjector
open scoped BigOperators
variable (S : OddScale) (n : Nat)
local instance : Fintype (XImage S n) := Fintype.ofFinite _
local instance : Fintype (ZImage S n) := Fintype.ofFinite _

/-- Literal basis error in the original physical carrier. -/
abbrev basisError (q : Physical S n) : Word (ZMod 2) (Physical S n) := Pi.single q 1

def epsilonX (q : Physical S n) : XImage S n :=
  ⟨zSyndrome S n (basisError S n q), ⟨basisError S n q, rfl⟩⟩
def epsilonZ (q : Physical S n) : ZImage S n :=
  ⟨xSyndrome S n (basisError S n q), ⟨basisError S n q, rfl⟩⟩

def translation (q : Physical S n) (a : CSSDaviesLocality.Axis) : JointImage S n ≃ JointImage S n :=
  CSSGibbs.jointTranslation (zSyndrome S n) (xSyndrome S n) (CSSDaviesLocality.singlePauli q a)

theorem translation_involutive (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    Function.Involutive (translation S n q a) :=
  CSSGibbs.jointTranslation_involutive _ _ _

theorem translation_bijective (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    Function.Bijective (translation S n q a) := (translation S n q a).bijective

@[simp] theorem translation_x (q : Physical S n) (s : JointImage S n) :
    translation S n q .x s = (s.1 + epsilonX S n q, s.2) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change s.2.val + xSyndrome S n 0 = s.2.val
    rw [map_zero, add_zero]

@[simp] theorem translation_z (q : Physical S n) (s : JointImage S n) :
    translation S n q .z s = (s.1, s.2 + epsilonZ S n q) := by
  apply Prod.ext
  · apply Subtype.ext
    change s.1.val + zSyndrome S n 0 = s.1.val
    rw [map_zero, add_zero]
  · rfl

@[simp] theorem translation_y (q : Physical S n) (s : JointImage S n) :
    translation S n q .y s = (s.1 + epsilonX S n q, s.2 + epsilonZ S n q) := rfl

/-- This is the original Hermitian Y, not an unphased XZ replacement. -/
theorem coupling_y_phase (q : Physical S n) :
    coupling S n q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) := coupling_y S n q

def translated (q : Physical S n) (a : CSSDaviesLocality.Axis) (A : Finset (JointImage S n)) :
    Finset (JointImage S n) := A.map (translation S n q a).toEmbedding

theorem translated_image (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S n)) :
    translated S n q a A = A.image (translation S n q a) :=
  CSSGibbs.translatedSelection_image _ _ _ A

/-- Every actual realizable atom is nonzero, derived from its trace two. -/
theorem atom_ne_zero (s : JointImage S n) :
    projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s) ≠ 0 := by
  intro h
  have ht := realizable_projector_trace_two S n s.1 s.2
  change LinearMap.trace ℂ _ (projector S n
    (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s)) = (2 : ℂ) at ht
  rw [h, map_zero] at ht
  norm_num at ht

/-- Orthogonal nonzero actual atoms distinguish every finite selection. -/
theorem selected_injective : Function.Injective (selected S n) := by
  intro A B h
  apply Finset.ext
  intro s
  have hm := congrArg (fun T : Operator (Qubit.QubitRegister (Physical S n)) =>
    projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s) * T) h
  change _ * CSSGibbs.selectedProjector _ _ _ A =
    _ * CSSGibbs.selectedProjector _ _ _ B at hm
  rw [CSSGibbs.atom_mul_selected, CSSGibbs.atom_mul_selected] at hm
  constructor
  · intro ha
    by_contra hb
    exact atom_ne_zero S n s (by simpa only [if_pos ha, if_neg hb] using hm)
  · intro hb
    by_contra ha
    exact atom_ne_zero S n s (by simpa only [if_neg ha, if_pos hb] using hm.symm)

theorem coupling_mul_atom (q : Physical S n) (a : CSSDaviesLocality.Axis) (s : JointImage S n) :
    coupling S n q a * projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s) =
      projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n)
        (translation S n q a s)) * coupling S n q a :=
  CSSGibbs.pauli_mul_realizable_projector _ _ (row_orthogonal S n) _ s

theorem coupling_mul_selected (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S n)) :
    coupling S n q a * selected S n A =
      selected S n (translated S n q a A) * coupling S n q a :=
  CSSGibbs.pauli_mul_selected _ _ (row_orthogonal S n) _ A

theorem conjugate_selected (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S n)) :
    coupling S n q a * selected S n A * coupling S n q a =
      selected S n (translated S n q a A) :=
  CSSGibbs.pauli_conjugate_selected _ _ (row_orthogonal S n) _ A

/-- The converse uses actual nonzero atoms, not an assumed invariance certificate. -/
theorem commute_selected_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S n)) :
    Commute (coupling S n q a) (selected S n A) ↔ translated S n q a A = A := by
  constructor
  · intro h
    apply selected_injective S n
    calc
      _ = coupling S n q a * selected S n A * coupling S n q a :=
        (conjugate_selected S n q a A).symm
      _ = selected S n A := by rw [h.eq, mul_assoc, coupling_square, mul_one]
  · intro h
    show _ * _ = _ * _
    simpa only [h] using coupling_mul_selected S n q a A

/-- Factor translations use the same single-Pauli binary coordinates. -/
def translatedX (q : Physical S n) (a : CSSDaviesLocality.Axis) (A : Finset (XImage S n)) :=
  A.map (CSSGibbs.rangeShiftEquiv (zSyndrome S n) (CSSDaviesLocality.singlePauli q a).vector.xPart).toEmbedding
def translatedZ (q : Physical S n) (a : CSSDaviesLocality.Axis) (B : Finset (ZImage S n)) :=
  B.map (CSSGibbs.rangeShiftEquiv (xSyndrome S n) (CSSDaviesLocality.singlePauli q a).vector.zPart).toEmbedding

theorem translated_rectangle (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (XImage S n)) (B : Finset (ZImage S n)) :
    translated S n q a (A ×ˢ B) = translatedX S n q a A ×ˢ translatedZ S n q a B :=
  CSSGibbs.translatedSelection_product _ _ _ A B

theorem conjugate_rectangle (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (XImage S n)) (B : Finset (ZImage S n)) :
    coupling S n q a * selected S n (A ×ˢ B) * coupling S n q a =
      selected S n (translatedX S n q a A ×ˢ translatedZ S n q a B) := by
  rw [conjugate_selected, translated_rectangle]

private theorem rectangle_eq_iff {α β : Type} [DecidableEq α] [DecidableEq β]
    (A C : Finset α) (B D : Finset β) (ha : A.Nonempty) (hb : B.Nonempty)
    (hc : C.Nonempty) (hd : D.Nonempty) :
    A ×ˢ B = C ×ˢ D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    constructor
    · ext x
      constructor
      · intro hx
        obtain ⟨y,hy⟩ := hb
        have hxy : (x,y) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨hx,hy⟩
        rw [h] at hxy
        exact (Finset.mem_product.mp hxy).1
      · intro hx
        obtain ⟨y,hy⟩ := hd
        have hxy : (x,y) ∈ C ×ˢ D := Finset.mem_product.mpr ⟨hx,hy⟩
        rw [← h] at hxy
        exact (Finset.mem_product.mp hxy).1
    · ext y
      constructor
      · intro hy
        obtain ⟨x,hx⟩ := ha
        have hxy : (x,y) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨hx,hy⟩
        rw [h] at hxy
        exact (Finset.mem_product.mp hxy).2
      · intro hy
        obtain ⟨x,hx⟩ := hc
        have hxy : (x,y) ∈ C ×ˢ D := Finset.mem_product.mpr ⟨hx,hy⟩
        rw [← h] at hxy
        exact (Finset.mem_product.mp hxy).2
  · rintro ⟨rfl,rfl⟩; rfl

/-- Empty factors give the zero operator; otherwise both factors must be invariant. -/
theorem commute_rectangle_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (XImage S n)) (B : Finset (ZImage S n)) :
    Commute (coupling S n q a) (selected S n (A ×ˢ B)) ↔
      A = ∅ ∨ B = ∅ ∨ (translatedX S n q a A = A ∧ translatedZ S n q a B = B) := by
  rw [commute_selected_iff, translated_rectangle]
  by_cases ha : A = ∅
  · subst A; simp [translatedX]
  by_cases hb : B = ∅
  · subst B; simp [translatedZ]
  have hA := Finset.nonempty_iff_ne_empty.mpr ha
  have hB := Finset.nonempty_iff_ne_empty.mpr hb
  have hX : (translatedX S n q a A).Nonempty := by
    obtain ⟨x,hx⟩ := hA
    exact ⟨_, Finset.mem_map.mpr ⟨x,hx,rfl⟩⟩
  have hZ : (translatedZ S n q a B).Nonempty := by
    obtain ⟨y,hy⟩ := hB
    exact ⟨_, Finset.mem_map.mpr ⟨y,hy,rfl⟩⟩
  simpa only [ha,hb,false_or] using
    rectangle_eq_iff (translatedX S n q a A) A (translatedZ S n q a B) B hX hZ hA hB

/-- Existing two-sector good selection, without a claim of decoder invariance. -/
theorem commute_goodJoint_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (coupling S n q a) (Pjoint S n BX BZ) ↔
      BXᶜ = ∅ ∨ BZᶜ = ∅ ∨
        (translatedX S n q a BXᶜ = BXᶜ ∧ translatedZ S n q a BZᶜ = BZᶜ) :=
  commute_rectangle_iff S n q a BXᶜ BZᶜ

theorem commute_PX_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (BX : Finset (XImage S n)) :
    Commute (coupling S n q a) (PX S n BX) ↔
      translated S n q a (goodX S n BX) = goodX S n BX :=
  commute_selected_iff S n q a (goodX S n BX)

theorem commute_PZ_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (BZ : Finset (ZImage S n)) :
    Commute (coupling S n q a) (PZ S n BZ) ↔
      translated S n q a (goodZ S n BZ) = goodZ S n BZ :=
  commute_selected_iff S n q a (goodZ S n BZ)

theorem commute_empty (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    Commute (coupling S n q a) (selected S n ∅) := by
  rw [commute_selected_iff]
  simp [translated]

theorem commute_full (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    Commute (coupling S n q a) (selected S n Finset.univ) := by
  change Commute _ (CSSGibbs.selectedProjector _ _ _ _)
  rw [CSSGibbs.selectedProjector_total]
  exact Commute.one_right _

theorem even_commute_selected_iff (k : Nat) (q : Physical S (2*k)) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S (2*k))) :
    Commute (coupling S (2*k) q a) (selected S (2*k) A) ↔
      translated S (2*k) q a A = A := commute_selected_iff S (2*k) q a A

end QEC.Coding.BDL26SectorTranslation
