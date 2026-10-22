import QEC.Coding.FiniteAlternatingConstruction.RXLocalReplacement
import QEC.Coding.FiniteAlternatingConstruction.XLocalWeightParity

/-!
# Counting the actual X-to-Q restriction coordinates

Basis costs are counted in the fibres of the concrete cylinder embeddings.
These fibres count all neighbouring Q blocks at once.
-/

namespace QEC.Coding.BDL26XLocalConnectingWeight

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

abbrev Two := Fin 2

abbrev Neighbor (P : TannerSquarePresentation) (x : P.X) :=
  {q : P.Q // P.xq x q = true}

abbrev Output (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  Σ q : Neighbor P x, QDoubleCylinderEdge P q.val S

def outputEdge (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (d : Output P x S) : DoubleCylinderEdge P x S :=
  qToXDoubleCylinderEdge P A d.1.val x d.1.property S d.2

noncomputable def connectingWeight
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f : Word (ZMod 2) (DoubleCylinderEdge P x S)) : ℕ :=
  ∑ q : Neighbor P x, HammingWeight (rxXQDegreeOne P A q.val x q.property S f)

abbrev Fiber (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) :=
  {d : Output P x S // outputEdge P A x S d = e}

theorem connectingWeight_eq_packed
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f : Word (ZMod 2) (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S f = HammingWeight (fun d => f (outputEdge P A x S d)) := by
  classical
  simp only [connectingWeight, HammingWeight, hammingSupport, Finset.card_filter]
  rw [Fintype.sum_sigma]
  rfl

/-- Exact basis cost, with no assumed support or multiplicity bound. -/
theorem connectingWeight_single
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) (b : ZMod 2) :
    connectingWeight P A x S (Pi.single e b) =
      bitWeight b * Fintype.card (Fiber P A x S e) := by
  classical
  rw [connectingWeight_eq_packed]
  by_cases hb : b = 0
  · subst b
    simp [bitWeight, hammingSupport]
  · rw [bitWeight, if_neg hb, one_mul, Fintype.card_subtype]
    unfold HammingWeight hammingSupport
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hd : outputEdge P A x S d = e
    · simp [hd, hb]
    · simp [Pi.single_eq_of_ne hd, hd]

/-- Regularity bounds the actual shared-Q fibre by the two face corners. -/
theorem sharedQ_card_le_two (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) (x : P.X) (z : P.Z) :
    Fintype.card (SharedQ P.data x z) ≤ 2 := by
  letI := R.faceOver_subsingleton x z
  let toCorner : SharedQ P.data x z → Two :=
    fun q => ((P.faceCornerEquiv x z).symm q).2
  have hi : Function.Injective toCorner := by
    intro a b hab
    apply (P.faceCornerEquiv x z).symm.injective
    exact Prod.ext (Subsingleton.elim _ _) hab
  simpa [Two] using Fintype.card_le_of_injective toCorner hi

/-- Read the old Q tag of a copied original Q-Z segment. -/
def copiedQ (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderEdge P x S → Option P.Q
  | .inl (_, .inl (old, _)) =>
      match old.val with
      | .inr qz => some qz.val.1
      | .inl _ => none
  | _ => none

@[simp] theorem copiedQ_image_copy
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : Two × QSubdivisionEdge P q.val S) :
    copiedQ P x S (outputEdge P A x S ⟨q, Sum.inl e⟩) = some q.val := rfl

@[simp] theorem copiedQ_image_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : QStarEdge P q.val) :
    copiedQ P x S (outputEdge P A x S ⟨q, Sum.inr e⟩) = none := rfl

/-- A copied original boundary segment occurs in at most one output block. -/
theorem fiber_card_le_one_of_copied
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (q : P.Q) (he : copiedQ P x S e = some q) :
    Fintype.card (Fiber P A x S e) ≤ 1 := by
  classical
  apply Fintype.card_le_one_iff.mpr
  rintro ⟨⟨qa, ea⟩, ha⟩ ⟨⟨qb, eb⟩, hb⟩
  have hqa : qa.val = q := by
    have h := congrArg (copiedQ P x S) ha
    rcases ea with ea | ea
    · simpa [he] using h
    · simp [he] at h
  have hqb : qb.val = q := by
    have h := congrArg (copiedQ P x S) hb
    rcases eb with eb | eb
    · simpa [he] using h
    · simp [he] at h
  have hq : qa = qb := Subtype.ext (hqa.trans hqb.symm)
  subst qb
  have hedges : ea = eb :=
    qToXDoubleCylinderEdge_injective P A qa.val x qa.property S (ha.trans hb.symm)
  subst eb
  rfl

theorem connectingWeight_single_le_of_copied
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (q : P.Q) (he : copiedQ P x S e = some q) (b : ZMod 2) :
    connectingWeight P A x S (Pi.single e b) ≤ bitWeight b := by
  rw [connectingWeight_single]
  simpa using Nat.mul_le_mul_left (bitWeight b)
    (fiber_card_le_one_of_copied P A x S e q he)

/-- Read the old Z tag of a vertical original-boundary vertex. -/
def verticalZ (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    DoubleCylinderEdge P x S → Option P.Z
  | .inr v =>
      match v.val with
      | .inl old =>
          match old.val with
          | .z z => some z
          | _ => none
      | _ => none
  | _ => none

@[simp] theorem verticalZ_image_copy
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : Two × QSubdivisionEdge P q.val S) :
    verticalZ P x S (outputEdge P A x S ⟨q, Sum.inl e⟩) = none := rfl

@[simp] theorem verticalZ_image_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (q : Neighbor P x)
    (e : QStarEdge P q.val) :
    verticalZ P x S (outputEdge P A x S ⟨q, Sum.inr e⟩) = some e.val := rfl

theorem fiber_neighbor_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) :
    Function.Injective (fun d : Fiber P A x S e => d.val.1) := by
  rintro ⟨⟨qa, ea⟩, ha⟩ ⟨⟨qb, eb⟩, hb⟩ hq
  change qa = qb at hq
  subst qb
  have hedges : ea = eb :=
    qToXDoubleCylinderEdge_injective P A qa.val x qa.property S (ha.trans hb.symm)
  subst eb
  rfl

/-- A vertical old-Z corner can meet only the two corners of its unique face. -/
theorem fiber_card_le_two_of_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (z : P.Z) (he : verticalZ P x S e = some z) :
    Fintype.card (Fiber P A x S e) ≤ 2 := by
  classical
  have hIncident : ∀ d : Fiber P A x S e, P.qz d.val.1.val z = true := by
    rintro ⟨⟨q, ed⟩, hd⟩
    have h := congrArg (verticalZ P x S) hd
    rcases ed with ed | ed
    · simp [he] at h
    · have hz : ed.val = z := by simpa [he] using h
      exact hz ▸ ed.property
  let toShared : Fiber P A x S e → SharedQ P.data x z := fun d =>
    ⟨d.val.1.val, by simpa using And.intro d.val.1.property (hIncident d)⟩
  have hi : Function.Injective toShared := by
    intro a b hab
    apply fiber_neighbor_injective P A x S e
    apply Subtype.ext
    exact congrArg (fun q : SharedQ P.data x z => q.val) hab
  exact (Fintype.card_le_of_injective toShared hi).trans
    (sharedQ_card_le_two P R x z)

theorem connectingWeight_single_le_of_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (z : P.Z) (he : verticalZ P x S e = some z) (b : ZMod 2) :
    connectingWeight P A x S (Pi.single e b) ≤ 2 * bitWeight b := by
  rw [connectingWeight_single]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left (bitWeight b)
    (fiber_card_le_two_of_vertical P A R x S e z he)

/-- All other cylinder edge tags have zero connecting cost. -/
theorem connectingWeight_single_eq_zero_of_other
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S)
    (hc : copiedQ P x S e = none) (hv : verticalZ P x S e = none)
    (b : ZMod 2) : connectingWeight P A x S (Pi.single e b) = 0 := by
  classical
  letI : IsEmpty (Fiber P A x S e) := ⟨by
    rintro ⟨⟨q, ed⟩, hd⟩
    rcases ed with ed | ed
    · have h := congrArg (copiedQ P x S) hd
      simp [hc] at h
    · have h := congrArg (verticalZ P x S) hd
      simp [hv] at h⟩
  simp [connectingWeight_single]

end QEC.Coding.BDL26XLocalConnectingWeight
