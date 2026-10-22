import QEC.Coding.CSS.GibbsSyndrome.Selection

/-! # Pauli translation of finite realizable CSS sector selections

The arbitrary-background transport formula is proved from signed measurement
outcomes. These are finite operator identities; no decoder stability is assumed.
-/
noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
local instance : Fintype (LinearMap.range P) := Fintype.ofFinite _
local instance : Fintype (LinearMap.range Q) := Fintype.ofFinite _

/-- Translation holds at every background, not just the all-plus sector. -/
theorem transport_add (E : Binary ι) (s : Word (ZMod 2) (Sum κP κQ)) :
    transportSyndrome (binaryCSSParityCheckGenerators P Q) (checks_commute P Q horth)
      E (syndromeOutcome _ s) =
    syndromeOutcome _ (s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) := by
  funext j
  by_cases hc : Commutes E (binaryCSSParityCheckGenerators P Q j)
  · have hz := (stabilizerSyndromeBit_eq_zero_iff_commutes _ _).mpr hc
    simp only [transportSyndrome, if_pos hc, syndromeOutcome_apply, Pi.add_apply,
      stabilizerSyndrome_apply, hz, add_zero]
  · have ho := (stabilizerSyndromeBit_eq_one_iff_not_commutes _ _).mpr hc
    simp only [transportSyndrome, if_neg hc, syndromeOutcome_apply, Pi.add_apply,
      stabilizerSyndrome_apply, ho]
    generalize s j = b
    fin_cases b <;> rfl

theorem pauli_mul_projector_add (E : Binary ι) (s : Word (ZMod 2) (Sum κP κQ)) :
    toHermitianQubitOperator E * projector P Q horth s =
      projector P Q horth
        (s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E) *
      toHermitianQubitOperator E := by
  have h := pauli_mul_syndromeProjector (binaryCSSParityCheckGenerators P Q)
    (checks_commute P Q horth) E (syndromeOutcome _ s)
  rw [transport_add P Q horth E s] at h
  exact h

/-- Add an actual image word within its original row-image carrier. -/
def rangeShift (x : Word (ZMod 2) ι) (u : LinearMap.range P) : LinearMap.range P :=
  u + ⟨P x, ⟨x, rfl⟩⟩

@[simp] theorem rangeShift_val (x : Word (ZMod 2) ι) (u : LinearMap.range P) :
    (rangeShift P x u).val = u.val + P x := rfl

theorem rangeShift_involutive (x : Word (ZMod 2) ι) :
    Function.Involutive (rangeShift P x) := by
  intro u
  apply Subtype.ext
  funext j
  change (u.val j + P x j) + P x j = u.val j
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

def rangeShiftEquiv (x : Word (ZMod 2) ι) : LinearMap.range P ≃ LinearMap.range P where
  toFun := rangeShift P x
  invFun := rangeShift P x
  left_inv := rangeShift_involutive P x
  right_inv := rangeShift_involutive P x

/-- The two classical images translate independently for an arbitrary Pauli. -/
def jointTranslation (E : Binary ι) : Realizable P Q ≃ Realizable P Q :=
  Equiv.prodCongr (rangeShiftEquiv P E.vector.xPart) (rangeShiftEquiv Q E.vector.zPart)

@[simp] theorem jointTranslation_apply (E : Binary ι) (s : Realizable P Q) :
    jointTranslation P Q E s =
      (rangeShift P E.vector.xPart s.1, rangeShift Q E.vector.zPart s.2) := rfl

theorem jointTranslation_involutive (E : Binary ι) :
    Function.Involutive (jointTranslation P Q E) := by
  intro s
  apply Prod.ext
  · exact rangeShift_involutive P E.vector.xPart s.1
  · exact rangeShift_involutive Q E.vector.zPart s.2

include horth in
theorem embedding_translation (E : Binary ι) (s : Realizable P Q) :
    realizableEmbedding P Q (jointTranslation P Q E s) =
      realizableEmbedding P Q s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E := by
  rw [binaryCSSSyndrome_eq_classicalSyndromes P Q horth E]
  funext j
  cases j <;> rfl

/-- Atom transport uses the Hermitian physical Pauli, including its phase. -/
theorem pauli_mul_realizable_projector (E : Binary ι) (s : Realizable P Q) :
    toHermitianQubitOperator E * projector P Q horth (realizableEmbedding P Q s) =
      projector P Q horth (realizableEmbedding P Q (jointTranslation P Q E s)) *
        toHermitianQubitOperator E := by
  rw [embedding_translation P Q horth]
  exact pauli_mul_projector_add P Q horth E _

def translatedSelection (E : Binary ι) (A : Finset (Realizable P Q)) :
    Finset (Realizable P Q) := A.map (jointTranslation P Q E).toEmbedding

theorem translatedSelection_image (E : Binary ι) (A : Finset (Realizable P Q)) :
    translatedSelection P Q E A = A.image (jointTranslation P Q E) := by
  ext a
  simp only [translatedSelection, Finset.mem_map, Finset.mem_image]
  constructor <;> rintro ⟨b, hb, he⟩ <;> exact ⟨b, hb, he⟩

theorem pauli_mul_selected (E : Binary ι) (A : Finset (Realizable P Q)) :
    toHermitianQubitOperator E * selectedProjector P Q horth A =
      selectedProjector P Q horth (translatedSelection P Q E A) *
        toHermitianQubitOperator E := by
  simp only [selectedProjector, translatedSelection, Finset.sum_map, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact pauli_mul_realizable_projector P Q horth E a

theorem pauli_conjugate_selected (E : Binary ι) (A : Finset (Realizable P Q)) :
    toHermitianQubitOperator E * selectedProjector P Q horth A *
        toHermitianQubitOperator E =
      selectedProjector P Q horth (translatedSelection P Q E A) := by
  rw [pauli_mul_selected, mul_assoc, toHermitianQubitOperator_square, mul_one]

/-- Rectangular selections translate componentwise, with no nonempty hypothesis. -/
theorem translatedSelection_product (E : Binary ι)
    (A : Finset (LinearMap.range P)) (B : Finset (LinearMap.range Q)) :
    translatedSelection P Q E (A ×ˢ B) =
      (A.map (rangeShiftEquiv P E.vector.xPart).toEmbedding) ×ˢ
      (B.map (rangeShiftEquiv Q E.vector.zPart).toEmbedding) := by
  ext s
  simp only [translatedSelection, Finset.mem_map, Finset.mem_product]
  constructor
  · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
    exact ⟨⟨a.1, ha, rfl⟩, ⟨a.2, hb, rfl⟩⟩
  · rintro ⟨⟨u, hu, heu⟩, ⟨v, hv, hev⟩⟩
    refine ⟨(u,v), ⟨hu,hv⟩, ?_⟩
    apply Prod.ext
    · exact heu
    · exact hev

end QEC.Coding.CSSGibbs
