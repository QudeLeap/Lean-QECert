import QEC.Coding.CSS.GibbsSyndrome.Translation
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.TwoSectorBadProjector
import Mathlib.Tactic

/-!
# Fixed binary coboundary containment in the actual finite Gibbs images

Project-derived internal refinement of registered BDL26 v1 paper.tex:3747–3755
(SHA256 66d1927b20efccb757da40af3d291e4738c60054799812393e0a739abcc73e5b).
The fixed word belongs to the literal image; no decoder witness or failure
cover is constructed. All temperatures are real. Actual X-error uses Z rows,
actual Z-error uses X rows, and the physical syndrome temperature is 2β.
-/
noncomputable section
namespace QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
local instance imageFintype (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) :
    Fintype (LinearMap.range P) := Fintype.ofFinite _

/-- Binary cancellation removes exactly the contained coordinates. -/
theorem support_remove (s τ : Word (ZMod 2) K)
    (h : hammingSupport τ ⊆ hammingSupport s) :
    hammingSupport (s+τ) = hammingSupport s \ hammingSupport τ := by
  ext j
  have hj : τ j≠0 → s j≠0 := by
    intro hn
    exact (Finset.mem_filter.mp (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))).2
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, Pi.add_apply]
  generalize τ j = a at hj ⊢
  generalize s j = b at hj ⊢
  fin_cases a <;> fin_cases b
  · change ((0 : ZMod 2)+0 ≠ 0) ↔ ((0 : ZMod 2) ≠ 0) ∧ ¬ ((0 : ZMod 2) ≠ 0)
    constructor
    · intro hn
      exact False.elim (hn (zero_add (0 : ZMod 2)))
    · rintro ⟨hn,_⟩
      exact False.elim (hn rfl)
  · change ((1 : ZMod 2)+0 ≠ 0) ↔ ((1 : ZMod 2) ≠ 0) ∧ ¬ ((0 : ZMod 2) ≠ 0)
    constructor
    · intro hn
      refine ⟨?_,?_⟩
      · intro he
        exact hn ((add_zero (1 : ZMod 2)).trans he)
      · intro h00
        exact h00 rfl
    · rintro ⟨hn,_⟩
      intro he
      exact hn ((add_zero (1 : ZMod 2)).symm.trans he)
  · change ((1 : ZMod 2) ≠ 0 → (0 : ZMod 2) ≠ 0) at hj
    change ((0 : ZMod 2)+1 ≠ 0) ↔ ((0 : ZMod 2) ≠ 0) ∧ ¬ ((1 : ZMod 2) ≠ 0)
    constructor
    · intro hn
      have h10 : (1 : ZMod 2) ≠ 0 := by
        intro he
        exact hn ((zero_add (1 : ZMod 2)).trans he)
      exact False.elim (hj h10 rfl)
    · rintro ⟨h00,_⟩
      exact False.elim (h00 rfl)
  · change ((1 : ZMod 2)+1 ≠ 0) ↔ ((1 : ZMod 2) ≠ 0) ∧ ¬ ((1 : ZMod 2) ≠ 0)
    constructor
    · intro hn
      exact False.elim (hn (CharTwo.add_self_eq_zero (1 : ZMod 2)))
    · rintro ⟨hn,hnot⟩
      exact False.elim (hnot hn)

/-- Exact energy removal, not merely a Hamming triangle inequality. -/
theorem weight_remove (s τ : Word (ZMod 2) K)
    (h : hammingSupport τ ⊆ hammingSupport s) :
    HammingWeight s = HammingWeight τ + HammingWeight (s+τ) := by
  change (hammingSupport s).card = (hammingSupport τ).card + (hammingSupport (s+τ)).card
  rw [support_remove s τ h]
  exact (Finset.card_sdiff_add_card_eq_card h).symm.trans (Nat.add_comm _ _)

/-- Addition inside the ORIGINAL image subtype; no preimage oracle. -/
def shift (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ s : LinearMap.range P) : LinearMap.range P := s+τ

theorem shift_involutive (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Function.Involutive (shift P τ) := by
  intro s
  apply Subtype.ext
  funext j
  change (s.val j+τ.val j)+τ.val j=s.val j
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

def shiftEquiv (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : LinearMap.range P ≃ LinearMap.range P where
  toFun := shift P τ
  invFun := shift P τ
  left_inv := shift_involutive P τ
  right_inv := shift_involutive P τ

theorem shift_injective (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Function.Injective (shift P τ) :=
  (shift_involutive P τ).injective

/-- The literal containment event on the finite image. -/
def containment (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Finset (LinearMap.range P) :=
  Finset.univ.filter fun s => hammingSupport τ.val ⊆ hammingSupport s.val

theorem mem_containment (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ s : LinearMap.range P) :
    s∈containment P τ ↔ hammingSupport τ.val ⊆ hammingSupport s.val := by
  simp only [containment, Finset.mem_filter, Finset.mem_univ, true_and]

def translated (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Finset (LinearMap.range P) :=
  (containment P τ).map (shiftEquiv P τ).toEmbedding

theorem translated_eq_image (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) :
    translated P τ = (containment P τ).image (shift P τ) := by
  ext s
  simp only [translated, Finset.mem_map, Finset.mem_image]
  constructor <;> rintro ⟨u,hu,he⟩ <;> exact ⟨u,hu,he⟩

def mass (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (A : Finset (LinearMap.range P)) : ℝ :=
  ∑ s ∈ A, CSSGibbs.rowProbability P t s

theorem mass_bounds (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (A : Finset (LinearMap.range P)) :
    0 ≤ mass P t A ∧ mass P t A ≤ 1 :=
  CSSGibbs.rowProbability_selection_bounds P t A

/-- The exact probability ratio uses the SAME original partition function. -/
theorem probability_factor (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ s : LinearMap.range P) (hs : s∈containment P τ) :
    CSSGibbs.rowProbability P t s =
      Real.exp (-t*(HammingWeight τ.val : ℝ)) * CSSGibbs.rowProbability P t (shift P τ s) := by
  have hw := weight_remove s.val τ.val ((mem_containment P τ s).mp hs)
  unfold CSSGibbs.rowProbability
  change Real.exp (-t*(HammingWeight s.val : ℝ)) / CSSGibbs.rowPartition P t =
    Real.exp (-t*(HammingWeight τ.val : ℝ)) *
      (Real.exp (-t*(HammingWeight (s.val+τ.val) : ℝ)) / CSSGibbs.rowPartition P t)
  rw [hw, Nat.cast_add, mul_add, Real.exp_add]
  ring

/-- Exact normalized translated mass for EVERY real temperature. -/
theorem containment_mass_exact (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ : LinearMap.range P) :
    mass P t (containment P τ) =
      Real.exp (-t*(HammingWeight τ.val : ℝ)) * mass P t (translated P τ) := by
  unfold mass translated
  rw [Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact probability_factor P t τ s hs

theorem containment_mass_le (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ : LinearMap.range P) :
    mass P t (containment P τ) ≤ Real.exp (-t*(HammingWeight τ.val : ℝ)) := by
  rw [containment_mass_exact]
  exact (mul_le_mul_of_nonneg_left (mass_bounds P t (translated P τ)).2
    (Real.exp_pos _).le).trans_eq (mul_one _)

theorem containment_zero (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) :
    containment P 0 = Finset.univ := by
  ext s
  simp [containment, hammingSupport_zero]

theorem zero_mass (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) (t : ℝ) :
    mass P t (containment P 0)=1 := by
  rw [containment_zero]
  exact CSSGibbs.sum_rowProbability P t

/-- Literal finite union; overlap is retained, not counted as disjointness. -/
def familyEvent (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (W : Finset (LinearMap.range P)) : Finset (LinearMap.range P) :=
  W.biUnion (containment P)

theorem mem_familyEvent (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (W : Finset (LinearMap.range P)) (s : LinearMap.range P) :
    s∈familyEvent P W ↔ ∃ τ∈W, hammingSupport τ.val ⊆ hammingSupport s.val := by
  simp only [familyEvent, Finset.mem_biUnion, mem_containment]

private theorem mass_union_le (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (A B : Finset (LinearMap.range P)) :
    mass P t (A∪B) ≤ mass P t A + mass P t B := by
  have he := Finset.sum_union_inter (s₁:=A) (s₂:=B)
    (f:=fun s => CSSGibbs.rowProbability P t s)
  change mass P t (A∪B)+mass P t (A∩B)=mass P t A+mass P t B at he
  have hn := (mass_bounds P t (A∩B)).1
  linarith

theorem family_mass_le_sum (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (W : Finset (LinearMap.range P)) :
    mass P t (familyEvent P W) ≤ ∑ τ∈W, mass P t (containment P τ) := by
  induction W using Finset.induction_on with
  | empty => simp [familyEvent,mass]
  | @insert τ W hτ ih =>
    have hf : familyEvent P (insert τ W)=containment P τ ∪ familyEvent P W := by
      simp only [familyEvent,Finset.biUnion_insert]
    rw [hf,Finset.sum_insert hτ]
    have hu := mass_union_le P t (containment P τ) (familyEvent P W)
    linarith

theorem family_mass_le_exp (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (W : Finset (LinearMap.range P)) :
    mass P t (familyEvent P W) ≤ ∑ τ∈W, Real.exp (-t*(HammingWeight τ.val : ℝ)) := by
  exact (family_mass_le_sum P t W).trans
    (Finset.sum_le_sum (fun τ _ => containment_mass_le P t τ))

theorem empty_family_mass (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) (t : ℝ) :
    mass P t (familyEvent P ∅)=0 := by simp [familyEvent,mass]

end QEC.Coding.FixedCoboundaryGibbs

namespace QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
local instance xImageFintype (S : OddScale) (n : Nat) : Fintype (XImage S n) := Fintype.ofFinite _
local instance zImageFintype (S : OddScale) (n : Nat) : Fintype (ZImage S n) := Fintype.ofFinite _

def xContainment (S : OddScale) (n : Nat) (τ : XImage S n) :=
  FixedCoboundaryGibbs.containment (zSyndrome S n) τ

def zContainment (S : OddScale) (n : Nat) (τ : ZImage S n) :=
  FixedCoboundaryGibbs.containment (xSyndrome S n) τ

def xFamily (S : OddScale) (n : Nat) (W : Finset (XImage S n)) :=
  FixedCoboundaryGibbs.familyEvent (zSyndrome S n) W

def zFamily (S : OddScale) (n : Nat) (W : Finset (ZImage S n)) :=
  FixedCoboundaryGibbs.familyEvent (xSyndrome S n) W

theorem x_mass_exact (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    pX S n β (xContainment S n τ) =
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) *
        pX S n β (FixedCoboundaryGibbs.translated (zSyndrome S n) τ) :=
  FixedCoboundaryGibbs.containment_mass_exact (zSyndrome S n) (2*β) τ

theorem z_mass_exact (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    pZ S n β (zContainment S n τ) =
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) *
        pZ S n β (FixedCoboundaryGibbs.translated (xSyndrome S n) τ) :=
  FixedCoboundaryGibbs.containment_mass_exact (xSyndrome S n) (2*β) τ

theorem x_mass_le (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    pX S n β (xContainment S n τ) ≤ Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) :=
  FixedCoboundaryGibbs.containment_mass_le (zSyndrome S n) (2*β) τ

theorem z_mass_le (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    pZ S n β (zContainment S n τ) ≤ Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) :=
  FixedCoboundaryGibbs.containment_mass_le (xSyndrome S n) (2*β) τ

theorem x_family_le (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (XImage S n)) :
    pX S n β (xFamily S n W) ≤ ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) :=
  FixedCoboundaryGibbs.family_mass_le_exp (zSyndrome S n) (2*β) W

theorem z_family_le (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    pZ S n β (zFamily S n W) ≤ ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) :=
  FixedCoboundaryGibbs.family_mass_le_exp (xSyndrome S n) (2*β) W

def xSelected (S : OddScale) (n : Nat) (A : Finset (XImage S n)) :
    Operator (Qubit.QubitRegister (Physical S n)) := selected S n (A ×ˢ Finset.univ)

def zSelected (S : OddScale) (n : Nat) (A : Finset (ZImage S n)) :
    Operator (Qubit.QubitRegister (Physical S n)) := selected S n (Finset.univ ×ˢ A)

/-- Full complex trace, not just its real part. -/
theorem x_selected_trace (S : OddScale) (n : Nat) (β : ℝ) (A : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n A) = ((pX S n β A : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (A ×ˢ Finset.univ)) = _
  rw [CSSGibbs.gibbs_rectangle_trace,CSSGibbs.sum_rowProbability,mul_one]
  rfl

theorem z_selected_trace (S : OddScale) (n : Nat) (β : ℝ) (A : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n A) = ((pZ S n β A : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (Finset.univ ×ˢ A)) = _
  rw [CSSGibbs.gibbs_rectangle_trace,CSSGibbs.sum_rowProbability,one_mul]
  rfl

theorem x_containment_trace (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xContainment S n τ)) =
      ((pX S n β (xContainment S n τ) : ℝ) : ℂ) := x_selected_trace S n β _

theorem z_containment_trace (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zContainment S n τ)) =
      ((pZ S n β (zContainment S n τ) : ℝ) : ℂ) := z_selected_trace S n β _

theorem x_containment_trace_bound (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xContainment S n τ))).re ≤
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by
  rw [x_containment_trace,Complex.ofReal_re]
  exact x_mass_le S n β τ

theorem z_containment_trace_bound (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zContainment S n τ))).re ≤
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by
  rw [z_containment_trace,Complex.ofReal_re]
  exact z_mass_le S n β τ

theorem x_family_trace (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xFamily S n W)) =
      ((pX S n β (xFamily S n W) : ℝ) : ℂ) := x_selected_trace S n β _

theorem z_family_trace (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zFamily S n W)) =
      ((pZ S n β (zFamily S n W) : ℝ) : ℂ) := z_selected_trace S n β _

theorem x_family_trace_bound (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (XImage S n)) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xFamily S n W))).re ≤
      ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by
  rw [x_family_trace,Complex.ofReal_re]
  exact x_family_le S n β W

theorem z_family_trace_bound (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zFamily S n W))).re ≤
      ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by
  rw [z_family_trace,Complex.ofReal_re]
  exact z_family_le S n β W

end QEC.Coding.BDL26CoboundaryContainment
