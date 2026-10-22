import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Gibbs
import QEC.Coding.CSS.GibbsSyndrome.Selection

/-!
# Actual selected two-sector projectors and their Gibbs bad weight

BDL26, paper.tex:3810–3818, combines the two sector bad weights. The exact
inclusion-exclusion formula below is derived from the proved physical CSS
Gibbs product law at syndrome temperature 2β. Arbitrary selections are not
asserted to be decoder-stable or protected. CLBT's actual operator tail is
used, preserving the original physical register and full labelled Hamiltonian.
-/

noncomputable section
namespace QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)

/-- X-error syndromes are actual Z-row images. -/
abbrev XImage := LinearMap.range (zSyndrome S n)
/-- Z-error syndromes are actual X-row images. -/
abbrev ZImage := LinearMap.range (xSyndrome S n)
local instance : Fintype (XImage S n) := Fintype.ofFinite _
local instance : Fintype (ZImage S n) := Fintype.ofFinite _

abbrev JointImage := XImage S n × ZImage S n
abbrev selected (A : Finset (JointImage S n)) : Operator (Qubit.QubitRegister (Physical S n)) :=
  CSSGibbs.selectedProjector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n) A

def goodX (BX : Finset (XImage S n)) : Finset (JointImage S n) := BXᶜ ×ˢ Finset.univ
def goodZ (BZ : Finset (ZImage S n)) : Finset (JointImage S n) := Finset.univ ×ˢ BZᶜ
def goodJoint (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Finset (JointImage S n) := BXᶜ ×ˢ BZᶜ

def PX (BX : Finset (XImage S n)) := selected S n (goodX S n BX)
def PZ (BZ : Finset (ZImage S n)) := selected S n (goodZ S n BZ)
def Pjoint (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :=
  selected S n (goodJoint S n BX BZ)

/-- Actual visible joint words with at least one selected bad sector. -/
def badUnionWords (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Finset (Word (ZMod 2) (Sum (ZLabel S n) (XLabel S n))) :=
  ((goodJoint S n BX BZ)ᶜ).map (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n))

theorem badUnionWords_mem (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n))
    (u : XImage S n) (v : ZImage S n) :
    CSSGibbs.joinSyndrome u.val v.val ∈ badUnionWords S n BX BZ ↔ u ∈ BX ∨ v ∈ BZ := by
  change CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) (u,v) ∈ _ ↔ _
  unfold badUnionWords
  constructor
  · intro hm
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hm
    have heq : a = (u,v) :=
      (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n)).injective he
    subst a
    simpa only [goodJoint, Finset.mem_compl, Finset.mem_product, not_and_or, not_not] using ha
  · intro hm
    apply Finset.mem_map.mpr
    refine ⟨(u,v), ?_, rfl⟩
    simpa only [goodJoint, Finset.mem_compl, Finset.mem_product, not_and_or, not_not] using hm

theorem projection_X (BX : Finset (XImage S n)) : IsStarProjection (PX S n BX) :=
  CSSGibbs.selectedProjector_starProjection _ _ (row_orthogonal S n) _
theorem projection_Z (BZ : Finset (ZImage S n)) : IsStarProjection (PZ S n BZ) :=
  CSSGibbs.selectedProjector_starProjection _ _ (row_orthogonal S n) _
theorem projection_joint (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    IsStarProjection (Pjoint S n BX BZ) :=
  CSSGibbs.selectedProjector_starProjection _ _ (row_orthogonal S n) _
theorem projection_bad (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    IsStarProjection (1 - Pjoint S n BX BZ) := (projection_joint S n BX BZ).one_sub

theorem product_XZ (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    PX S n BX * PZ S n BZ = Pjoint S n BX BZ := by
  change CSSGibbs.selectedProjector _ _ _ _ * CSSGibbs.selectedProjector _ _ _ _ = _
  rw [CSSGibbs.selectedProjector_mul]
  congr 1
  ext a
  simp [goodX, goodZ, goodJoint]

theorem product_ZX (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    PZ S n BZ * PX S n BX = Pjoint S n BX BZ := by
  change CSSGibbs.selectedProjector _ _ _ _ * CSSGibbs.selectedProjector _ _ _ _ = _
  rw [CSSGibbs.selectedProjector_mul]
  congr 1
  ext a
  simp [goodX, goodZ, goodJoint, and_comm]

theorem commute_XZ (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (PX S n BX) (PZ S n BZ) :=
  (product_XZ S n BX BZ).trans (product_ZX S n BX BZ).symm

theorem bad_complement (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    1 - Pjoint S n BX BZ =
      CSSGibbs.badProjector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
        (badUnionWords S n BX BZ) := by
  unfold badUnionWords
  rw [← CSSGibbs.selectedProjector_eq_badProjector,
    CSSGibbs.selectedProjector_compl]
  rfl

theorem hamiltonian_commute (A : Finset (JointImage S n)) :
    Commute (hamiltonian S n) (selected S n A) :=
  CSSGibbs.hamiltonian_commute_selected _ _ (row_orthogonal S n) A
theorem gibbs_commute (β : ℝ) (A : Finset (JointImage S n)) :
    Commute (gibbs S n β).toOperator (selected S n A) :=
  CSSGibbs.gibbs_commute_selected _ _ (row_orthogonal S n) β A

theorem hamiltonian_commute_bad (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (hamiltonian S n) (1 - Pjoint S n BX BZ) :=
  (Commute.one_right _).sub_right (hamiltonian_commute S n (goodJoint S n BX BZ))
theorem gibbs_commute_bad (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (gibbs S n β).toOperator (1 - Pjoint S n BX BZ) :=
  (Commute.one_right _).sub_right (gibbs_commute S n β (goodJoint S n BX BZ))

def pX (β : ℝ) (BX : Finset (XImage S n)) : ℝ :=
  ∑ u ∈ BX, CSSGibbs.rowProbability (zSyndrome S n) (2*β) u
def pZ (β : ℝ) (BZ : Finset (ZImage S n)) : ℝ :=
  ∑ v ∈ BZ, CSSGibbs.rowProbability (xSyndrome S n) (2*β) v

theorem pX_bounds (β : ℝ) (BX : Finset (XImage S n)) :
    0 ≤ pX S n β BX ∧ pX S n β BX ≤ 1 :=
  CSSGibbs.rowProbability_selection_bounds _ (2*β) BX
theorem pZ_bounds (β : ℝ) (BZ : Finset (ZImage S n)) :
    0 ≤ pZ S n β BZ ∧ pZ S n β BZ ≤ 1 :=
  CSSGibbs.rowProbability_selection_bounds _ (2*β) BZ

theorem trace_X (β : ℝ) (BX : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * PX S n BX) = ((1 - pX S n β BX : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (BXᶜ ×ˢ Finset.univ)) = _
  rw [CSSGibbs.gibbs_rectangle_trace, CSSGibbs.rowProbability_compl, CSSGibbs.sum_rowProbability]
  simp only [mul_one, pX]

theorem trace_Z (β : ℝ) (BZ : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * PZ S n BZ) = ((1 - pZ S n β BZ : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (Finset.univ ×ˢ BZᶜ)) = _
  rw [CSSGibbs.gibbs_rectangle_trace, CSSGibbs.rowProbability_compl, CSSGibbs.sum_rowProbability]
  simp only [one_mul, pZ]

theorem trace_joint (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * Pjoint S n BX BZ) =
      (((1-pX S n β BX)*(1-pZ S n β BZ) : ℝ) : ℂ) := by
  change LinearMap.trace ℂ _ (_ * CSSGibbs.selectedProjector _ _ _ (BXᶜ ×ˢ BZᶜ)) = _
  rw [CSSGibbs.gibbs_rectangle_trace, CSSGibbs.rowProbability_compl, CSSGibbs.rowProbability_compl]
  rfl

theorem trace_bad (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * (1-Pjoint S n BX BZ)) =
      ((pX S n β BX+pZ S n β BZ-pX S n β BX*pZ S n β BZ : ℝ) : ℂ) := by
  rw [mul_sub, mul_one, map_sub, (gibbs S n β).trace_one, trace_joint]
  push_cast
  ring

theorem tail_exact (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) =
      pX S n β BX+pZ S n β BZ-pX S n β BX*pZ S n β BZ := by
  unfold clbtGibbsTailMass
  rw [← (gibbs_commute_bad S n β BX BZ).eq, trace_bad, Complex.ofReal_re]

theorem tail_nonneg (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    0 ≤ clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) := by
  rw [tail_exact]
  have hx := pX_bounds S n β BX
  have hz := pZ_bounds S n β BZ
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hz.2)]

theorem tail_union_bound (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) ≤ pX S n β BX+pZ S n β BZ := by
  rw [tail_exact]
  exact sub_le_self _ (mul_nonneg (pX_bounds S n β BX).1 (pZ_bounds S n β BZ).1)

theorem tail_two_bounds (β εX εZ : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n))
    (hX : pX S n β BX ≤ εX) (hZ : pZ S n β BZ ≤ εZ) :
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) ≤ εX+εZ :=
  (tail_union_bound S n β BX BZ).trans (add_le_add hX hZ)

theorem joint_empty : Pjoint S n ∅ ∅ = 1 := by
  change CSSGibbs.selectedProjector _ _ _ _ = _
  have h : goodJoint S n ∅ ∅ = Finset.univ := by ext a; simp [goodJoint]
  rw [h, CSSGibbs.selectedProjector_total]
theorem joint_all : Pjoint S n Finset.univ Finset.univ = 0 := by
  simp [Pjoint, goodJoint, selected, CSSGibbs.selectedProjector]

theorem even_tail_exact (k : Nat) (β : ℝ)
    (BX : Finset (XImage S (2*k))) (BZ : Finset (ZImage S (2*k))) :
    clbtGibbsTailMass (Pjoint S (2*k) BX BZ) (gibbs S (2*k) β) =
      pX S (2*k) β BX+pZ S (2*k) β BZ-pX S (2*k) β BX*pZ S (2*k) β BZ :=
  tail_exact S (2*k) β BX BZ
theorem even_tail_two_bounds (k : Nat) (β εX εZ : ℝ)
    (BX : Finset (XImage S (2*k))) (BZ : Finset (ZImage S (2*k)))
    (hX : pX S (2*k) β BX ≤ εX) (hZ : pZ S (2*k) β BZ ≤ εZ) :
    clbtGibbsTailMass (Pjoint S (2*k) BX BZ) (gibbs S (2*k) β) ≤ εX+εZ :=
  tail_two_bounds S (2*k) β εX εZ BX BZ hX hZ

end QEC.Coding.BDL26TwoSectorBadProjector
