import QEC.Coding.CSS.GibbsSyndrome.Gibbs

/-! # Finite selections of the actual CSS joint eigenspaces

These are operator sums on the original register. No stability or protection
property is ascribed to a selection. Exact rectangular Gibbs probabilities
are consequences of the actual CSS product law, not assumptions.
-/

noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
local instance : Fintype (LinearMap.range P) := Fintype.ofFinite _
local instance : Fintype (LinearMap.range Q) := Fintype.ofFinite _

/-- A selection in the literal realizable pair carrier. -/
def selectedProjector (A : Finset (Realizable P Q)) : Operator (Qubit.QubitRegister ι) :=
  ∑ a ∈ A, projector P Q horth (realizableEmbedding P Q a)

theorem selectedProjector_eq_badProjector (A : Finset (Realizable P Q)) :
    selectedProjector P Q horth A = badProjector P Q horth (A.map (realizableEmbedding P Q)) := by
  simp only [selectedProjector, badProjector, Finset.sum_map]

theorem projector_commute (s t : Word (ZMod 2) (Sum κP κQ)) :
    Commute (projector P Q horth s) (projector P Q horth t) := by
  by_cases h : s = t
  · subst t; exact Commute.refl _
  · show _ * _ = _ * _
    rw [projector_mul_of_ne P Q horth s t h,
      projector_mul_of_ne P Q horth t s (Ne.symm h)]

theorem atom_mul_selected (a : Realizable P Q) (A : Finset (Realizable P Q)) :
    projector P Q horth (realizableEmbedding P Q a) * selectedProjector P Q horth A =
      if a ∈ A then projector P Q horth (realizableEmbedding P Q a) else 0 := by
  simp only [selectedProjector, Finset.mul_sum]
  by_cases ha : a ∈ A
  · rw [if_pos ha, Finset.sum_eq_single a]
    · exact projector_square P Q horth _
    · intro b _ hb
      apply projector_mul_of_ne P Q horth
      intro h
      exact hb (((realizableEmbedding P Q).injective h).symm)
    · intro h; exact (h ha).elim
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b hb
    apply projector_mul_of_ne P Q horth
    intro h
    apply ha
    exact ((realizableEmbedding P Q).injective h).symm ▸ hb

theorem selectedProjector_mul (A B : Finset (Realizable P Q)) :
    selectedProjector P Q horth A * selectedProjector P Q horth B =
      selectedProjector P Q horth (A ∩ B) := by
  change (∑ a ∈ A, projector P Q horth (realizableEmbedding P Q a)) * _ = _
  rw [Finset.sum_mul]
  simp_rw [atom_mul_selected]
  have hi : A ∩ B = A.filter (fun a => a ∈ B) := by ext a; simp
  rw [selectedProjector, hi, Finset.sum_filter]

theorem selectedProjector_starProjection (A : Finset (Realizable P Q)) :
    IsStarProjection (selectedProjector P Q horth A) := by
  rw [selectedProjector_eq_badProjector]
  refine ⟨badProjector_square P Q horth _, ?_⟩
  change LinearMap.adjoint (badProjector P Q horth _) = _
  exact badProjector_adjoint P Q horth _

theorem selectedProjector_total : selectedProjector P Q horth Finset.univ = 1 := by
  have hs : (∑ s ∈ realizableSyndromes P Q, projector P Q horth s) =
      ∑ s, projector P Q horth s := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    exact projector_eq_zero_of_not_realizable P Q horth s hs
  calc
    _ = ∑ s ∈ realizableSyndromes P Q, projector P Q horth s := by
      simp only [selectedProjector, realizableSyndromes, Finset.sum_map]
    _ = 1 := hs.trans (sum_projector P Q horth)

theorem selectedProjector_compl (A : Finset (Realizable P Q)) :
    selectedProjector P Q horth Aᶜ = 1 - selectedProjector P Q horth A := by
  apply eq_sub_iff_add_eq.mpr
  change (∑ a ∈ Aᶜ, projector P Q horth (realizableEmbedding P Q a)) +
    (∑ a ∈ A, projector P Q horth (realizableEmbedding P Q a)) = _
  rw [Finset.sum_compl_add_sum]
  exact selectedProjector_total P Q horth

theorem projector_commute_selected (s : Word (ZMod 2) (Sum κP κQ))
    (A : Finset (Realizable P Q)) :
    Commute (projector P Q horth s) (selectedProjector P Q horth A) := by
  unfold selectedProjector
  apply Commute.sum_right
  intro a _
  exact projector_commute P Q horth s _

theorem hamiltonian_commute_selected (A : Finset (Realizable P Q)) :
    Commute (hamiltonian P Q) (selectedProjector P Q horth A) := by
  rw [hamiltonian_syndrome_resolution P Q horth]
  apply Commute.sum_left
  intro s _
  exact (projector_commute_selected P Q horth s A).smul_left _

theorem gibbs_commute_selected (β : ℝ) (A : Finset (Realizable P Q)) :
    Commute (gibbs P Q β).toOperator (selectedProjector P Q horth A) := by
  rw [gibbs_normalized_exp, thermalExponential_resolution P Q horth]
  apply Commute.smul_left
  apply Commute.sum_left
  intro s _
  exact (projector_commute_selected P Q horth s A).smul_left _

theorem gibbs_selected_trace (β : ℝ) (A : Finset (Realizable P Q)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι)
      ((gibbs P Q β).toOperator * selectedProjector P Q horth A) =
      ((∑ a ∈ A, rowProbability P (2*β) a.1 * rowProbability Q (2*β) a.2 : ℝ) : ℂ) := by
  simp only [selectedProjector, Finset.mul_sum, map_sum, gibbs_joint_trace,
    realizableEmbedding_apply, jointProbability_product, Complex.ofReal_sum, Complex.ofReal_mul]

theorem gibbs_rectangle_trace (β : ℝ)
    (A : Finset (LinearMap.range P)) (B : Finset (LinearMap.range Q)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι)
      ((gibbs P Q β).toOperator * selectedProjector P Q horth (A ×ˢ B)) =
      (((∑ a ∈ A, rowProbability P (2*β) a) *
        (∑ b ∈ B, rowProbability Q (2*β) b) : ℝ) : ℂ) := by
  rw [gibbs_selected_trace]
  congr 1
  simp only [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem rowProbability_nonneg (t : ℝ) (u : LinearMap.range P) :
    0 ≤ rowProbability P t u :=
  div_nonneg (Real.exp_pos _).le (rowPartition_pos P t).le

theorem rowProbability_selection_bounds (t : ℝ) (A : Finset (LinearMap.range P)) :
    0 ≤ ∑ u ∈ A, rowProbability P t u ∧ (∑ u ∈ A, rowProbability P t u) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun u _ => rowProbability_nonneg P t u), ?_⟩
  calc
    _ ≤ ∑ u, rowProbability P t u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun u _ _ => rowProbability_nonneg P t u)
    _ = 1 := sum_rowProbability P t

theorem rowProbability_compl (t : ℝ) (A : Finset (LinearMap.range P)) :
    (∑ u ∈ Aᶜ, rowProbability P t u) = 1 - ∑ u ∈ A, rowProbability P t u := by
  apply eq_sub_iff_add_eq.mpr
  rw [Finset.sum_compl_add_sum, sum_rowProbability]

end QEC.Coding.CSSGibbs
