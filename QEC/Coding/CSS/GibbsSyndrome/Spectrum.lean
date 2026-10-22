import QEC.Coding.CSS.GibbsSyndrome.Projectors

/-! # Equal multiplicities of actual CSS syndrome eigenspaces -/
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

/-- Rank always means the dimension of the actual linear-map image. -/
def checkRank : Nat := Module.finrank (ZMod 2) (LinearMap.range P)

theorem checkRank_eq_rowDimension : checkRank P = Dimension (parityCheckRowCode P) := by
  have h := (parityCheckRowCode P).dimension_add_dual_dimension_eq_length
  rw [parityCheckRowCode_dual_eq_kernelCode] at h
  have hk := LinearMap.finrank_range_add_finrank_ker P
  rw [finrank_word_eq_length] at hk
  change Dimension (parityCheckRowCode P) + Module.finrank (ZMod 2) (LinearMap.ker P) =
    Length (ZMod 2) ι at h
  unfold checkRank
  omega

include horth in
theorem checkRanks_le : checkRank P + checkRank Q ≤ Fintype.card ι := by
  have hle := Submodule.finrank_mono
    ((parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).mp horth)
  have hd := (parityCheckRowCode Q).dimension_add_dual_dimension_eq_length
  rw [checkRank_eq_rowDimension P, checkRank_eq_rowDimension Q]
  change Dimension (parityCheckRowCode P) ≤ Dimension (parityCheckRowCode Q).dual at hle
  change Dimension (parityCheckRowCode Q) + Dimension (parityCheckRowCode Q).dual =
    Fintype.card ι at hd
  omega

/-- The common eigenspace multiplicity is derived from the semantic CSS carrier. -/
def multiplicity : Nat := 2 ^ (Fintype.card ι - checkRank P - checkRank Q)

theorem multiplicity_pos : 0 < multiplicity P Q := by
  exact pow_pos (by norm_num) _

theorem sector_zero_finrank : Module.finrank ℂ (sector P Q horth 0) = multiplicity P Q := by
  rw [sector_zero_eq_code]
  rw [binaryCSSQuantumCodeOfDualLe_finrank_carrier]
  rw [multiplicity, checkRank_eq_rowDimension P, checkRank_eq_rowDimension Q]
  congr 1
  change Fintype.card ι - Dimension (parityCheckRowCode Q) - Dimension (parityCheckRowCode P) = _
  omega

theorem sector_realizable_finrank (u : LinearMap.range P) (v : LinearMap.range Q) :
    Module.finrank ℂ (sector P Q horth (joinSyndrome u.val v.val)) = multiplicity P Q := by
  have h := trace_projector_realizable P Q horth u v
  rw [trace_projector, trace_projector, sector_zero_finrank] at h
  exact_mod_cast h

theorem card_realizable : Fintype.card (Realizable P Q) = 2 ^ (checkRank P + checkRank Q) := by
  rw [Fintype.card_prod, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range P),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range Q), ZMod.card, pow_add]
  rfl

include horth in
theorem multiplicity_mul_card_realizable :
    multiplicity P Q * Fintype.card (Realizable P Q) = 2 ^ Fintype.card ι := by
  rw [card_realizable, multiplicity, ← pow_add]
  congr 1
  have h := checkRanks_le P Q horth
  omega

def realizableEmbedding : Realizable P Q ↪ Word (ZMod 2) (Sum κP κQ) where
  toFun s := joinSyndrome s.1.val s.2.val
  inj' s t h := by
    apply Prod.ext
    · apply Subtype.ext; funext j; exact congrFun h (.inl j)
    · apply Subtype.ext; funext j; exact congrFun h (.inr j)

@[simp] theorem realizableEmbedding_apply (s : Realizable P Q) :
    realizableEmbedding P Q s = joinSyndrome s.1.val s.2.val := rfl

/-- The finite image of the actual pair of syndrome maps. -/
def realizableSyndromes : Finset (Word (ZMod 2) (Sum κP κQ)) :=
  Finset.univ.map (realizableEmbedding P Q)

theorem mem_realizableSyndromes_iff (s : Word (ZMod 2) (Sum κP κQ)) :
    s ∈ realizableSyndromes P Q ↔
      (fun p => s (.inl p)) ∈ LinearMap.range P ∧
      (fun q => s (.inr q)) ∈ LinearMap.range Q := by
  constructor
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨⟨u,v⟩, _, rfl⟩
    exact ⟨u.property, v.property⟩
  · rintro ⟨hu,hv⟩
    apply Finset.mem_map.mpr
    refine ⟨(⟨_,hu⟩,⟨_,hv⟩), Finset.mem_univ _, ?_⟩
    funext j; cases j <;> rfl

theorem sum_sector_finrank :
    (∑ s, Module.finrank ℂ (sector P Q horth s)) = 2 ^ Fintype.card ι := by
  have h := congrArg (LinearMap.trace ℂ (Qubit.QubitRegister ι)) (sum_projector P Q horth)
  simp only [map_sum, trace_projector, LinearMap.trace_one, Qubit.finrank_qubitRegister] at h
  exact_mod_cast h

theorem sum_realizable_finrank :
    (∑ s ∈ realizableSyndromes P Q, Module.finrank ℂ (sector P Q horth s)) =
      2 ^ Fintype.card ι := by
  rw [realizableSyndromes, Finset.sum_map]
  simp only [realizableEmbedding_apply]
  calc
    _ = ∑ _ : Realizable P Q, multiplicity P Q := by
      apply Finset.sum_congr rfl
      intro s _
      exact sector_realizable_finrank P Q horth s.1 s.2
    _ = _ := by simpa [mul_comm] using multiplicity_mul_card_realizable P Q horth

/-- Completeness and the derived dimension count exclude every impossible sector. -/
theorem projector_eq_zero_of_not_realizable (s : Word (ZMod 2) (Sum κP κQ))
    (hs : s ∉ realizableSyndromes P Q) : projector P Q horth s = 0 := by
  have hle : Module.finrank ℂ (sector P Q horth s) + 2 ^ Fintype.card ι ≤
      2 ^ Fintype.card ι := by
    calc
      _ = ∑ t ∈ insert s (realizableSyndromes P Q), Module.finrank ℂ (sector P Q horth t) := by
        rw [Finset.sum_insert hs, sum_realizable_finrank]
      _ ≤ ∑ t, Module.finrank ℂ (sector P Q horth t) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = _ := sum_sector_finrank P Q horth
  have hr : Module.finrank ℂ (sector P Q horth s) = 0 := by omega
  apply (trace_projector_zero_iff P Q horth s).mp
  rw [trace_projector, hr, Nat.cast_zero]

theorem projector_ne_zero_iff (s : Word (ZMod 2) (Sum κP κQ)) :
    projector P Q horth s ≠ 0 ↔ s ∈ realizableSyndromes P Q := by
  constructor
  · intro hn
    exact Classical.byContradiction (fun hs => hn (projector_eq_zero_of_not_realizable P Q horth s hs))
  · intro hs hz
    rcases Finset.mem_map.mp hs with ⟨⟨u,v⟩, _, rfl⟩
    have ht := congrArg (LinearMap.trace ℂ (Qubit.QubitRegister ι)) hz
    rw [trace_projector, realizableEmbedding_apply, sector_realizable_finrank, map_zero] at ht
    have hm : multiplicity P Q = 0 := by exact_mod_cast ht
    exact (Nat.ne_of_gt (multiplicity_pos P Q)) hm

theorem trace_projector_formula (s : Word (ZMod 2) (Sum κP κQ)) :
    LinearMap.trace ℂ (Qubit.QubitRegister ι) (projector P Q horth s) =
      if s ∈ realizableSyndromes P Q then (multiplicity P Q : ℂ) else 0 := by
  by_cases hs : s ∈ realizableSyndromes P Q
  · rw [if_pos hs]
    rcases Finset.mem_map.mp hs with ⟨⟨u,v⟩, _, rfl⟩
    rw [trace_projector, realizableEmbedding_apply, sector_realizable_finrank]
  · rw [if_neg hs, projector_eq_zero_of_not_realizable P Q horth s hs, map_zero]

theorem sector_finrank_zero_of_not_realizable (s : Word (ZMod 2) (Sum κP κQ))
    (hs : s ∉ realizableSyndromes P Q) : Module.finrank ℂ (sector P Q horth s) = 0 := by
  have ht := trace_projector P Q horth s
  rw [projector_eq_zero_of_not_realizable P Q horth s hs, map_zero] at ht
  exact_mod_cast ht.symm

/-- Every literal row, including an identity row, contributes one Hamiltonian term. -/
def hamiltonian : Operator (Qubit.QubitRegister ι) :=
  -(∑ j : Sum κP κQ, toQubitOperator (binaryCSSParityCheckGenerators P Q j))

@[simp] theorem row_adjoint (j : Sum κP κQ) :
    LinearMap.adjoint (toQubitOperator (binaryCSSParityCheckGenerators P Q j)) =
      toQubitOperator (binaryCSSParityCheckGenerators P Q j) := by
  have h := adjoint_toHermitianQubitOperator_eq_self (binaryCSSParityCheckGenerators P Q j)
  simpa only [hermitian_row] using h

theorem hamiltonian_adjoint : LinearMap.adjoint (hamiltonian P Q) = hamiltonian P Q := by
  simp [hamiltonian]

theorem hamiltonian_symmetric : (hamiltonian P Q).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (hamiltonian_adjoint P Q)

/-- The row-count shift preserves redundant checks; it is not a rank. -/
def energy (_P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (_Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (s : Word (ZMod 2) (Sum κP κQ)) : ℝ :=
  -(Fintype.card κP + Fintype.card κQ : Nat) + 2 * HammingWeight s

private theorem sum_phase {τ : Type} [Fintype τ] (s : Word (ZMod 2) τ) :
    (∑ j, binaryPhaseScalar (s j)) = (Fintype.card τ : ℂ) - 2 * HammingWeight s := by
  have hphase : ∀ b : ZMod 2, binaryPhaseScalar b =
      (1 : ℂ) - 2 * (if b ≠ 0 then 1 else 0) := by
    intro b; by_cases h : b = 0 <;> norm_num [binaryPhaseScalar, h]
  have hw : (HammingWeight s : ℂ) = ∑ j, if s j ≠ 0 then (1 : ℂ) else 0 := by
    simp [HammingWeight, hammingSupport, Finset.card_filter, Nat.cast_sum]
  simp_rw [hphase]
  rw [hw]
  simp [Finset.sum_sub_distrib, Finset.mul_sum]

theorem hamiltonian_mul_projector (s : Word (ZMod 2) (Sum κP κQ)) :
    hamiltonian P Q * projector P Q horth s = (energy P Q s : ℂ) • projector P Q horth s := by
  simp only [hamiltonian, neg_mul, Finset.sum_mul, row_mul_projector, ← Finset.sum_smul,
    sum_phase, Fintype.card_sum]
  rw [← neg_smul]
  congr 1
  simp [energy]
  ring

/-- A literal syndrome energy decomposition; energy-degenerate sectors remain distinct. -/
theorem hamiltonian_syndrome_resolution : hamiltonian P Q =
    ∑ s, (energy P Q s : ℂ) • projector P Q horth s := by
  calc
    hamiltonian P Q = hamiltonian P Q * (∑ s, projector P Q horth s) := by
      rw [sum_projector, mul_one]
    _ = _ := by simp only [Finset.mul_sum, hamiltonian_mul_projector]

theorem weight_joinSyndrome (u : Word (ZMod 2) κP) (v : Word (ZMod 2) κQ) :
    HammingWeight (joinSyndrome u v) = HammingWeight u + HammingWeight v := by
  simp only [HammingWeight, hammingSupport, Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rfl

theorem energy_joinSyndrome (u : Word (ZMod 2) κP) (v : Word (ZMod 2) κQ) :
    energy P Q (joinSyndrome u v) =
      -(Fintype.card κP + Fintype.card κQ : Nat) + 2 * (HammingWeight u + HammingWeight v : Nat) := by
  rw [energy, weight_joinSyndrome]

end QEC.Coding.CSSGibbs
