import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Intervals
import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Preimages

/-! # Syndrome sensitivity of actual stopped histories

BDL26, paper.tex2438–2465 supplies local computability. The quantitative
constant57 is derived from the actual readers, not a quoted paper constant.
The bounds concern syndrome differences, without parent/support/stability
conclusions about corrections or the internal full error representatives.
-/
noncomputable section
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators

variable (S : OddScale) (d : Nat) (i : StepIndex d)

def differentialInfluence (e : (indexedFamily S d).Cochain1 i.succ) :
    Finset (FamilyZ S d i.succ) :=
  (hammingSupport e).biUnion (fun q => hammingSupport (basisSyndrome S d i q))

theorem differential_support (e : (indexedFamily S d).Cochain1 i.succ) :
    hammingSupport ((indexedFamily S d).coboundary1 i.succ e) ⊆
      differentialInfluence S d i e := by
  have heq : (indexedFamily S d).coboundary1 i.succ e =
      ∑ q, e q • basisSyndrome S d i q := by
    conv_lhs => rw [error_basis_expansion S d i e]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact map_smul ((indexedFamily S d).coboundary1 i.succ) (e q) _
  intro z hz
  by_contra hn
  have hzero : (∑ q, e q • basisSyndrome S d i q) z = 0 := by
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : e q = 0
    · simp only [hq, zero_smul, Pi.zero_apply]
    · have hzq : basisSyndrome S d i q z = 0 := by
        by_contra hzq
        exact hn (Finset.mem_biUnion.mpr
          ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzq⟩⟩)
      change e q * basisSyndrome S d i q z = 0
      rw [hzq,mul_zero]
  exact (Finset.mem_filter.mp hz).2 ((congrFun heq z).trans hzero)

theorem differential_weight (e : (indexedFamily S d).Cochain1 i.succ) :
    HammingWeight ((indexedFamily S d).coboundary1 i.succ e) ≤ 4 * HammingWeight e := by
  have hs := Finset.card_le_card (differential_support S d i e)
  have hc := Finset.card_biUnion_le_card_mul (hammingSupport e)
    (fun q => hammingSupport (basisSyndrome S d i q)) 4
    (fun q _ => basisSyndrome_weight_le_four S d i q)
  exact hs.trans (hc.trans_eq (Nat.mul_comm _ _))

variable (n : Nat)

/-- Genuine validity is constructed from a real preimage of the background plus e. -/
def perturbTop (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) : TopInput S n :=
  ⟨sigma.val + (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e, by
    obtain ⟨a,ha⟩ := sigma.property
    exact ⟨a+e,by rw [map_add,ha]⟩⟩

theorem perturbTop_preimage (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) :
    ∃ a : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2)),
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) a = sigma.val ∧
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) (a+e) =
        (perturbTop S n sigma e).val := by
  obtain ⟨a,ha⟩ := sigma.property
  exact ⟨a,ha,by change _ = sigma.val + _; rw [map_add,ha]⟩

theorem perturbTop_difference (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) :
    sigma.val + (perturbTop S n sigma e).val =
      (indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e := by
  funext z
  change sigma.val z + (sigma.val z + _) = _
  rw [← add_assoc, ZModModule.add_self, zero_add]

theorem actualReadout_top (sigma : TopInput S n) :
    actualReadout S n sigma (TopIndex n) = sigma.val := by
  rw [actualInputs_readout, actualInputs_top]

/-- The sharper bound keeps the actual top differential rather than its column estimate. -/
theorem physical_error_differential_bound (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) (a : LevelIndex n) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n (perturbTop S n sigma e) a) ≤
      57 ^ ((n+1)/2 - (a.val+1)/2) *
        HammingWeight ((indexedFamily S (n+2)).coboundary1 (TopIndex (n+2)) e) := by
  have h := actual_interval_weight S n sigma (perturbTop S n sigma e) a (TopIndex n)
    (Nat.le_of_lt_succ a.isLt)
  rw [actualReadout_top, actualReadout_top, perturbTop_difference] at h
  exact h

theorem physical_error_weight_bound (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) (a : LevelIndex n) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n (perturbTop S n sigma e) a) ≤
      4 * 57 ^ ((n+1)/2 - (a.val+1)/2) * HammingWeight e := by
  have ht := physical_error_differential_bound S n sigma e a
  have hd := differential_weight S (n+2) (Fin.last (n+1)) e
  exact (ht.trans (Nat.mul_le_mul_left _ hd)).trans_eq (by ac_rfl)

/-- Physical C2 is the actual final input, not a fabricated below-base snapshot. -/
theorem c2_pair_weight (sigma tau : TopInput S n) :
    HammingWeight (actualReadout S n sigma 0 + actualReadout S n tau 0) ≤
      57 ^ ((n+1)/2) * HammingWeight (sigma.val + tau.val) := by
  have h := actual_interval_weight S n sigma tau 0 (TopIndex n) (Nat.zero_le _)
  simpa only [actualReadout_top, Fin.val_zero, Nat.zero_add, Nat.div_eq_of_lt
    (by decide : 1 < 2), Nat.sub_zero] using h

theorem c2_physical_error_weight (sigma : TopInput S n)
    (e : (indexedFamily S (n+2)).Cochain1 (TopIndex (n+2))) :
    HammingWeight (actualReadout S n sigma 0 + actualReadout S n (perturbTop S n sigma e) 0) ≤
      4 * 57 ^ ((n+1)/2) * HammingWeight e := by
  simpa only [Fin.val_zero, Nat.zero_add, Nat.div_eq_of_lt (by decide : 1 < 2),
    Nat.sub_zero] using physical_error_weight_bound S n sigma e 0

theorem depthTwo_readout (sigma : TopInput S 0) : actualReadout S 0 sigma 0 = sigma.val :=
  actualReadout_top S 0 sigma

end QEC.Coding.BDL26HistorySyndromeSensitivity
