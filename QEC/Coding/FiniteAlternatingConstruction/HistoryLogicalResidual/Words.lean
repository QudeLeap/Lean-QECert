import QEC.Coding.FiniteAlternatingConstruction.HistoryLogicalResidual.Intervals

/-! # Actual full stopped-history residual words

The caller's genuine upper representative is fixed. Its second descent starts
at exactly u+e. Both original complete corrections and both C2 base corrections
are retained; no existential chosen representative is substituted for u.
-/
noncomputable section
namespace QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical

variable (S : OddScale) (n : Nat)

def baseCorrection (sigma : TopInput S n) : (SuffixData S n).family.Cochain1 0 :=
  (actualBase S n).decode (actualInputs S n sigma 0)

def fullCorrection (sigma : TopInput S n) : (SuffixData S n).family.Cochain1 (TopIndex n) :=
  historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)

def lowerWord (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.Cochain1 0 :=
  descentWord S n (TopIndex n) u 0 (Nat.zero_le _) +
    descentWord S n (TopIndex n) (u+e) 0 (Nat.zero_le _) +
      baseCorrection S n sigma + baseCorrection S n (perturbTop S n sigma e)

def topWord (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.Cochain1 (TopIndex n) :=
  e + fullCorrection S n sigma + fullCorrection S n (perturbTop S n sigma e)

def residualPotential (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.Cochain0 (TopIndex n) :=
  accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _) +
    accumulatedPotential S n (TopIndex n) (u+e) 0 n (Nat.le_refl _) (Nat.zero_le _)

theorem shared_valid (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    (SuffixData S n).family.coboundary1 (TopIndex n) (u+e) =
      (perturbTop S n sigma e).val := by
  change (SuffixData S n).family.coboundary1 (TopIndex n) (u+e) =
    sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e
  rw [map_add,hu]

theorem lower_closed (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    (SuffixData S n).family.coboundary1 0 (lowerWord S n sigma e u) = 0 := by
  let tau := perturbTop S n sigma e
  have hue := shared_valid S n sigma e u hu
  have hv := hu.trans (actualReadout_top S n sigma).symm
  have hv' := hue.trans (actualReadout_top S n tau).symm
  have hl := descentWord_readout S n sigma (TopIndex n) u hv 0 (Nat.zero_le _)
  have hl' := descentWord_readout S n tau (TopIndex n) (u+e) hv' 0 (Nat.zero_le _)
  have hb : (SuffixData S n).family.coboundary1 0 (baseCorrection S n sigma) =
      actualReadout S n sigma 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n sigma 0).symm
  have hb' : (SuffixData S n).family.coboundary1 0 (baseCorrection S n tau) =
      actualReadout S n tau 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n tau 0).symm
  unfold lowerWord
  rw [map_add,map_add,map_add,hl,hl',hb,hb']
  calc
    (actualReadout S n sigma 0 + actualReadout S n tau 0) + actualReadout S n sigma 0 +
        actualReadout S n tau 0 =
      (actualReadout S n sigma 0 + actualReadout S n sigma 0) +
        (actualReadout S n tau 0 + actualReadout S n tau 0) := by ac_rfl
    _ = 0 := by rw [word_add_self,word_add_self,add_zero]

theorem top_closed (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.coboundary1 (TopIndex n) (topWord S n sigma e) = 0 := by
  have hs : (SuffixData S n).family.coboundary1 (TopIndex n) (fullCorrection S n sigma) =
      sigma.val := actualHistory_syndrome S n sigma
  have ht : (SuffixData S n).family.coboundary1 (TopIndex n)
      (fullCorrection S n (perturbTop S n sigma e)) = (perturbTop S n sigma e).val :=
    actualHistory_syndrome S n (perturbTop S n sigma e)
  unfold topWord
  rw [map_add,map_add,hs,ht]
  change (SuffixData S n).family.coboundary1 (TopIndex n) e + sigma.val +
    (sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e) = 0
  calc
    _ = ((SuffixData S n).family.coboundary1 (TopIndex n) e +
        (SuffixData S n).family.coboundary1 (TopIndex n) e) + (sigma.val+sigma.val) := by ac_rfl
    _ = 0 := by rw [word_add_self,word_add_self,add_zero]

/-- The full identity for this caller's u, with the entire exact Q(u)+Q(u+e). -/
theorem full_identity (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    topWord S n sigma e =
      intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (lowerWord S n sigma e u) +
        (SuffixData S n).family.coboundary0 (TopIndex n) (residualPotential S n e u) := by
  let tau := perturbTop S n sigma e
  let l := descentWord S n (TopIndex n) u 0 (Nat.zero_le _)
  let l' := descentWord S n (TopIndex n) (u+e) 0 (Nat.zero_le _)
  let bs := baseCorrection S n sigma
  let bt := baseCorrection S n tau
  let q := accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)
  let q' := accumulatedPotential S n (TopIndex n) (u+e) 0 n (Nat.le_refl _) (Nat.zero_le _)
  have hs := actual_fullspan S n sigma u hu
  have ht := actual_fullspan S n tau (u+e) (shared_valid S n sigma e u hu)
  have heq := combine_full_words
    (intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _))
    ((SuffixData S n).family.coboundary0 (TopIndex n)) u e
    (fullCorrection S n sigma) (fullCorrection S n tau) (l+bs) (l'+bt) q q' hs ht
  have hinside : (l+bs)+(l'+bt)=(l+l')+bs+bt := by ac_rfl
  rw [hinside] at heq
  exact heq

theorem residualPotential_closed (e u : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      ((SuffixData S n).family.coboundary0 (TopIndex n) (residualPotential S n e u)) = 0 :=
  LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0 (TopIndex n)) _

def lowerCocycle (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) : FC.Cocycle S 2 :=
  ⟨lowerWord S n sigma e u, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have h := lower_closed S n sigma e u hu
    rw [suffix_delta1] at h
    exact h⟩

def topCocycle (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) : FC.Cocycle S (n+2) :=
  ⟨topWord S n sigma e, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have h := top_closed S n sigma e
    rw [suffix_delta1] at h
    exact h⟩

theorem perturbTop_of_closed (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n))
    (he : (SuffixData S n).family.coboundary1 (TopIndex n) e = 0) :
    perturbTop S n sigma e = sigma := by
  apply Subtype.ext
  change sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e = sigma.val
  rw [he,add_zero]

/-- A closed error survives as itself: this is not a blanket stability claim. -/
theorem topWord_of_closed (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n))
    (he : (SuffixData S n).family.coboundary1 (TopIndex n) e = 0) : topWord S n sigma e = e := by
  have hc : fullCorrection S n (perturbTop S n sigma e) = fullCorrection S n sigma :=
    congrArg (fullCorrection S n) (perturbTop_of_closed S n sigma e he)
  change e + fullCorrection S n sigma + fullCorrection S n (perturbTop S n sigma e) = e
  calc
    e + fullCorrection S n sigma + fullCorrection S n (perturbTop S n sigma e) =
        e + fullCorrection S n sigma + fullCorrection S n sigma :=
      congrArg (fun h : (SuffixData S n).family.Cochain1 (TopIndex n) =>
        e + fullCorrection S n sigma + h) hc
    _ = e + (fullCorrection S n sigma + fullCorrection S n sigma) := add_assoc e _ _
    _ = e := (congrArg (fun h : (SuffixData S n).family.Cochain1 (TopIndex n) => e+h)
      (word_add_self (fullCorrection S n sigma))).trans (add_zero e)

theorem topWord_zero (sigma : TopInput S n) : topWord S n sigma 0 = 0 :=
  topWord_of_closed S n sigma 0 (map_zero _)

end QEC.Coding.BDL26HistoryLogicalResidual
