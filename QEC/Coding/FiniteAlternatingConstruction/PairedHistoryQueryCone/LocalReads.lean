import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Intervals
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXQConcreteCoherence
import QEC.Coding.FiniteAlternatingConstruction.GraphQuantitativeBounds

/-!
# The actual selector queries used by a paired history

These are coordinate queries of the existing selectors. In particular, no
linearity is asserted for a correction selector. The radius-two RX block is
a convenient common envelope for its radius-one correction query and its
radius-two coarse query. Its coordinate cardinality includes the whole
syndrome fibre at every vertex.
-/
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

abbrev Owners (S : OddScale) (depth : Nat) (i : StepIndex depth) :=
  RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
    (state S i.val).presentation.Z

def AgreeOn {I : Type} (A : Finset I) (s t : Word BDL26Field I) : Prop :=
  ∀ p ∈ A, s p = t p

theorem binary_word_add_self {I : Type} (s : Word BDL26Field I) : s+s=0 := by
  funext p
  exact ZModModule.add_self _

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

def rxOwnerRead (h : i.val % 2 = 0) (v : Owners S depth i) :
    Finset (FamilyZ S depth i.succ) :=
  (xiIndexSet (rxData S depth i h).levelGraph.graph v 2).biUnion
    (fun w => (rxXiLocalComplex (rxData S depth i h)).syndromeRegion w)

theorem mem_rxOwnerRead (h : i.val % 2 = 0) (v : Owners S depth i)
    (p : FamilyZ S depth i.succ) :
    p ∈ rxOwnerRead S depth i h v ↔
      (rxData S depth i h).levelGraph.graph.distance
        ((rxData S depth i h).topCenter p) v ≤ 2 := by
  rw [rxOwnerRead, Finset.mem_biUnion]
  constructor
  · rintro ⟨w,hw,hp⟩
    have he := (rxXiLocalComplex_region_mem_iff (rxData S depth i h) w p).mp hp
    subst w
    exact (Finset.mem_filter.mp hw).2
  · intro hp
    exact ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,
      (rxXiLocalComplex_region_mem_iff _ _ _).mpr rfl⟩

def ownerRead (v : Owners S depth i) : Finset (FamilyZ S depth i.succ) :=
  if h : i.val % 2 = 0 then rxOwnerRead S depth i h v else
    match v with
    | .inl _ => ∅
    | .inr (.inl _) => ∅
    | .inr (.inr z) => (rzData S depth i h).coarseRegion z

def coarseRead (z : FamilyZ S depth i.castSucc) :
    Finset (FamilyZ S depth i.succ) :=
  if h : i.val % 2 = 0 then readRegion S depth i h z
  else (rzData S depth i h).coarseRegion z

def component (v : Owners S depth i)
    (s : Word BDL26Field (FamilyZ S depth i.succ)) :
    Word BDL26Field (FamilyQ S depth i.succ) :=
  if h : i.val % 2 = 0 then
    (rxLocalComponents (rxData S depth i h)).component v s
  else match v with
    | .inl _ => 0
    | .inr (.inl _) => 0
    | .inr (.inr z) => RZCoarseGraining.localCorrectionComponent
        (rzData S depth i h) (rzData_localTopCohomology S depth i h) z s

theorem rx_component_agreement (h : i.val % 2 = 0) (v : Owners S depth i)
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (ha : AgreeOn (rxOwnerRead S depth i h v) s t) :
    (rxLocalComponents (rxData S depth i h)).component v s =
      (rxLocalComponents (rxData S depth i h)).component v t := by
  have he : rxXiSignal (rxData S depth i h) s v 1 =
      rxXiSignal (rxData S depth i h) t v 1 := by
    funext p
    rw [rxXiSignal_apply,rxXiSignal_apply]
    split_ifs with hd
    · exact ha p ((mem_rxOwnerRead S depth i h v p).mpr (le_trans hd (by decide)))
    · rfl
  have hs := (rx_local_computability_certificate (rxData S depth i h)).componentInvariantAtXiOne v s
  have ht := (rx_local_computability_certificate (rxData S depth i h)).componentInvariantAtXiOne v t
  exact hs.trans ((congrArg (fun w =>
    (rxLocalComponents (rxData S depth i h)).component v w) he).trans ht.symm)

theorem rz_component_agreement (h : ¬ i.val % 2 = 0)
    (z : FamilyZ S depth i.castSucc)
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (ha : AgreeOn ((rzData S depth i h).coarseRegion z) s t) :
    RZCoarseGraining.localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z s =
    RZCoarseGraining.localCorrectionComponent (rzData S depth i h)
      (rzData_localTopCohomology S depth i h) z t := by
  have hp : RZCoarseGraining.RZCoarseGrainingData.topParity (rzData S depth i h) s z =
      RZCoarseGraining.RZCoarseGrainingData.topParity (rzData S depth i h) t z := by
    exact Finset.sum_congr rfl (fun p hp => ha p hp)
  apply congrArg (RZCoarseGraining.localCorrectionSelector (rzData S depth i h) z)
  funext p
  change maskWord _ s p + _ = maskWord _ t p + _
  rw [hp]
  by_cases hm : p ∈ (rzData S depth i h).coarseRegion z
  · simp only [maskWord,if_pos hm,ha p hm]
  · simp only [maskWord,if_neg hm]

theorem component_agreement (v : Owners S depth i)
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (ha : AgreeOn (ownerRead S depth i v) s t) :
    component S depth i v s = component S depth i v t := by
  by_cases h : i.val % 2 = 0
  · have hread : AgreeOn (rxOwnerRead S depth i h v) s t := by
      simpa only [ownerRead,dif_pos h] using ha
    simpa only [component,dif_pos h] using rx_component_agreement S depth i h v s t hread
  · cases v with
    | inl x => simp only [component,dif_neg h]
    | inr v => cases v with
      | inl q => simp only [component,dif_neg h]
      | inr z =>
          have hread : AgreeOn ((rzData S depth i h).coarseRegion z) s t := by
            simpa only [ownerRead,dif_neg h] using ha
          simpa only [component,dif_neg h] using rz_component_agreement S depth i h z s t hread

theorem correction_eq_components
    (s : (indexedFamily S depth).Syndrome i.succ) :
    (actualStep S depth i s).correction = ∑ v, component S depth i v s.val := by
  by_cases h : i.val % 2 = 0
  · rw [actualStep_rx S depth i h,rxStepOutput_correction,
      rx_total_correction_decomposition]
    funext q
    change (∑ v, (rxLocalComponents (rxData S depth i h)).component v s.val q) = _
    simp only [Finset.sum_apply,component,dif_pos h]
  · rw [actualStep_rz S depth i h]
    rw [(rzStepOutput S depth i h s).correction_decomposition,
      rzStepOutput_localComponents]
    simp [component,dif_neg h,Fintype.sum_sum_type] <;> rfl

theorem coarse_agreement (s t : (indexedFamily S depth).Syndrome i.succ)
    (z : FamilyZ S depth i.castSucc)
    (ha : AgreeOn (coarseRead S depth i z) s.val t.val) :
    (actualStep S depth i s).coarse.val z = (actualStep S depth i t).coarse.val z := by
  by_cases h : i.val % 2 = 0
  · rw [actualStep_rx S depth i h]
    exact rx_coarse_agreement S depth i h s t z (by
      intro p hp
      exact ha p (by simpa only [coarseRead,dif_pos h] using hp))
  · rw [actualStep_rz S depth i h,rzStepOutput_coarse_apply,rzStepOutput_coarse_apply]
    apply Finset.sum_congr rfl
    intro p hp
    exact ha p (by simpa only [coarseRead,dif_neg h] using hp)

/-- The owner is affected exactly when its actual query envelope meets U. -/
def affected (U : Finset (FamilyZ S depth i.succ)) : Finset (Owners S depth i) :=
  Finset.univ.filter fun v => ∃ p ∈ U, p ∈ ownerRead S depth i v

def correctionQueries (U : Finset (FamilyZ S depth i.succ)) :
    Finset (FamilyZ S depth i.succ) :=
  (affected S depth i U).biUnion (ownerRead S depth i)

def liftQueries (A : Finset (FamilyZ S depth i.castSucc)) :
    Finset (FamilyZ S depth i.succ) := A.biUnion (coarseRead S depth i)

theorem component_pair_zero (U : Finset (FamilyZ S depth i.succ))
    (s t : Word BDL26Field (FamilyZ S depth i.succ))
    (hs : hammingSupport (s+t) ⊆ U) (v : Owners S depth i)
    (hv : v ∉ affected S depth i U) :
    component S depth i v s + component S depth i v t = 0 := by
  have he : component S depth i v s = component S depth i v t := by
    apply component_agreement S depth i v s t
    intro p hp
    apply (binary_add_eq_zero_iff _ _).mp
    by_contra hn
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,hs
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩),hp⟩)
  rw [he]
  exact binary_word_add_self _

/-- Replay the two component differences, without asserting linearity. -/
theorem correction_pair_replay (U : Finset (FamilyZ S depth i.succ))
    (s t s' t' : (indexedFamily S depth).Syndrome i.succ)
    (hs : hammingSupport (s.val+t.val) ⊆ U)
    (hs' : hammingSupport (s'.val+t'.val) ⊆ U)
    (ha : AgreeOn (correctionQueries S depth i U) s.val s'.val)
    (hb : AgreeOn (correctionQueries S depth i U) t.val t'.val) :
    (actualStep S depth i s).correction + (actualStep S depth i t).correction =
      (actualStep S depth i s').correction + (actualStep S depth i t').correction := by
  simp_rw [correction_eq_components,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ affected S depth i U
  · have hsub : ownerRead S depth i v ⊆ correctionQueries S depth i U :=
      fun p hp => Finset.mem_biUnion.mpr ⟨v,hv,hp⟩
    rw [component_agreement S depth i v s.val s'.val (fun p hp => ha p (hsub hp)),
      component_agreement S depth i v t.val t'.val (fun p hp => hb p (hsub hp))]
  · rw [component_pair_zero S depth i U s.val t.val hs v hv,
      component_pair_zero S depth i U s'.val t'.val hs' v hv]

end QEC.Coding.BDL26PairedHistoryQueryCone
