import QEC.Coding.FiniteAlternatingConstruction.HistoryLogicalResidual.Words

/-! # The full stopped-history logical residual at physical C2

The top residual and the C2 residual have the same canonical coefficient.
The coefficient is not asserted to vanish: the actual logical generator keeps
coefficient one. Both original histories, both base corrections, and the same
caller's u and u+e are retained throughout.
-/
noncomputable section
namespace QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical

variable (S : OddScale) (n : Nat)

def topCoefficient (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) : BDL26Field :=
  FC.finiteH1Equiv S (n+2) (FC.classOf S (n+2) (topCocycle S n sigma e))

def lowerCoefficient (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) : BDL26Field :=
  FC.finiteH1Equiv S 2 (FC.classOf S 2 (lowerCocycle S n sigma e u hu))

/-- The quotient relation is induced by the literal intervalMap1 on full words. -/
theorem class_relation (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    FC.classOf S (n+2) (topCocycle S n sigma e) =
      suffixEquiv S n 0 (TopIndex n) (FC.classOf S 2 (lowerCocycle S n sigma e u hu)) := by
  let v := intervalCocycle S n 0 (TopIndex n) (Nat.zero_le _)
    (lowerCocycle S n sigma e u hu)
  have hboundary : FC.classOf S (n+2) (topCocycle S n sigma e) =
      FC.classOf S (n+2) v := by
    apply (class_eq_iff_boundary S (n+2) _ _).mpr
    refine ⟨residualPotential S n e u, ?_⟩
    have hi := full_identity S n sigma e u hu
    have hv := intervalCocycle_word S n 0 (TopIndex n) (Nat.zero_le _)
      (lowerCocycle S n sigma e u hu)
    change v.val = intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
      (lowerWord S n sigma e u) at hv
    change tannerCoboundary0 (state S (n+2)).presentation (residualPotential S n e u) =
      topWord S n sigma e - v.val
    rw [← suffix_delta0 S n (TopIndex n),hv,hi]
    abel
  exact hboundary.trans (suffixEquiv_mk S n 0 (TopIndex n) (Nat.zero_le _)
    (lowerCocycle S n sigma e u hu)).symm

theorem coefficient_equality (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    topCoefficient S n sigma e = lowerCoefficient S n sigma e u hu := by
  unfold topCoefficient lowerCoefficient
  rw [class_relation S n sigma e u hu]
  exact coefficient_natural S n 0 (TopIndex n) _

theorem pureX_coefficient_equality (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    BDL26LogicalQubitPreservation.logicalEquiv S (n+2)
        (BDL26LogicalQubitPreservation.logicalClass S (n+2)
          (pureX S (n+2) (topCocycle S n sigma e))) =
      BDL26LogicalQubitPreservation.logicalEquiv S 2
        (BDL26LogicalQubitPreservation.logicalClass S 2
          (pureX S 2 (lowerCocycle S n sigma e u hu))) := by
  rw [pureX_coefficient,pureX_coefficient]
  exact coefficient_equality S n sigma e u hu

theorem top_zero_iff_boundary (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    topCoefficient S n sigma e = 0 ↔
      ∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
        (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma e := by
  have h := coefficient_zero_iff_boundary S (n+2) (topCocycle S n sigma e)
  rw [← suffix_delta0 S n (TopIndex n)] at h
  exact h

theorem lower_zero_iff_boundary (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma e u hu = 0 ↔
      ∃ f : (SuffixData S n).family.Cochain0 0,
        (SuffixData S n).family.coboundary0 0 f = lowerWord S n sigma e u := by
  have h := coefficient_zero_iff_boundary S 2 (lowerCocycle S n sigma e u hu)
  have hd : (SuffixData S n).family.coboundary0 0 =
      tannerCoboundary0 (state S 2).presentation := suffix_delta0 S n (0 : LevelIndex n)
  rw [← hd] at h
  exact h

theorem boundary_iff (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    (∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
      (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma e) ↔
      ∃ f : (SuffixData S n).family.Cochain0 0,
        (SuffixData S n).family.coboundary0 0 f = lowerWord S n sigma e u := by
  rw [← top_zero_iff_boundary,← lower_zero_iff_boundary,coefficient_equality S n sigma e u hu]

/-- The forward witness is this entire transported f2 plus the computed Q+Q'. -/
theorem forward_potential (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (f2 : (SuffixData S n).family.Cochain0 0)
    (hf2 : (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u) :
    (SuffixData S n).family.coboundary0 (TopIndex n)
        (intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) f2 +
          residualPotential S n e u) = topWord S n sigma e := by
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),hf2]
  exact (full_identity S n sigma e u hu).symm

theorem reverse_potential (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (ftop : (SuffixData S n).family.Cochain0 (TopIndex n))
    (hftop : (SuffixData S n).family.coboundary0 (TopIndex n) ftop = topWord S n sigma e) :
    ∃ f2 : (SuffixData S n).family.Cochain0 0,
      (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u :=
  (boundary_iff S n sigma e u hu).mp ⟨ftop,hftop⟩

/-- Only the representative is varied; sigma and e remain fixed. -/
theorem representative_independent (sigma : TopInput S n)
    (e u v : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (hv : (SuffixData S n).family.coboundary1 (TopIndex n) v = sigma.val) :
    lowerCoefficient S n sigma e u hu = lowerCoefficient S n sigma e v hv :=
  (coefficient_equality S n sigma e u hu).symm.trans (coefficient_equality S n sigma e v hv)

theorem representative_boundary (sigma : TopInput S n)
    (e u v : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (hv : (SuffixData S n).family.coboundary1 (TopIndex n) v = sigma.val) :
    ∃ f2 : (SuffixData S n).family.Cochain0 0,
      (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u-lowerWord S n sigma e v := by
  have h := (coefficient_eq_iff_boundary S 2 (lowerCocycle S n sigma e u hu)
    (lowerCocycle S n sigma e v hv)).mp (representative_independent S n sigma e u v hu hv)
  have hd : (SuffixData S n).family.coboundary0 0 =
      tannerCoboundary0 (state S 2).presentation := suffix_delta0 S n (0 : LevelIndex n)
  rw [← hd] at h
  exact h

/-- The nontrivial error is the existing actual selected-prefix generator. -/
def logicalError : (SuffixData S n).family.Cochain1 (TopIndex n) :=
  (FC.generator S (n+2) 1).val

theorem logicalError_closed :
    (SuffixData S n).family.coboundary1 (TopIndex n) (logicalError S n) = 0 := by
  rw [suffix_delta1]
  exact (BDL26RZCohomology.mem_cocycle_iff _ _).mp (FC.generator S (n+2) 1).property

theorem logicalError_coefficient (sigma : TopInput S n) :
    topCoefficient S n sigma (logicalError S n) = 1 := by
  have hw : topCocycle S n sigma (logicalError S n) = FC.generator S (n+2) 1 := by
    apply Subtype.ext
    exact topWord_of_closed S n sigma (logicalError S n) (logicalError_closed S n)
  unfold topCoefficient
  rw [hw]
  have hg : (FC.finiteH1Equiv S (n+2)).symm 1 =
      FC.classOf S (n+2) (FC.generator S (n+2) 1) :=
    BDL26FiniteCohomology.finiteH1Equiv_symm_scalar S (n+2) 1
  exact (congrArg (FC.finiteH1Equiv S (n+2)) hg).symm.trans
    ((FC.finiteH1Equiv S (n+2)).apply_symm_apply 1)

theorem logicalError_not_boundary (sigma : TopInput S n) :
    ¬ ∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
      (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma (logicalError S n) := by
  intro h
  have hz := (top_zero_iff_boundary S n sigma (logicalError S n)).mpr h
  rw [logicalError_coefficient] at hz
  exact one_ne_zero hz

theorem lower_logicalError_coefficient (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma (logicalError S n) u hu = 1 :=
  (coefficient_equality S n sigma (logicalError S n) u hu).symm.trans
    (logicalError_coefficient S n sigma)

theorem zero_coefficient (sigma : TopInput S n) : topCoefficient S n sigma 0 = 0 := by
  have hw : topCocycle S n sigma 0 = 0 := by
    apply Subtype.ext
    exact topWord_zero S n sigma
  unfold topCoefficient
  rw [hw,map_zero,map_zero]

theorem lower_zero_coefficient (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma 0 u hu = 0 :=
  (coefficient_equality S n sigma 0 u hu).symm.trans (zero_coefficient S n sigma)

/-- All source-even physical depths, including physical C2 at k=1. -/
theorem source_even_valid (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (u : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k)))
    (hu : (indexedFamily S (2*k)).coboundary1 (TopIndex (2*k)) u = sigma.val) :
    (SuffixData S (2*(k-1))).family.coboundary1 (TopIndex (2*(k-1)))
      (sourceEvenError S k hk u) = (sourceEvenInput S k hk sigma).val := by
  cases k with
  | zero => omega
  | succ k => exact hu

theorem source_even_coefficient (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (e u : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k)))
    (hu : (indexedFamily S (2*k)).coboundary1 (TopIndex (2*k)) u = sigma.val) :
    topCoefficient S (2*(k-1)) (sourceEvenInput S k hk sigma) (sourceEvenError S k hk e) =
      lowerCoefficient S (2*(k-1)) (sourceEvenInput S k hk sigma)
        (sourceEvenError S k hk e) (sourceEvenError S k hk u) (source_even_valid S k hk sigma u hu) :=
  coefficient_equality S _ _ _ _ (source_even_valid S k hk sigma u hu)

end QEC.Coding.BDL26HistoryLogicalResidual
