import QEC.Coding.FiniteAlternatingConstruction.HistoryErrorTelescoping
import QEC.Coding.FiniteAlternatingConstruction.LogicalQubitPreservation

/-! # The literal stopped-history interval on actual cohomology

Suffix index i is physical index i+2. The quotient equivalence below is proved
to act by the original intervalMap1 on the entire representative word.
-/
noncomputable section
namespace QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical

namespace FC
export BDL26FiniteCohomology (Cocycle H1 classOf stepCocycle stepCocycle_value
  stepEquiv stepEquiv_mk prefixEquiv prefixEquiv_succ finiteH1Equiv generator)
end FC

variable (S : OddScale) (n : Nat)

/-- These are equalities of the actual differentials, not new complexes. -/
theorem suffix_delta0 (i : LevelIndex n) :
    (SuffixData S n).family.coboundary0 i =
      tannerCoboundary0 (state S (i.val+2)).presentation := by
  change (indexedFamily S (n+2)).coboundary0 (LevelTwoHistory.physicalLevel i) = _
  exact indexedFamily_coboundary0 S (n+2) (LevelTwoHistory.physicalLevel i)

theorem suffix_delta1 (i : LevelIndex n) :
    (SuffixData S n).family.coboundary1 i =
      tannerCoboundary1 (state S (i.val+2)).presentation := by
  change (indexedFamily S (n+2)).coboundary1 (LevelTwoHistory.physicalLevel i) = _
  exact indexedFamily_coboundary1 S (n+2) (LevelTwoHistory.physicalLevel i)

def cocycleEdge (i : StepIndex n) :
    FC.Cocycle S (i.castSucc.val+2) →ₗ[BDL26Field] FC.Cocycle S (i.succ.val+2) :=
  FC.stepCocycle S (i.val+2)

theorem cocycleEdge_word (i : StepIndex n) (w : FC.Cocycle S (i.castSucc.val+2)) :
    (cocycleEdge S n i w).val = ((SuffixData S n).selectedMap i).map1 w.val := by
  rw [LevelTwoHistory.suffix_selected_map1,selectedMap_eq]
  exact FC.stepCocycle_value S (i.val+2) w

def intervalCocycle (a b : LevelIndex n) (hab : a.val ≤ b.val) :
    FC.Cocycle S (a.val+2) →ₗ[BDL26Field] FC.Cocycle S (b.val+2) :=
  linearUp (V := fun i : LevelIndex n => ↥(FC.Cocycle S (i.val+2)))
    (cocycleEdge S n) b.val (Nat.le_of_lt_succ b.isLt) a hab

theorem intervalCocycle_self (a : LevelIndex n) :
    intervalCocycle S n a a (Nat.le_refl _) = LinearMap.id :=
  linearUp_self (V := fun i : LevelIndex n => ↥(FC.Cocycle S (i.val+2)))
    (cocycleEdge S n) a.val _

theorem intervalCocycle_succ (a : LevelIndex n) (i : StepIndex n) (hai : a.val ≤ i.val) :
    intervalCocycle S n a i.succ (by change a.val ≤ i.val+1; omega) =
      (cocycleEdge S n i).comp (intervalCocycle S n a i.castSucc hai) :=
  linearUp_succ (V := fun j : LevelIndex n => ↥(FC.Cocycle S (j.val+2)))
    (cocycleEdge S n) i.val (Nat.le_of_lt_succ i.succ.isLt) a hai

theorem intervalCocycle_comp (a b c : LevelIndex n)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalCocycle S n a c (hab.trans hbc) =
      (intervalCocycle S n b c hbc).comp (intervalCocycle S n a b hab) :=
  linearUp_comp (V := fun i : LevelIndex n => ↥(FC.Cocycle S (i.val+2)))
    (cocycleEdge S n) c.val _ b a hbc hab

/-- The actual quotient maps are the already proved selected finite maps. -/
def suffixEquiv (a b : LevelIndex n) :
    FC.H1 S (a.val+2) ≃ₗ[BDL26Field] FC.H1 S (b.val+2) :=
  (FC.prefixEquiv S (a.val+2)).symm.trans (FC.prefixEquiv S (b.val+2))

theorem suffixEquiv_self (a : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n a a x = x := (FC.prefixEquiv S (a.val+2)).apply_symm_apply x

theorem suffixEquiv_comp (a b c : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n b c (suffixEquiv S n a b x) = suffixEquiv S n a c x := by
  change FC.prefixEquiv S (c.val+2)
    ((FC.prefixEquiv S (b.val+2)).symm
      (FC.prefixEquiv S (b.val+2) ((FC.prefixEquiv S (a.val+2)).symm x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem suffixEquiv_succ (a : LevelIndex n) (i : StepIndex n)
    (x : FC.H1 S (a.val+2)) :
    suffixEquiv S n a i.succ x =
      FC.stepEquiv S (i.val+2) (suffixEquiv S n a i.castSucc x) := by
  change FC.prefixEquiv S ((i.val+2)+1) ((FC.prefixEquiv S (a.val+2)).symm x) = _
  rw [FC.prefixEquiv_succ]
  rfl

theorem suffix_left_inverse (a b : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    (suffixEquiv S n a b).symm (suffixEquiv S n a b x) = x :=
  (suffixEquiv S n a b).symm_apply_apply x

theorem suffix_right_inverse (a b : LevelIndex n) (x : FC.H1 S (b.val+2)) :
    suffixEquiv S n a b ((suffixEquiv S n a b).symm x) = x :=
  (suffixEquiv S n a b).apply_symm_apply x

/-- Word and quotient equations are proved together along the actual interval. -/
theorem interval_facts_nat (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (w : FC.Cocycle S (a.val+2)) :
    (intervalCocycle S n a ⟨b,Nat.lt_succ_of_le hb⟩ ha w).val =
        intervalMap1 (SuffixData S n) a ⟨b,Nat.lt_succ_of_le hb⟩ ha w.val ∧
      suffixEquiv S n a ⟨b,Nat.lt_succ_of_le hb⟩ (FC.classOf S (a.val+2) w) =
        FC.classOf S (b+2) (intervalCocycle S n a ⟨b,Nat.lt_succ_of_le hb⟩ ha w) := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      constructor
      · rw [intervalCocycle_self,intervalMap1_self]; rfl
      · rw [suffixEquiv_self,intervalCocycle_self]; rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        constructor
        · rw [intervalCocycle_self,intervalMap1_self]; rfl
        · rw [suffixEquiv_self,intervalCocycle_self]; rfl
      · have hal : a.val ≤ b := by omega
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        have hf := ih (by omega) a hal w
        have hv := hf.1
        have hq := hf.2
        change (intervalCocycle S n a i.castSucc hal w).val =
          intervalMap1 (SuffixData S n) a i.castSucc hal w.val at hv
        change suffixEquiv S n a i.castSucc (FC.classOf S (a.val+2) w) =
          FC.classOf S (i.castSucc.val+2) (intervalCocycle S n a i.castSucc hal w) at hq
        change (intervalCocycle S n a i.succ ha w).val =
            intervalMap1 (SuffixData S n) a i.succ ha w.val ∧
          suffixEquiv S n a i.succ (FC.classOf S (a.val+2) w) =
            FC.classOf S (i.succ.val+2) (intervalCocycle S n a i.succ ha w)
        rw [intervalCocycle_succ S n a i hal,LinearMap.comp_apply]
        constructor
        · rw [cocycleEdge_word,hv,intervalMap1_succ _ a i hal,LinearMap.comp_apply]
        · rw [suffixEquiv_succ,hq]
          exact FC.stepEquiv_mk S (i.val+2) (intervalCocycle S n a i.castSucc hal w)

theorem intervalCocycle_word (a b : LevelIndex n) (hab : a.val ≤ b.val)
    (w : FC.Cocycle S (a.val+2)) :
    (intervalCocycle S n a b hab w).val = intervalMap1 (SuffixData S n) a b hab w.val :=
  (interval_facts_nat S n b.val (Nat.le_of_lt_succ b.isLt) a hab w).1

theorem suffixEquiv_mk (a b : LevelIndex n) (hab : a.val ≤ b.val)
    (w : FC.Cocycle S (a.val+2)) :
    suffixEquiv S n a b (FC.classOf S (a.val+2) w) =
      FC.classOf S (b.val+2) (intervalCocycle S n a b hab w) :=
  (interval_facts_nat S n b.val (Nat.le_of_lt_succ b.isLt) a hab w).2

theorem coefficient_natural (a b : LevelIndex n) (x : FC.H1 S (a.val+2)) :
    FC.finiteH1Equiv S (b.val+2) (suffixEquiv S n a b x) =
      FC.finiteH1Equiv S (a.val+2) x := by
  change BDL26SeedCohomology.stateZeroEquivalence S
    ((FC.prefixEquiv S (b.val+2)).symm
      (FC.prefixEquiv S (b.val+2) ((FC.prefixEquiv S (a.val+2)).symm x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem class_eq_iff_boundary (r : Nat) (v w : FC.Cocycle S r) :
    FC.classOf S r v = FC.classOf S r w ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val-w.val := by
  constructor
  · intro h
    have hb := (Submodule.Quotient.eq
      (BDL26FiniteCohomology.complex S r).middleCoboundaryInCocycles).mp h
    change v.val-w.val ∈ (BDL26FiniteCohomology.complex S r).firstCoboundaryCheckCode.carrier at hb
    exact (BDL26RZCohomology.mem_boundary_iff _ _).mp hb
  · intro h
    apply (Submodule.Quotient.eq
      (BDL26FiniteCohomology.complex S r).middleCoboundaryInCocycles).mpr
    exact (BDL26RZCohomology.mem_boundary_iff _ _).mpr h

theorem coefficient_eq_iff_boundary (r : Nat) (v w : FC.Cocycle S r) :
    FC.finiteH1Equiv S r (FC.classOf S r v) = FC.finiteH1Equiv S r (FC.classOf S r w) ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val-w.val := by
  constructor
  · intro h
    exact (class_eq_iff_boundary S r v w).mp ((FC.finiteH1Equiv S r).injective h)
  · intro h
    exact congrArg (FC.finiteH1Equiv S r) ((class_eq_iff_boundary S r v w).mpr h)

theorem coefficient_zero_iff_boundary (r : Nat) (v : FC.Cocycle S r) :
    FC.finiteH1Equiv S r (FC.classOf S r v) = 0 ↔
      ∃ f : Word BDL26Field (state S r).presentation.X,
        tannerCoboundary0 (state S r).presentation f = v.val := by
  have hzero : FC.finiteH1Equiv S r (FC.classOf S r (0 : FC.Cocycle S r)) = 0 := by
    rw [map_zero,map_zero]
  have h := coefficient_eq_iff_boundary S r v 0
  simpa only [hzero,ZeroMemClass.coe_zero,sub_zero] using h

/-- The original pure-X adapter is identity on every complete physical word. -/
def pureX (r : Nat) (v : FC.Cocycle S r) :
    BDL26LogicalQubitPreservation.DualRepresentative S r :=
  (BDL26LogicalQubitPreservation.cocycleEquiv S r).symm v

theorem pureX_word (r : Nat) (v : FC.Cocycle S r) : (pureX S r v).val = v.val :=
  BDL26LogicalQubitPreservation.cocycleEquiv_symm_word S r v

theorem pureX_coefficient (r : Nat) (v : FC.Cocycle S r) :
    BDL26LogicalQubitPreservation.logicalEquiv S r
        (BDL26LogicalQubitPreservation.logicalClass S r (pureX S r v)) =
      FC.finiteH1Equiv S r (FC.classOf S r v) := by
  rw [BDL26LogicalQubitPreservation.logicalEquiv_mk]
  change FC.finiteH1Equiv S r (FC.classOf S r
    (BDL26LogicalQubitPreservation.cocycleEquiv S r
      ((BDL26LogicalQubitPreservation.cocycleEquiv S r).symm v))) = _
  rw [LinearEquiv.apply_symm_apply]

end QEC.Coding.BDL26HistoryLogicalResidual
