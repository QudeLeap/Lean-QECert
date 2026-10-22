import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity.Snapshots

/-!
# Real interval maps in the stopped decoder

The maps below compose the actual selected adjacent cochain maps. Their
construction uses no error representative, potential, correction or desired
transport identity. Suffix level zero in the actual family is physical C2.
-/
noncomputable section
namespace QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder
open scoped Classical

universe u v

section LinearIntervals
variable {depth : Nat} {V : LevelIndex depth → Type u}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module BDL26Field (V i)]

/-- Increasing finite composition of the given real adjacent linear maps.
The upper natural index makes every recursive call strictly shorter. -/
def linearUp (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b) :
    V a →ₗ[BDL26Field] V ⟨b,Nat.lt_succ_of_le hb⟩ := by
  cases b with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      exact LinearMap.id
  | succ b =>
      if h : a.val = b+1 then
        have he : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext h
        subst a
        exact LinearMap.id
      else
        exact (edge ⟨b,by omega⟩).comp
          (linearUp edge b (by omega) a (by omega))
termination_by b

theorem linearUp_self
    (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (b : Nat) (hb : b ≤ depth) :
    linearUp edge b hb ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) = LinearMap.id := by
  cases b with
  | zero => rw [linearUp] <;> rfl
  | succ b =>
      rw [linearUp]
      exact dif_pos rfl

theorem linearUp_succ
    (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (b : Nat) (hb : b+1 ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b) :
    linearUp edge (b+1) hb a (ha.trans (Nat.le_succ b)) =
      (edge ⟨b,by omega⟩).comp (linearUp edge b (by omega) a ha) := by
  have hne : ¬ a.val = b+1 := by omega
  rw [linearUp]
  exact dif_neg hne

theorem linearUp_comp
    (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (c : Nat) (hc : c ≤ depth) (b a : LevelIndex depth)
    (hbc : b.val ≤ c) (hab : a.val ≤ b.val) :
    linearUp edge c hc a (hab.trans hbc) =
      (linearUp edge c hc b hbc).comp
        (linearUp edge b.val (Nat.le_of_lt_succ b.isLt) a hab) := by
  induction c generalizing b a with
  | zero =>
      have hb0 : b = ⟨0,Nat.lt_succ_of_le hc⟩ := Fin.ext (by change b.val = 0; omega)
      subst b
      have ha0 : a = ⟨0,Nat.lt_succ_of_le hc⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      simp only [linearUp_self, LinearMap.id_comp]
  | succ c ih =>
      by_cases he : b.val = c+1
      · have hb' : b = ⟨c+1,Nat.lt_succ_of_le hc⟩ := Fin.ext he
        subst b
        rw [linearUp_self]
        rfl
      · have hbc' : b.val ≤ c := by omega
        rw [linearUp_succ edge c hc a (hab.trans hbc'),
          linearUp_succ edge c hc b hbc',
          ih (by omega) b a hbc' hab, LinearMap.comp_assoc]

end LinearIntervals

section DecoderIntervals
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

def intervalMap0 (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) (hab : a.val ≤ b.val) :
    D.family.Cochain0 a →ₗ[BDL26Field] D.family.Cochain0 b :=
  linearUp (fun i => (D.selectedMap i).map0) b.val
    (Nat.le_of_lt_succ b.isLt) a hab

def intervalMap1 (D : BDL26DecoderData depth C0 C1 C2)
    (a b : LevelIndex depth) (hab : a.val ≤ b.val) :
    D.family.Cochain1 a →ₗ[BDL26Field] D.family.Cochain1 b :=
  linearUp (fun i => (D.selectedMap i).map1) b.val
    (Nat.le_of_lt_succ b.isLt) a hab

theorem intervalMap0_self (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) : intervalMap0 D a a (Nat.le_refl _) = LinearMap.id :=
  linearUp_self _ a.val _

theorem intervalMap1_self (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) : intervalMap1 D a a (Nat.le_refl _) = LinearMap.id :=
  linearUp_self _ a.val _

theorem intervalMap0_comp (D : BDL26DecoderData depth C0 C1 C2)
    (a b c : LevelIndex depth) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalMap0 D a c (hab.trans hbc) =
      (intervalMap0 D b c hbc).comp (intervalMap0 D a b hab) :=
  linearUp_comp _ c.val _ b a hbc hab

theorem intervalMap1_comp (D : BDL26DecoderData depth C0 C1 C2)
    (a b c : LevelIndex depth) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    intervalMap1 D a c (hab.trans hbc) =
      (intervalMap1 D b c hbc).comp (intervalMap1 D a b hab) :=
  linearUp_comp _ c.val _ b a hbc hab

theorem intervalMap0_succ (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) (i : StepIndex depth) (hai : a.val ≤ i.val) :
    intervalMap0 D a i.succ (by change a.val ≤ i.val+1; omega) =
      ((D.selectedMap i).map0).comp (intervalMap0 D a i.castSucc hai) :=
  linearUp_succ _ i.val (Nat.le_of_lt_succ i.succ.isLt) a hai

theorem intervalMap1_succ (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) (i : StepIndex depth) (hai : a.val ≤ i.val) :
    intervalMap1 D a i.succ (by change a.val ≤ i.val+1; omega) =
      ((D.selectedMap i).map1).comp (intervalMap1 D a i.castSucc hai) :=
  linearUp_succ _ i.val (Nat.le_of_lt_succ i.succ.isLt) a hai

theorem intervalMap0_adjacent (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) :
    intervalMap0 D i.castSucc i.succ (by simp) = (D.selectedMap i).map0 := by
  rw [intervalMap0_succ D i.castSucc i (Nat.le_refl _), intervalMap0_self]
  rfl

theorem intervalMap1_adjacent (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) :
    intervalMap1 D i.castSucc i.succ (by simp) = (D.selectedMap i).map1 := by
  rw [intervalMap1_succ D i.castSucc i (Nat.le_refl _), intervalMap1_self]
  rfl

/-- The whole degree-zero potential commutes through every actual interval. -/
theorem intervalMap_commutes0 (D : BDL26DecoderData depth C0 C1 C2)
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b)
    (p : D.family.Cochain0 a) :
    D.family.coboundary0 ⟨b,Nat.lt_succ_of_le hb⟩
        (intervalMap0 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha p) =
      intervalMap1 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha (D.family.coboundary0 a p) := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      rw [intervalMap0_self, intervalMap1_self]
      rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        rw [intervalMap0_self, intervalMap1_self]
        rfl
      · have hal : a.val ≤ b := by omega
        let i : StepIndex depth := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        change D.family.coboundary0 i.succ (intervalMap0 D a i.succ ha p) =
          intervalMap1 D a i.succ ha (D.family.coboundary0 a p)
        rw [intervalMap0_succ D a i hal, intervalMap1_succ D a i hal]
        change D.family.coboundary0 i.succ
          ((D.selectedMap i).map0 (intervalMap0 D a i.castSucc hal p)) = _
        have hc := LinearMap.congr_fun (D.selectedMap i).commutes_coboundary0
          (intervalMap0 D a i.castSucc hal p)
        simp only [LinearMap.comp_apply] at hc
        have hp := ih (by omega) a hal p
        change D.family.coboundary0 i.castSucc (intervalMap0 D a i.castSucc hal p) =
          intervalMap1 D a i.castSucc hal (D.family.coboundary0 a p) at hp
        rw [hc]
        exact congrArg ((D.selectedMap i).map1) hp

/-- Interval lifting is exactly the old full correction lift, not merely
an alternative word with the same syndrome. -/
theorem liftCorrection_intervalMap1 (D : BDL26DecoderData depth C0 C1 C2)
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b)
    (w : D.family.Cochain1 a) :
    liftCorrection D ⟨b,Nat.lt_succ_of_le hb⟩
      (intervalMap1 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha w) = liftCorrection D a w := by
  induction b generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le hb⟩ := Fin.ext (by change a.val = 0; omega)
      subst a
      rw [intervalMap1_self]
      rfl
  | succ b ih =>
      by_cases he : a.val = b+1
      · have he' : a = ⟨b+1,Nat.lt_succ_of_le hb⟩ := Fin.ext he
        subst a
        rw [intervalMap1_self]
        rfl
      · have hal : a.val ≤ b := by omega
        let i : StepIndex depth := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        change liftCorrection D i.succ (intervalMap1 D a i.succ ha w) = liftCorrection D a w
        rw [intervalMap1_succ D a i hal]
        change liftCorrection D i.succ
          ((D.selectedMap i).map1 (intervalMap1 D a i.castSucc hal w)) = _
        rw [← liftCorrection_map1_eq]
        exact ih (by omega) a hal w

theorem intervalMap1_top (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) (w : D.family.Cochain1 a) :
    intervalMap1 D a (TopIndex depth) (Nat.le_of_lt_succ a.isLt) w =
      liftCorrection D a w := by
  have h := liftCorrection_intervalMap1 D depth (Nat.le_refl _) a
    (Nat.le_of_lt_succ a.isLt) w
  rw [liftCorrection_top] at h
  exact h

end DecoderIntervals
end QEC.Coding.BDL26HistoryErrorTelescoping
