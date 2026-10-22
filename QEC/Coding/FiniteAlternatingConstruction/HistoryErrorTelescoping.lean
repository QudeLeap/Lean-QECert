import QEC.Coding.FiniteAlternatingConstruction.HistoryErrorTelescoping.HistorySums
import QEC.Coding.FiniteAlternatingConstruction.HistorySyndromeSensitivity

/-!
# Full-word telescoping of the actual C2-stopped history

Every descent is initialized at the supplied genuine upper word. Complete
degree-zero potentials are constructed internally and accumulated through the
real selected map0. Original assembled prefixes, including the C2 correction,
are retained. The physical-error consumer shares one background u and u+e.
These are algebraic word equalities, without locality or stability claims.
-/
noncomputable section
namespace QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical

universe u v w

theorem word_add_self {I : Type u} (x : Word BDL26Field I) : x+x=0 := by
  funext i
  exact ZModModule.add_self (x i)

/-- F2 cancellation is coordinatewise, including empty coordinate carriers. -/
theorem word_toggle {I : Type u} (x y p : Word BDL26Field I) (h : x=y+p) : y=x+p := by
  rw [h]
  calc
    y = y+(p+p) := by rw [word_add_self,add_zero]
    _ = y+p+p := by ac_rfl

theorem balance_full_word {I : Type u} (x y c k p : Word BDL26Field I)
    (h : x=y+c+p) : y+(c+k)=x+k+p := by
  rw [h]
  symm
  calc
    (y+c+p)+k+p = (y+(c+k))+(p+p) := by ac_rfl
    _ = y+(c+k) := by rw [word_add_self,add_zero]

theorem combine_full_words {I : Type u} {J : Type v} {K : Type w}
    (f : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field J)
    (g : Word BDL26Field K →ₗ[BDL26Field] Word BDL26Field J)
    (u e d d' : Word BDL26Field J) (y y' : Word BDL26Field I)
    (p p' : Word BDL26Field K)
    (h : f y=u+d+g p) (h' : f y'=u+e+d'+g p') :
    e+d+d'=f (y+y')+g (p+p') := by
  rw [map_add,map_add,h,h']
  calc
    e+d+d' = (u+u)+(e+d+d')+((g p+g p)+(g p'+g p')) := by
      rw [word_add_self,word_add_self,word_add_self,zero_add,zero_add,add_zero]
    _ = (u+d+g p)+(u+e+d'+g p')+(g p+g p') := by ac_rfl

variable (S : OddScale) (n : Nat)

/-- The actual descent at every lower level, starting at this exact upper word. -/
def descentWord (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) : (SuffixData S n).family.Cochain1 a :=
  errorDown S n b.val (Nat.le_of_lt_succ b.isLt) u a ha

theorem descentWord_self (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b) :
    descentWord S n b u b (Nat.le_refl _) = u := errorDown_self S n b.val _ u

theorem actualInputs_prefix (sigma : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val) :
    prefixInput (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) b.val
      (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) a hab = actualInputs S n sigma a :=
  (prefixInput_comp (SuffixData S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) n (Nat.le_refl _)
    sigma b a (Nat.le_of_lt_succ b.isLt) hab).symm

theorem descentWord_valid (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 a (descentWord S n b u a ha) =
      (actualInputs S n sigma a).val := by
  have hin := hu.trans (actualInputs_readout S n sigma b)
  have hd := errorDown_valid S n b.val (Nat.le_of_lt_succ b.isLt) u
    (actualInputs S n sigma b) hin a ha
  exact hd.trans (congrArg Subtype.val (actualInputs_prefix S n sigma a b ha))

theorem descentWord_readout (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 a (descentWord S n b u a ha) =
      actualReadout S n sigma a :=
  (descentWord_valid S n sigma b u hu a ha).trans (actualInputs_readout S n sigma a).symm

/-- The entire original one-run upper degree-zero potential. -/
def descentPotential (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (i : StepIndex n) (hi : i.val < b.val) : (SuffixData S n).family.Cochain0 i.succ :=
  fullPotential S (n+2) (LevelTwoHistory.physicalStep i)
    (by simp only [LevelTwoHistory.physicalStep_val]; omega)
    (physicalUpperError S n i (descentWord S n b u i.succ (by change i.val+1 ≤ b.val; omega)))

theorem descentWord_step (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (i : StepIndex n) (hi : i.val < b.val) :
    ((SuffixData S n).selectedMap i).map1
        (descentWord S n b u i.castSucc (by change i.val ≤ b.val; omega)) =
      descentWord S n b u i.succ (by change i.val+1 ≤ b.val; omega) +
        (actualOutput S n sigma i).correction +
        (SuffixData S n).family.coboundary0 i.succ (descentPotential S n b u i hi) := by
  let e := descentWord S n b u i.succ (by change i.val+1 ≤ b.val; omega)
  let k := LevelTwoHistory.physicalStep i
  have hk : 2 ≤ k.val := by simp only [k,LevelTwoHistory.physicalStep_val]; omega
  have hl : descentWord S n b u i.castSucc (by change i.val ≤ b.val; omega) =
      lowerRepresentative S (n+2) k hk e :=
    errorDown_step S n b.val (Nat.le_of_lt_succ b.isLt) u i hi
  have hin : errorInput S (n+2) k e = actualInputs S n sigma i.succ :=
    Subtype.ext (descentWord_valid S n sigma b u hu i.succ (by change i.val+1 ≤ b.val; omega))
  have hs := (lowerRepresentative_spec S (n+2) k hk e).1
  rw [hin] at hs
  rw [hl,LevelTwoHistory.suffix_selected_map1,actualOutput_correction]
  exact hs

/-- Full potential accumulation by a finite recursion over the interval.
The only added term is the actual entire descentPotential at the next step. -/
def accumulatedPotential (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (a : LevelIndex n) (c : Nat) (hc : c ≤ b.val) (ha : a.val ≤ c) :
    (SuffixData S n).family.Cochain0
      ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ := by
  cases c with
  | zero => exact 0
  | succ c =>
      if h : a.val = c+1 then exact 0
      else
        have hcn : c < n := Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc) (Nat.le_of_lt_succ b.isLt)
        let i : StepIndex n := ⟨c,hcn⟩
        exact ((SuffixData S n).selectedMap i).map0
          (accumulatedPotential b u a c (by omega) (by omega)) +
            descentPotential S n b u i (by change c < b.val; omega)
termination_by c

theorem accumulatedPotential_zero_eq (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a : LevelIndex n) (ha : a.val ≤ 0) :
    accumulatedPotential S n b u a 0 (Nat.zero_le _) ha = 0 := by
  rw [accumulatedPotential] <;> rfl

theorem accumulatedPotential_succ_eq (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a : LevelIndex n)
    (c : Nat) (hc : c+1 ≤ b.val) (ha : a.val ≤ c+1) :
    accumulatedPotential S n b u a (c+1) hc ha =
      if h : a.val = c+1 then 0 else
        let i : StepIndex n := ⟨c,Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc) (Nat.le_of_lt_succ b.isLt)⟩
        ((SuffixData S n).selectedMap i).map0
          (accumulatedPotential S n b u a c (by omega) (by omega)) +
            descentPotential S n b u i (by change c < b.val; omega) := by
  rw [accumulatedPotential] <;> rfl

theorem accumulatedPotential_self (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (a : LevelIndex n) (hab : a.val ≤ b.val) :
    accumulatedPotential S n b u a a.val hab (Nat.le_refl _) = 0 := by
  rcases a with ⟨a,ha⟩
  cases a with
  | zero => exact accumulatedPotential_zero_eq S n b u ⟨0,ha⟩ (Nat.le_refl _)
  | succ c =>
      rw [accumulatedPotential_succ_eq,dif_pos rfl]

theorem accumulatedPotential_succ (b : LevelIndex n) (u : (SuffixData S n).family.Cochain1 b)
    (a : LevelIndex n) (i : StepIndex n) (hib : i.val < b.val) (hai : a.val ≤ i.val) :
    accumulatedPotential S n b u a (i.val+1) (by omega) (by omega) =
      ((SuffixData S n).selectedMap i).map0
        (accumulatedPotential S n b u a i.val (by omega) hai) + descentPotential S n b u i hib := by
  have hn : ¬ a.val = i.val+1 := by omega
  rw [accumulatedPotential_succ_eq]
  exact dif_neg hn

theorem accumulatedPotential_comp (upper : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 upper) (c : Nat) (hc : c ≤ upper.val)
    (b a : LevelIndex n) (hbc : b.val ≤ c) (hab : a.val ≤ b.val) :
    accumulatedPotential S n upper u a c hc (hab.trans hbc) =
      intervalMap0 (SuffixData S n) b
          ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ upper.isLt))⟩ hbc
          (accumulatedPotential S n upper u a b.val (hbc.trans hc) hab) +
        accumulatedPotential S n upper u b c hc hbc := by
  induction c generalizing b a with
  | zero =>
      have hb0 : b = ⟨0,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ upper.isLt))⟩ :=
        Fin.ext (by change b.val = 0; omega)
      subst b
      have ha0 : a = ⟨0,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ upper.isLt))⟩ :=
        Fin.ext (by change a.val = 0; omega)
      subst a
      let z : LevelIndex n := ⟨0,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ upper.isLt))⟩
      have hz : z.val ≤ 0 := Nat.le_refl 0
      change accumulatedPotential S n upper u z 0 hc hz =
        intervalMap0 (SuffixData S n) z z (Nat.le_refl _)
            (accumulatedPotential S n upper u z 0 hc hz) +
          accumulatedPotential S n upper u z 0 hc hz
      simp only [accumulatedPotential_zero_eq,map_zero,add_zero]
  | succ c ih =>
      by_cases he : b.val = c+1
      · have hb' : b = ⟨c+1,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ upper.isLt))⟩ :=
          Fin.ext he
        subst b
        rw [accumulatedPotential_self,intervalMap0_self,LinearMap.id_apply,add_zero]
      · have hbc' : b.val ≤ c := by omega
        have hcn : c < n := Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc) (Nat.le_of_lt_succ upper.isLt)
        let i : StepIndex n := ⟨c,hcn⟩
        have hi : i.val < upper.val := by change c < upper.val; omega
        let qa : (SuffixData S n).family.Cochain0 i.castSucc :=
          accumulatedPotential S n upper u a c (by omega) (hab.trans hbc')
        let qb : (SuffixData S n).family.Cochain0 i.castSucc :=
          accumulatedPotential S n upper u b c (by omega) hbc'
        let qab : (SuffixData S n).family.Cochain0 b :=
          accumulatedPotential S n upper u a b.val (hbc.trans hc) hab
        let qac : (SuffixData S n).family.Cochain0 i.succ :=
          accumulatedPotential S n upper u a (c+1) hc (hab.trans hbc)
        let qbc : (SuffixData S n).family.Cochain0 i.succ :=
          accumulatedPotential S n upper u b (c+1) hc hbc
        have hqa := accumulatedPotential_succ S n upper u a i hi (hab.trans hbc')
        have hqb := accumulatedPotential_succ S n upper u b i hi hbc'
        change qac = ((SuffixData S n).selectedMap i).map0 qa +
          descentPotential S n upper u i hi at hqa
        change qbc = ((SuffixData S n).selectedMap i).map0 qb +
          descentPotential S n upper u i hi at hqb
        have hp := ih (by omega) b a hbc' hab
        change qa = intervalMap0 (SuffixData S n) b i.castSucc hbc' qab + qb at hp
        change qac = intervalMap0 (SuffixData S n) b i.succ hbc qab + qbc
        rw [hqa,hqb,
          intervalMap0_succ (SuffixData S n) b i hbc',LinearMap.comp_apply,
          hp,map_add]
        ac_rfl

theorem actual_interval_word_nat (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (c : Nat) (hc : c ≤ b.val) (a : LevelIndex n) (ha : a.val ≤ c) :
    intervalMap1 (SuffixData S n) a
        ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ ha
        (descentWord S n b u a (ha.trans hc)) =
      descentWord S n b u ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ hc +
        correctionIntervalSum S n sigma a
          ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ +
        (SuffixData S n).family.coboundary0 _ (accumulatedPotential S n b u a c hc ha) := by
  induction c generalizing a with
  | zero =>
      have he : a = ⟨0,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ :=
        Fin.ext (by change a.val = 0; omega)
      subst a
      rw [intervalMap1_self,correctionIntervalSum_self,accumulatedPotential_self,map_zero,
        add_zero,add_zero]
      rfl
  | succ c ih =>
      by_cases he : a.val = c+1
      · have he' : a = ⟨c+1,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ := Fin.ext he
        subst a
        rw [intervalMap1_self,correctionIntervalSum_self,accumulatedPotential_self,map_zero,
          add_zero,add_zero]
        rfl
      · have hal : a.val ≤ c := by omega
        have hcn : c < n := Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc) (Nat.le_of_lt_succ b.isLt)
        let i : StepIndex n := ⟨c,hcn⟩
        have hib : i.val < b.val := by change c < b.val; omega
        have hp := ih (by omega) a hal
        change intervalMap1 (SuffixData S n) a i.castSucc hal
            (descentWord S n b u a (by omega)) =
          descentWord S n b u i.castSucc (by change i.val ≤ b.val; exact Nat.le_of_lt hib) +
            correctionIntervalSum S n sigma a i.castSucc +
            (SuffixData S n).family.coboundary0 i.castSucc
              (accumulatedPotential S n b u a c (by omega) hal) at hp
        have hs := descentWord_step S n sigma b u hu i hib
        have hd := LinearMap.congr_fun ((SuffixData S n).selectedMap i).commutes_coboundary0
          (accumulatedPotential S n b u a c (by omega) hal)
        simp only [LinearMap.comp_apply] at hd
        change (SuffixData S n).family.coboundary0 i.succ
            (((SuffixData S n).selectedMap i).map0
              (accumulatedPotential S n b u a c (by omega) hal)) =
          ((SuffixData S n).selectedMap i).map1
            ((SuffixData S n).family.coboundary0 i.castSucc
              (accumulatedPotential S n b u a c (by omega) hal)) at hd
        have hq := accumulatedPotential_succ S n b u a i hib hal
        change accumulatedPotential S n b u a (c+1) hc ha =
          ((SuffixData S n).selectedMap i).map0
            (accumulatedPotential S n b u a c (by omega) hal) + descentPotential S n b u i hib at hq
        change intervalMap1 (SuffixData S n) a i.succ ha
            (descentWord S n b u a (ha.trans hc)) =
          descentWord S n b u i.succ hc + correctionIntervalSum S n sigma a i.succ +
            (SuffixData S n).family.coboundary0 i.succ (accumulatedPotential S n b u a (c+1) hc ha)
        rw [intervalMap1_succ _ a i hal,LinearMap.comp_apply,hp,map_add,map_add,
          hs,← hd,correctionIntervalSum_succ S n sigma a i hal,
          hq,map_add]
        ac_rfl

theorem actual_interval_word (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a c : LevelIndex n) (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    intervalMap1 (SuffixData S n) a c hac (descentWord S n b u a (hac.trans hcb)) =
      descentWord S n b u c hcb + correctionIntervalSum S n sigma a c +
        (SuffixData S n).family.coboundary0 c
          (accumulatedPotential S n b u a c.val hcb hac) :=
  actual_interval_word_nat S n sigma b u hu c.val hcb a hac

theorem accumulatedPotential_boundary_zero (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a c : LevelIndex n)
    (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 c
      ((SuffixData S n).family.coboundary0 c (accumulatedPotential S n b u a c.val hcb hac)) = 0 := by
  have h := LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0 c)
    (accumulatedPotential S n b u a c.val hcb hac)
  exact h

theorem actual_assembled_interval (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a c : LevelIndex n) (hac : a.val ≤ c.val) (hcb : c.val ≤ b.val) :
    descentWord S n b u c hcb + assembledPrefix S n sigma c =
      intervalMap1 (SuffixData S n) a c hac
        (descentWord S n b u a (hac.trans hcb) + assembledPrefix S n sigma a) +
        (SuffixData S n).family.coboundary0 c
          (accumulatedPotential S n b u a c.val hcb hac) := by
  rw [assembledPrefix_split S n sigma a c hac,map_add]
  exact balance_full_word _ _ _ _ _ (actual_interval_word S n sigma b u hu a c hac hcb)

/-- Arbitrary genuine top word; neither it nor the lower prefix is re-chosen. -/
theorem actual_fullspan (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
        (descentWord S n (TopIndex n) u 0 (Nat.zero_le _) +
          (actualBase S n).decode (actualInputs S n sigma 0)) =
      u + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
        (SuffixData S n).family.coboundary0 (TopIndex n)
          (accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)) := by
  have hv : (SuffixData S n).family.coboundary1 (TopIndex n) u =
      actualReadout S n sigma (TopIndex n) := hu.trans (actualReadout_top S n sigma).symm
  have h := actual_assembled_interval S n sigma (TopIndex n) u hv 0 (TopIndex n)
    (Nat.zero_le _) (Nat.le_refl _)
  rw [descentWord_self,assembledPrefix_top,assembledPrefix_zero] at h
  exact word_toggle _ _ _ h

/-- The sigma-only consumer selects a genuine top preimage internally. -/
theorem actual_fullspan_exists (sigma : TopInput S n) :
    ∃ (l : (SuffixData S n).family.Cochain1 0)
      (q : (SuffixData S n).family.Cochain0 (TopIndex n)),
      (SuffixData S n).family.coboundary1 0 l = actualReadout S n sigma 0 ∧
      ∃ u : (SuffixData S n).family.Cochain1 (TopIndex n),
        (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val ∧
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (l + (actualBase S n).decode (actualInputs S n sigma 0)) =
          u + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
            (SuffixData S n).family.coboundary0 (TopIndex n) q := by
  obtain ⟨u,hu⟩ := sigma.property
  have hv := hu.trans (actualReadout_top S n sigma).symm
  exact ⟨descentWord S n (TopIndex n) u 0 (Nat.zero_le _),
    accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _),
    descentWord_readout S n sigma (TopIndex n) u hv 0 (Nat.zero_le _),u,hu,
    actual_fullspan S n sigma u hu⟩

theorem coherent_top_initialization (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    ∃ u : (SuffixData S n).family.Cochain1 (TopIndex n),
      (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val ∧
      (SuffixData S n).family.coboundary1 (TopIndex n) (u+e) = (perturbTop S n sigma e).val ∧
      descentWord S n (TopIndex n) u (TopIndex n) (Nat.le_refl _) +
        descentWord S n (TopIndex n) (u+e) (TopIndex n) (Nat.le_refl _) = e := by
  obtain ⟨u,hu,hue⟩ := perturbTop_preimage S n sigma e
  refine ⟨u,hu,hue,?_⟩
  rw [descentWord_self,descentWord_self,← add_assoc,word_add_self,zero_add]

/-- Both entire original corrections and both physical-C2 base corrections
remain in the actual physical-error residual. The one background preimage
is shared by the two descents; h and R are internally constructed words. -/
theorem actual_two_run (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    ∃ (h : (SuffixData S n).family.Cochain1 0)
      (R : (SuffixData S n).family.Cochain0 (TopIndex n)),
      (SuffixData S n).family.coboundary1 0 h =
        actualReadout S n sigma 0 + actualReadout S n (perturbTop S n sigma e) 0 ∧
      e + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
          historyLiftedCorrection (SuffixData S n) (actualHistory S n (perturbTop S n sigma e)) =
        intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (h + (actualBase S n).decode (actualInputs S n sigma 0) +
            (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0)) +
          (SuffixData S n).family.coboundary0 (TopIndex n) R ∧
      (SuffixData S n).family.coboundary1 (TopIndex n)
        ((SuffixData S n).family.coboundary0 (TopIndex n) R) = 0 ∧
      (SuffixData S n).family.coboundary1 0
        (h + (actualBase S n).decode (actualInputs S n sigma 0) +
          (actualBase S n).decode (actualInputs S n (perturbTop S n sigma e) 0)) = 0 ∧
      (SuffixData S n).family.coboundary1 (TopIndex n)
        (e + historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma) +
          historyLiftedCorrection (SuffixData S n) (actualHistory S n (perturbTop S n sigma e))) = 0 := by
  obtain ⟨u,hu,hue⟩ := perturbTop_preimage S n sigma e
  let tau := perturbTop S n sigma e
  let l := descentWord S n (TopIndex n) u 0 (Nat.zero_le _)
  let l' := descentWord S n (TopIndex n) (u+e) 0 (Nat.zero_le _)
  let q := accumulatedPotential S n (TopIndex n) u 0 n (Nat.le_refl _) (Nat.zero_le _)
  let q' := accumulatedPotential S n (TopIndex n) (u+e) 0 n (Nat.le_refl _) (Nat.zero_le _)
  let bs := (actualBase S n).decode (actualInputs S n sigma 0)
  let bt := (actualBase S n).decode (actualInputs S n tau 0)
  have hv := hu.trans (actualReadout_top S n sigma).symm
  have hv' := hue.trans (actualReadout_top S n tau).symm
  have hl : (SuffixData S n).family.coboundary1 0 l = actualReadout S n sigma 0 :=
    descentWord_readout S n sigma (TopIndex n) u hv 0 (Nat.zero_le _)
  have hl' : (SuffixData S n).family.coboundary1 0 l' = actualReadout S n tau 0 :=
    descentWord_readout S n tau (TopIndex n) (u+e) hv' 0 (Nat.zero_le _)
  have hb : (SuffixData S n).family.coboundary1 0 bs = actualReadout S n sigma 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n sigma 0).symm
  have hb' : (SuffixData S n).family.coboundary1 0 bt = actualReadout S n tau 0 :=
    ((actualBase S n).rightInverse _).trans (actualInputs_readout S n tau 0).symm
  have hs := actual_fullspan S n sigma u hu
  have ht := actual_fullspan S n tau (u+e) hue
  have heq := combine_full_words
    (intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _))
    ((SuffixData S n).family.coboundary0 (TopIndex n)) u e
    (historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma))
    (historyLiftedCorrection (SuffixData S n) (actualHistory S n tau))
    (l+bs) (l'+bt) q q' hs ht
  have hinside : (l+bs)+(l'+bt)=(l+l')+bs+bt := by ac_rfl
  rw [hinside] at heq
  refine ⟨l+l',q+q',?_,heq,?_,?_,?_⟩
  · rw [map_add,hl,hl']
  · exact LinearMap.congr_fun ((SuffixData S n).family.coboundary1_comp_coboundary0
      (TopIndex n)) (q+q')
  · change (SuffixData S n).family.coboundary1 0 ((l+l')+bs+bt)=0
    rw [map_add,map_add,map_add,hl,hl',hb,hb']
    calc
      (actualReadout S n sigma 0 + actualReadout S n tau 0) + actualReadout S n sigma 0 +
          actualReadout S n tau 0 =
        (actualReadout S n sigma 0 + actualReadout S n sigma 0) +
          (actualReadout S n tau 0 + actualReadout S n tau 0) := by ac_rfl
      _ = 0 := by rw [word_add_self,word_add_self,add_zero]
  · rw [map_add,map_add]
    have hs' : (SuffixData S n).family.coboundary1 (TopIndex n)
        (historyLiftedCorrection (SuffixData S n) (actualHistory S n sigma)) = sigma.val :=
      actualHistory_syndrome S n sigma
    have ht' : (SuffixData S n).family.coboundary1 (TopIndex n)
        (historyLiftedCorrection (SuffixData S n) (actualHistory S n tau)) = tau.val :=
      actualHistory_syndrome S n tau
    rw [hs',ht']
    change (SuffixData S n).family.coboundary1 (TopIndex n) e + sigma.val +
      (sigma.val + (SuffixData S n).family.coboundary1 (TopIndex n) e) = 0
    calc
      _ = ((SuffixData S n).family.coboundary1 (TopIndex n) e +
          (SuffixData S n).family.coboundary1 (TopIndex n) e) + (sigma.val+sigma.val) := by ac_rfl
      _ = 0 := by rw [word_add_self,word_add_self,add_zero]

/-- Source-even depth includes k=1, whose suffix has no nonbase step. -/
theorem source_even_depth (k : Nat) (hk : 1 ≤ k) : 2*(k-1)+2=2*k := by omega

def sourceEvenInput (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k))) :
    TopInput S (2*(k-1)) := by
  cases k with
  | zero => omega
  | succ k => exact sigma

def sourceEvenError (k : Nat) (hk : 1 ≤ k)
    (e : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k))) :
    (SuffixData S (2*(k-1))).family.Cochain1 (TopIndex (2*(k-1))) := by
  cases k with
  | zero => omega
  | succ k => exact e

theorem source_even_two_run (k : Nat) (hk : 1 ≤ k)
    (sigma : (indexedFamily S (2*k)).Syndrome (TopIndex (2*k)))
    (e : (indexedFamily S (2*k)).Cochain1 (TopIndex (2*k))) :
    let m := 2*(k-1)
    let s := sourceEvenInput S k hk sigma
    let v := sourceEvenError S k hk e
    ∃ (h : (SuffixData S m).family.Cochain1 0)
      (R : (SuffixData S m).family.Cochain0 (TopIndex m)),
      (SuffixData S m).family.coboundary1 0 h =
        actualReadout S m s 0 + actualReadout S m (perturbTop S m s v) 0 ∧
      v + historyLiftedCorrection (SuffixData S m) (actualHistory S m s) +
          historyLiftedCorrection (SuffixData S m) (actualHistory S m (perturbTop S m s v)) =
        intervalMap1 (SuffixData S m) 0 (TopIndex m) (Nat.zero_le _)
          (h + (actualBase S m).decode (actualInputs S m s 0) +
            (actualBase S m).decode (actualInputs S m (perturbTop S m s v) 0)) +
          (SuffixData S m).family.coboundary0 (TopIndex m) R ∧
      (SuffixData S m).family.coboundary1 (TopIndex m)
        ((SuffixData S m).family.coboundary0 (TopIndex m) R) = 0 ∧
      (SuffixData S m).family.coboundary1 0
        (h + (actualBase S m).decode (actualInputs S m s 0) +
          (actualBase S m).decode (actualInputs S m (perturbTop S m s v) 0)) = 0 ∧
      (SuffixData S m).family.coboundary1 (TopIndex m)
        (v + historyLiftedCorrection (SuffixData S m) (actualHistory S m s) +
          historyLiftedCorrection (SuffixData S m) (actualHistory S m (perturbTop S m s v))) = 0 := by
  cases k with
  | zero => omega
  | succ k => exact actual_two_run S (2*k) sigma e

end QEC.Coding.BDL26HistoryErrorTelescoping
