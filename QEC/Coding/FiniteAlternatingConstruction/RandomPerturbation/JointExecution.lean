import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Execution
import QEC.Coding.ProbabilisticConstruction.Resampling.ParameterizedExecution
import QEC.Coding.ProbabilisticConstruction.SphericalCap.JointTriangleHit

/-!
# A fixed representation of the original geometric execution

All four-label sets are used only to represent a varying event subtype. A label
is enabled exactly when it is an original eligible event. The lemmas below
identify the selected original event and every original counter, for every
incoming map and every table, including nonterminating executions.
-/
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory

abbrev MasterEvent (P : TannerSquarePresentation) :=
  {s : Finset (Triangle P) // s.card = 4}

instance masterEventFintype (P : TannerSquarePresentation) : Fintype (MasterEvent P) :=
  Fintype.ofFinite _

def masterScanKey (P : TannerSquarePresentation) (e : MasterEvent P) : List ℕ :=
  (e.val.image (triangleKey P)).sort (· ≤ ·)

theorem masterScanKey_injective (P : TannerSquarePresentation) :
    Function.Injective (masterScanKey P) := by
  intro a b h
  have he := congrArg List.toFinset h
  simp only [masterScanKey, Finset.sort_toFinset] at he
  exact Subtype.ext (Finset.image_injective (triangleKey_injective P) he)

instance masterEventOrder (P : TannerSquarePresentation) : LinearOrder (MasterEvent P) :=
  let order := LinearOrder.lift' (masterScanKey P) (masterScanKey_injective P)
  { order.toPartialOrder with
    le_total := order.le_total
    toDecidableLE := order.toDecidableLE
    toDecidableLT := order.toDecidableLT
    toDecidableEq := Subtype.instDecidableEq
    compare := fun a b => @compareOfLessAndEq (MasterEvent P) a b order.toLT
      (order.toDecidableLT a b) Subtype.instDecidableEq
    compare_eq_compareOfLessAndEq := by intro a b; rfl }

instance masterEventMeasurableSpace (P : TannerSquarePresentation) :
    MeasurableSpace (MasterEvent P) := ⊤
instance masterEventMeasurableSingleton (P : TannerSquarePresentation) :
    MeasurableSingletonClass (MasterEvent P) := ⟨fun _ => trivial⟩

def eventToMaster (P : TannerSquarePresentation) (J : Vertex P → Space) (r : ℝ)
    (e : Event P J r) : MasterEvent P := ⟨e.val,e.property.1⟩

theorem eventToMaster_priority (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    eventToMaster P J r e ≤ eventToMaster P J r f ↔ e ≤ f := Iff.rfl

/-- The scan compares sorted triangle keys, rather than inherited subset order. -/
theorem eventToMaster_scan_priority (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (e f : Event P J r) :
    (masterEventOrder P).toLE.le (eventToMaster P J r e) (eventToMaster P J r f) ↔
      (geometricEventOrder P J r).toLE.le e f := Iff.rfl

/-- Choice of decision proofs does not change any result of the original scan. -/
private theorem select_decidable_eq {W I : Type*} [Fintype I] [LinearOrder I]
    (B : I → Set W) (d : ∀ i, DecidablePred (· ∈ B i)) (w : W) :
    @select W I B d _ _ w =
      @select W I B (fun i u => Classical.propDecidable (u ∈ B i)) _ _ w := by
  have hd : d = (fun i u => Classical.propDecidable (u ∈ B i)) := Subsingleton.elim _ _
  cases hd
  rfl

def masterSupport (P : TannerSquarePresentation) (e : MasterEvent P) : Finset (Vertex P) :=
  e.val.biUnion (triangleSupport P)

theorem master_nonempty (P : TannerSquarePresentation) (e : MasterEvent P) :
    e.val.Nonempty := Finset.card_pos.mp (by rw [e.property]; decide)

def masterAnchor (P : TannerSquarePresentation) (e : MasterEvent P) : Triangle P := by
  letI : LinearOrder (Triangle P) := LinearOrder.lift' (triangleKey P) (triangleKey_injective P)
  exact e.val.min' (master_nonempty P e)

def masterVertex (P : TannerSquarePresentation) (e : MasterEvent P) (a : e.val)
    (i : Fin 3) : masterSupport P e :=
  ⟨triangleVertex P a.val i, Finset.mem_biUnion.mpr
    ⟨a.val,a.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩⟩

def masterCenter (P : TannerSquarePresentation) (J : Vertex P → Space)
    (lambda : ℝ) (K : ℕ) (e : MasterEvent P) (g : Grid K) : Space :=
  lambda • oldAnchor P J (masterAnchor P e)+gridPoint K g

/-- Ineligible labels are false. The enabled geometric predicate is unchanged. -/
def masterBad (P : TannerSquarePresentation) (radius lambda : ℝ) (K : ℕ)
    (J : Vertex P → Space) (e : MasterEvent P) : Set (masterSupport P e → Space) :=
  {u | Eligible P J radius e.val ∧ ∃ g : Grid K, ∀ a : e.val,
    (fun i => u (masterVertex P e a i)) ∈
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (masterCenter P J lambda K e g) 2}

theorem continuous_oldAnchor (P : TannerSquarePresentation) (a : Triangle P) :
    Continuous (fun J : Vertex P → Space => oldAnchor P J a) := by
  change Continuous (fun J : Vertex P → Space => (1/2 : ℝ) • J (.x (P.faceX a.1)))
  exact (continuous_apply (Vertex.x (P.faceX a.1) : Vertex P)).const_smul (1/2 : ℝ)

theorem measurableSet_eligible (P : TannerSquarePresentation) (s : Finset (Triangle P))
    (r : ℝ) : MeasurableSet {J : Vertex P → Space | Eligible P J r s} := by
  have hd (a b : Triangle P) : MeasurableSet
      {J : Vertex P → Space | dist (oldAnchor P J a) (oldAnchor P J b) ≤ r} :=
    (isClosed_le ((continuous_oldAnchor P a).dist (continuous_oldAnchor P b))
      continuous_const).measurableSet
  have hf : MeasurableSet {J : Vertex P → Space |
      ∀ a ∈ s, ∀ b ∈ s, dist (oldAnchor P J a) (oldAnchor P J b) ≤ r} := by
    have he : {J : Vertex P → Space |
        ∀ a ∈ s, ∀ b ∈ s, dist (oldAnchor P J a) (oldAnchor P J b) ≤ r} =
        ⋂ a : Triangle P, ⋂ (_ : a ∈ s), ⋂ b : Triangle P, ⋂ (_ : b ∈ s),
          {J | dist (oldAnchor P J a) (oldAnchor P J b) ≤ r} := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [he]
    exact MeasurableSet.iInter fun a : Triangle P => MeasurableSet.iInter fun _ : a ∈ s =>
      MeasurableSet.iInter fun b : Triangle P => MeasurableSet.iInter fun _ : b ∈ s => hd a b
  by_cases h : s.card = 4 ∧ ∀ a ∈ s, ∀ b ∈ s, triangleColor P a = triangleColor P b
  · convert hf using 1
    ext J
    constructor
    · exact fun hj => hj.2.2
    · exact fun hj => ⟨h.1,h.2,hj⟩
  · have he : {J : Vertex P → Space | Eligible P J r s} = ∅ := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun he => h ⟨he.1,he.2.1⟩
    rw [he]
    exact MeasurableSet.empty

theorem measurableSet_masterBad (P : TannerSquarePresentation) (r lambda : ℝ) (K : ℕ)
    (e : MasterEvent P) : MeasurableSet
      {z : (Vertex P → Space) × (masterSupport P e → Space) |
        z.2 ∈ masterBad P r lambda K z.1 e} := by
  have hg (g : Grid K) (a : e.val) : MeasurableSet
      {z : (Vertex P → Space) × (masterSupport P e → Space) |
        (fun i => z.2 (masterVertex P e a i)) ∈
          triangleHit (fun i => lambda • ((1/2 : ℝ) • z.1 (triangleVertex P a.val i)))
            (masterCenter P z.1 lambda K e g) 2} := by
    apply measurableSet_triangleHit_of_measurable
    · apply measurable_pi_lambda
      intro i
      have hcoord : Measurable (fun z : (Vertex P → Space) × (masterSupport P e → Space) =>
          z.1 (triangleVertex P a.val i)) := (measurable_pi_apply _).comp measurable_fst
      exact (hcoord.const_smul (1/2 : ℝ)).const_smul lambda
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd
    · exact (((continuous_oldAnchor P (masterAnchor P e)).const_smul lambda).add_const
        (gridPoint K g)).measurable.comp measurable_fst
    · exact measurable_const
  have he : {z : (Vertex P → Space) × (masterSupport P e → Space) |
      z.2 ∈ masterBad P r lambda K z.1 e} =
      {z | Eligible P z.1 r e.val} ∩
        ⋃ g : Grid K, ⋂ a : e.val,
          {z | (fun i => z.2 (masterVertex P e a i)) ∈
            triangleHit (fun i => lambda • ((1/2 : ℝ) • z.1 (triangleVertex P a.val i)))
              (masterCenter P z.1 lambda K e g) 2} := by
    ext z
    simp only [masterBad, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]
  rw [he]
  exact ((measurableSet_eligible P e.val r).preimage measurable_fst).inter
    (MeasurableSet.iUnion fun g : Grid K => MeasurableSet.iInter fun a : e.val => hg g a)

theorem masterBad_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r)
    (u : eventSupport P J r e → Space) :
    u ∈ masterBad P r lambda K J (eventToMaster P J r e) ↔
      u ∈ eventBad P J r lambda K e := by
  change (Eligible P J r e.val ∧ ∃ g : Grid K, ∀ a : e.val,
    (fun i => u (eventVertex P J r e a i)) ∈
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (eventCenter P J r lambda K e g) 2) ↔ u ∈ eventBad P J r lambda K e
  simp only [e.property, true_and, eventBad, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage]

theorem master_selected_scan (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (u : Vertex P → Space) :
    (select (localEvent (eventSupport P J r) (eventBad P J r lambda K)) u).map
        (eventToMaster P J r) =
      select (localEvent (masterSupport P) (masterBad P r lambda K J)) u := by
  apply select_map_of_enabled
  · exact eventToMaster_scan_priority P J r
  · intro e u
    exact masterBad_original P J r lambda K e _
  · intro e u hu
    have he : Eligible P J r e.val := hu.1
    exact ⟨⟨e.val,he⟩,Subtype.ext rfl⟩

theorem master_step_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space))
    (c : Counters (Vertex P)) :
    step (masterSupport P) (masterBad P r lambda K J) T c =
      step (eventSupport P J r) (eventBad P J r lambda K) T c := by
  have he := master_selected_scan P J r lambda K (assignment T c)
  cases ho : select (localEvent (eventSupport P J r) (eventBad P J r lambda K))
      (assignment T c) with
  | none =>
      simp only [ho, Option.map_none] at he
      simp only [step, select_decidable_eq, ho, ← he]
  | some e =>
      simp only [ho, Option.map_some] at he
      simp only [step, select_decidable_eq, ho, ← he]
      have hs : masterSupport P (eventToMaster P J r e) = eventSupport P J r e := by
        ext v
        simp only [masterSupport, eventSupport, eventToMaster, Finset.mem_biUnion]
      funext v
      by_cases hv : v ∈ eventSupport P J r e <;> simp only [advance, hs, hv, if_true, if_false]

theorem master_counters_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    counters (masterSupport P) (masterBad P r lambda K J) T n =
      counters (eventSupport P J r) (eventBad P J r lambda K) T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [counters, counters, ih]
      exact master_step_original P J r lambda K T _

theorem master_selected_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    (selected (eventSupport P J r) (eventBad P J r lambda K) T n).map
        (eventToMaster P J r) =
      selected (masterSupport P) (masterBad P r lambda K J) T n := by
  unfold selected
  rw [master_counters_original]
  simpa only [select_decidable_eq] using master_selected_scan P J r lambda K
    (assignment T (counters (eventSupport P J r) (eventBad P J r lambda K) T n))

theorem master_halts_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) :
    Halts (masterSupport P) (masterBad P r lambda K J) T ↔
      Halts (eventSupport P J r) (eventBad P J r lambda K) T := by
  simp only [Halts, ← master_selected_original, Option.map_eq_none_iff]

theorem master_haltTime_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) :
    haltTime (masterSupport P) (masterBad P r lambda K J) T =
      haltTime (eventSupport P J r) (eventBad P J r lambda K) T := by
  by_cases h : Halts (eventSupport P J r) (eventBad P J r lambda K) T
  · have hm := (master_halts_original P J r lambda K T).mpr h
    simp only [haltTime, dif_pos h, dif_pos hm]
    exact Nat.find_congr' (by
      intro n
      rw [← master_selected_original, Option.map_eq_none_iff])
  · have hm : ¬ Halts (masterSupport P) (masterBad P r lambda K J) T :=
      fun hh => h ((master_halts_original P J r lambda K T).mp hh)
    simp only [haltTime, dif_neg h, dif_neg hm]

theorem master_output_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (T : Table (X := fun _ : Vertex P => Space)) :
    output (masterSupport P) (masterBad P r lambda K J) T =
      output (eventSupport P J r) (eventBad P J r lambda K) T := by
  unfold output
  rw [master_haltTime_original, master_counters_original]

theorem measurable_joint_counters (P : TannerSquarePresentation) (r lambda : ℝ)
    (K n : ℕ) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        counters (eventSupport P z.1 r) (eventBad P z.1 r lambda K) z.2 n) := by
  simpa only [master_counters_original] using
    measurable_parameterized_counters (A := Vertex P → Space) (X := fun _ : Vertex P => Space)
      (masterSupport P) (masterBad P r lambda K)
      (measurableSet_masterBad P r lambda K) n

theorem measurable_joint_selected (P : TannerSquarePresentation) (r lambda : ℝ)
    (K n : ℕ) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        (selected (eventSupport P z.1 r) (eventBad P z.1 r lambda K) z.2 n).map
          (eventToMaster P z.1 r)) := by
  simpa only [master_selected_original] using
    measurable_parameterized_selected (A := Vertex P → Space) (X := fun _ : Vertex P => Space)
      (masterSupport P) (masterBad P r lambda K)
      (measurableSet_masterBad P r lambda K) n

theorem measurableSet_joint_halts (P : TannerSquarePresentation) (r lambda : ℝ)
    (K : ℕ) : MeasurableSet
      {z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) |
        Halts (eventSupport P z.1 r) (eventBad P z.1 r lambda K) z.2} := by
  simpa only [master_halts_original] using
    measurableSet_parameterized_halts (A := Vertex P → Space) (X := fun _ : Vertex P => Space)
      (masterSupport P) (masterBad P r lambda K)
      (measurableSet_masterBad P r lambda K)

theorem measurable_joint_haltTime (P : TannerSquarePresentation) (r lambda : ℝ)
    (K : ℕ) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        haltTime (eventSupport P z.1 r) (eventBad P z.1 r lambda K) z.2) := by
  simpa only [master_haltTime_original] using
    measurable_parameterized_haltTime (A := Vertex P → Space) (X := fun _ : Vertex P => Space)
      (masterSupport P) (masterBad P r lambda K)
      (measurableSet_masterBad P r lambda K)

theorem measurable_joint_geometricOutput (P : TannerSquarePresentation)
    {L : ℝ} (p : GeometricParameters L) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        geometricOutput P z.1 p z.2) := by
  have hm := measurable_parameterized_output
      (A := Vertex P → Space) (X := fun _ : Vertex P => Space)
      (masterSupport P)
      (masterBad P (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
      (measurableSet_masterBad P _ _ _)
  convert hm using 1
  funext z
  calc
    geometricOutput P z.1 p z.2 =
        output (eventSupport P z.1 (anchorRadius p.m))
          (eventBad P z.1 (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) z.2 := by
      unfold geometricOutput
      congr 1 <;> exact Subsingleton.elim _ _
    _ = output (masterSupport P)
        (masterBad P (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) z.1) z.2 :=
      (master_output_original P z.1 _ _ _ z.2).symm

end QEC.Coding.BDL26RandomPerturbation
