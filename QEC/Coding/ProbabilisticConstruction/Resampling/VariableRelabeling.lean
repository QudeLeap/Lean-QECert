import QEC.Coding.ProbabilisticConstruction.Resampling.Termination
import QEC.Coding.ProbabilisticConstruction.Resampling.TableProbability

/-!
# Variable relabeling of the original ordered table process

Only variable labels change. Event labels/order, Nat clocks and table columns
are literally retained. Homogeneous sampling values avoid dependent value casts.
Full observation laws include nonhalting default0/initial output and infinity.
This is a project-derived internal API, not an original-rank/setup cost theorem.
-/
noncomputable section
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

abbrev HTable (V X : Type*) := Table (X := fun _ : V => X)

variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]

/-- The support is pulled back by the actual equivalence, not assumed equal. -/
def codedSupport (u : A ≃ V) (U : I → Finset V) (i : I) : Finset A :=
  (U i).image u.symm

@[simp] theorem mem_codedSupport (u : A ≃ V) (U : I → Finset V) (i : I) (a : A) :
    a∈codedSupport u U i ↔ u a∈U i := by
  constructor
  · rintro ha
    obtain ⟨v,hv,hva⟩ := Finset.mem_image.mp ha
    simpa only [← hva,u.apply_symm_apply] using hv
  · intro ha
    exact Finset.mem_image.mpr ⟨u a,ha,u.symm_apply_apply a⟩

/-- The actual support subtype equivalence is constructed from membership. -/
def supportEquiv (u : A ≃ V) (U : I → Finset V) (i : I) :
    codedSupport u U i ≃ U i where
  toFun a := ⟨u a.val,(mem_codedSupport u U i a.val).mp a.property⟩
  invFun v := ⟨u.symm v.val,(mem_codedSupport u U i _).mpr (by simpa using v.property)⟩
  left_inv a := Subtype.ext (u.symm_apply_apply a.val)
  right_inv v := Subtype.ext (u.apply_symm_apply v.val)

def encodeAssignment (u : A ≃ V) (z : V → X) : A → X := fun a => z (u a)
def decodeAssignment (u : A ≃ V) (z : A → X) : V → X := fun v => z (u.symm v)
def encodeTable (u : A ≃ V) (T : HTable V X) : HTable A X :=
  fun p => T (u p.1,p.2)
def decodeTable (u : A ≃ V) (T : HTable A X) : HTable V X := encodeTable u.symm T

def decodeLocal (u : A ≃ V) (U : I → Finset V) (i : I)
    (z : codedSupport u U i → X) : U i → X := fun v => z ((supportEquiv u U i).symm v)

def codedBad (u : A ≃ V) (U : I → Finset V)
    (B : ∀ i, Set (U i → X)) (i : I) : Set (codedSupport u U i → X) :=
  decodeLocal u U i ⁻¹' B i

@[simp] theorem decode_encode_assignment (u : A ≃ V) (z : V → X) :
    decodeAssignment u (encodeAssignment u z)=z := by funext v; simp [decodeAssignment,encodeAssignment]
@[simp] theorem encode_decode_assignment (u : A ≃ V) (z : A → X) :
    encodeAssignment u (decodeAssignment u z)=z := by funext a; simp [decodeAssignment,encodeAssignment]
@[simp] theorem decode_encode_table (u : A ≃ V) (T : HTable V X) :
    decodeTable u (encodeTable u T)=T := by
  funext p
  rcases p with ⟨v,n⟩
  exact congrArg (fun z : V => T (z,n)) (u.apply_symm_apply v)
@[simp] theorem encode_decode_table (u : A ≃ V) (T : HTable A X) :
    encodeTable u (decodeTable u T)=T := by
  funext p
  rcases p with ⟨a,n⟩
  exact congrArg (fun z : A => T (z,n)) (u.symm_apply_apply a)

theorem restriction_decode (u : A ≃ V) (U : I → Finset V) (i : I) (z : A → X) :
    decodeLocal u U i ((codedSupport u U i).restrict z)=
      (U i).restrict (decodeAssignment u z) := by funext v; rfl

theorem localEvent_decode (u : A ≃ V) (U : I → Finset V)
    (B : ∀ i, Set (U i → X)) (i : I) (z : A → X) :
    z∈localEvent (codedSupport u U) (codedBad u U B) i ↔
      decodeAssignment u z∈localEvent U B i := by
  change decodeLocal u U i ((codedSupport u U i).restrict z)∈B i ↔ _
  rw [restriction_decode]
  rfl

variable (u : A ≃ V) (U : I → Finset V) (B : ∀ i, Set (U i → X))
variable [∀ i, DecidablePred (·∈B i)]

/-- Every original list, including empty/repeated/non-sorted lists, is retained. -/
theorem firstBadFrom_conjugacy (L : List I) (z : A → X) :
    firstBadFrom (localEvent (codedSupport u U) (codedBad u U B)) L z=
      firstBadFrom (localEvent U B) L (decodeAssignment u z) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      by_cases hi : decodeAssignment u z∈localEvent U B i
      · have hc := (localEvent_decode u U B i z).mpr hi
        simp only [firstBadFrom,if_pos hi,if_pos hc]
      · have hc : z∉localEvent (codedSupport u U) (codedBad u U B) i :=
          fun h => hi ((localEvent_decode u U B i z).mp h)
        simp only [firstBadFrom,if_neg hi,if_neg hc,ih]

theorem select_conjugacy (z : A → X) :
    select (localEvent (codedSupport u U) (codedBad u U B)) z=
      select (localEvent U B) (decodeAssignment u z) :=
  firstBadFrom_conjugacy u U B _ z

/-- Decision dictionaries do not change a fixed original ordered scan. -/
private theorem select_decision_eq {Ω J : Type*} [Fintype J] [LinearOrder J]
    (E : J → Set Ω) (d e : ∀ i, DecidablePred (·∈E i)) (z : Ω) :
    @select Ω J E d inferInstance inferInstance z=
      @select Ω J E e inferInstance inferInstance z :=
  congrArg (fun f : ∀ i, DecidablePred (·∈E i) =>
    @select Ω J E f inferInstance inferInstance z) (Subsingleton.elim d e)

theorem assignment_conjugacy (T : HTable V X) (c : Counters V) :
    assignment (encodeTable u T) (encodeAssignment u c)=encodeAssignment u (assignment T c) := rfl

theorem advance_conjugacy (i : I) (c : Counters V) :
    advance (codedSupport u U) i (encodeAssignment u c)=encodeAssignment u (advance U i c) := by
  funext a
  simp only [advance,encodeAssignment,mem_codedSupport]

theorem step_conjugacy (T : HTable V X) (c : Counters V) :
    step (codedSupport u U) (codedBad u U B) (encodeTable u T) (encodeAssignment u c)=
      encodeAssignment u (step U B T c) := by
  let ea : I → Set (A → X) :=
    localEvent (X := fun _ : A => X) (codedSupport u U) (codedBad (X := X) u U B)
  let ev : I → Set (V → X) := localEvent (X := fun _ : V => X) U B
  have hsel : select (ea)
      (assignment (encodeTable u T) (encodeAssignment u c))=
      select (ev) (assignment T c) :=
    (congrArg (fun z : A → X =>
      select (ea) z)
      (assignment_conjugacy u T c)).trans
      ((select_conjugacy (X := X) u U B (encodeAssignment u (assignment T c))).trans
        (congrArg (fun z : V → X => select (ev) z)
          (decode_encode_assignment u (assignment T c))))
  let da := decidableLocalEvents (X := fun _ : A => X)
    (codedSupport u U) (codedBad (X := X) u U B)
  let dv := decidableLocalEvents (X := fun _ : V => X) U B
  let ca : (i : I) → (z : A → X) → Decidable (z∈ea i) :=
    fun (i : I) (z : A → X) => Classical.propDecidable (z∈ea i)
  let cv : (i : I) → (z : V → X) → Decidable (z∈ev i) :=
    fun (i : I) (z : V → X) => Classical.propDecidable (z∈ev i)
  have hactual : @select (A → X) I
      (ea) da inferInstance inferInstance
      (assignment (encodeTable u T) (encodeAssignment u c))=
      @select (V → X) I (ev) dv inferInstance inferInstance (assignment T c) :=
    (select_decision_eq _ da ca _).trans (hsel.trans (select_decision_eq _ cv dv _))
  change (match @select (A → X) I
      (ea) da inferInstance inferInstance
      (assignment (encodeTable u T) (encodeAssignment u c)) with
      | none => encodeAssignment u c
      | some i => advance (codedSupport u U) i (encodeAssignment u c))=
    encodeAssignment u (match @select (V → X) I (ev) dv
      inferInstance inferInstance (assignment T c) with
      | none => c | some i => advance U i c)
  rw [hactual]
  cases h : @select (V → X) I (ev) dv
      inferInstance inferInstance (assignment T c) with
  | none => rfl
  | some i => exact advance_conjugacy u U i c

/-- All times and every variable, including absorbing clean states. -/
theorem counters_conjugacy (T : HTable V X) (m : ℕ) :
    counters (codedSupport u U) (codedBad u U B) (encodeTable u T) m=
      encodeAssignment u (counters U B T m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [counters,counters,ih]; exact step_conjugacy u U B T _

theorem selected_conjugacy (T : HTable V X) (m : ℕ) :
    selected (codedSupport u U) (codedBad u U B) (encodeTable u T) m=selected U B T m := by
  let ea : I → Set (A → X) :=
    localEvent (X := fun _ : A => X) (codedSupport u U) (codedBad (X := X) u U B)
  let ev : I → Set (V → X) := localEvent (X := fun _ : V => X) U B
  unfold selected
  rw [counters_conjugacy,assignment_conjugacy]
  let da := decidableLocalEvents (X := fun _ : A => X)
    (codedSupport u U) (codedBad (X := X) u U B)
  let dv := decidableLocalEvents (X := fun _ : V => X) U B
  let ca : (i : I) → (z : A → X) → Decidable (z∈ea i) :=
    fun (i : I) (z : A → X) => Classical.propDecidable (z∈ea i)
  let cv : (i : I) → (z : V → X) → Decidable (z∈ev i) :=
    fun (i : I) (z : V → X) => Classical.propDecidable (z∈ev i)
  change @select (A → X) I (ea)
      da inferInstance inferInstance (encodeAssignment u (assignment T (counters U B T m)))=
    @select (V → X) I (ev) dv inferInstance inferInstance
      (assignment T (counters U B T m))
  exact (select_decision_eq _ da ca _).trans
    ((select_conjugacy (X := X) u U B
      (encodeAssignment u (assignment T (counters U B T m)))).trans
        ((congrArg (fun z : V → X =>
          @select (V → X) I (ev) cv inferInstance inferInstance z)
          (decode_encode_assignment u (assignment T (counters U B T m)))).trans
            (select_decision_eq _ cv dv _)))

theorem halts_conjugacy (T : HTable V X) :
    Halts (codedSupport u U) (codedBad u U B) (encodeTable u T) ↔ Halts U B T := by
  simp only [Halts,selected_conjugacy]

theorem haltTime_conjugacy (T : HTable V X) :
    haltTime (codedSupport u U) (codedBad u U B) (encodeTable u T)=haltTime U B T := by
  by_cases h : Halts U B T
  · have hc := (halts_conjugacy u U B T).mpr h
    simp only [haltTime,dif_pos h,dif_pos hc]
    exact Nat.find_congr' (by intro m; rw [selected_conjugacy])
  · have hc : ¬Halts (codedSupport u U) (codedBad u U B) (encodeTable u T) :=
      fun hh => h ((halts_conjugacy u U B T).mp hh)
    simp only [haltTime,dif_neg h,dif_neg hc]

theorem output_conjugacy (T : HTable V X) :
    output (codedSupport u U) (codedBad u U B) (encodeTable u T)=encodeAssignment u (output U B T) := by
  unfold output
  rw [haltTime_conjugacy,counters_conjugacy]
  exact assignment_conjugacy u T _

/-- Nonhalting returns the initial assignment at unchanged column0, not zero. -/
theorem nonhalting_output (T : HTable V X) (h : ¬Halts U B T) :
    output (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      fun a => T (u a,0) := by
  have hz : haltTime (X := fun _ : V => X) U B T=0 := by
    unfold haltTime
    exact dif_neg h
  rw [output_conjugacy]
  funext a
  change T (u a,counters U B T (haltTime U B T) (u a))=T (u a,0)
  exact congrArg (fun n : ℕ => T (u a,counters U B T n (u a))) hz

theorem prefixCount_conjugacy (T : HTable V X) (m : ℕ) (i : I) :
    prefixCount (codedSupport u U) (codedBad u U B) (encodeTable u T) m i=prefixCount U B T m i := by
  simp only [prefixCount,occurrences,selected_conjugacy]

theorem totalCount_conjugacy (T : HTable V X) (i : I) :
    totalCount (codedSupport u U) (codedBad u U B) (encodeTable u T) i=totalCount U B T i := by
  simp only [totalCount,prefixCount_conjugacy]

theorem totalSteps_conjugacy (T : HTable V X) :
    totalSteps (codedSupport u U) (codedBad u U B) (encodeTable u T)=totalSteps U B T := by
  simp only [totalSteps,totalCount_conjugacy]

theorem nonhalting_totalSteps (T : HTable V X) (h : ¬Halts U B T) :
    totalSteps U B T=∞ ∧
      totalSteps (codedSupport u U) (codedBad u U B) (encodeTable u T)=∞ := by
  have ht : totalSteps U B T=∞ := by
    by_contra hn
    have hf : totalSteps (X := fun _ : V => X) U B T < (∞ : ℝ≥0∞) :=
      lt_top_iff_ne_top.mpr hn
    have hh : Halts (X := fun _ : V => X) U B T :=
      @halts_of_totalSteps_lt_top I V inferInstance inferInstance inferInstance inferInstance
        (fun _ : V => X) (fun _ : V => (⊥ : MeasurableSpace X)) U B inferInstance T hf
    exact h hh
  exact ⟨ht,(totalSteps_conjugacy u U B T).trans ht⟩

/-- Identity/inverse/composition laws do not make new event/rank choices. -/
theorem encodeTable_refl (T : HTable V X) : encodeTable (Equiv.refl V) T=T := rfl

theorem encodeTable_trans (v : D ≃ A) (T : HTable V X) :
    encodeTable (v.trans u) T=encodeTable v (encodeTable u T) := rfl

theorem encodeAssignment_trans (v : D ≃ A) (z : V → X) :
    encodeAssignment (v.trans u) z=encodeAssignment v (encodeAssignment u z) := rfl

theorem counters_trans [Fintype D] [DecidableEq D] (v : D ≃ A) (T : HTable V X) (m : ℕ) :
    counters (codedSupport (v.trans u) U) (codedBad (v.trans u) U B)
      (encodeTable v (encodeTable u T)) m=
      encodeAssignment v (encodeAssignment u (counters U B T m)) :=
  counters_conjugacy (v.trans u) U B T m

theorem output_inverse (T : HTable A X) :
    decodeAssignment u (output (codedSupport u U) (codedBad u U B) T)=
      output U B (decodeTable u T) := by
  have h := congrArg (decodeAssignment u) (output_conjugacy u U B (decodeTable u T))
  simpa only [encode_decode_table,decode_encode_assignment] using h

section Measurable
variable [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]

theorem measurable_encodeAssignment : Measurable (encodeAssignment (X := X) u) :=
  measurable_pi_lambda _ (fun a => measurable_pi_apply (u a))
theorem measurable_decodeAssignment : Measurable (decodeAssignment (X := X) u) :=
  measurable_pi_lambda _ (fun v => measurable_pi_apply (u.symm v))
theorem measurable_encodeTable : Measurable (encodeTable (X := X) u) :=
  measurable_pi_lambda _ (fun p => measurable_pi_apply (u p.1,p.2))
theorem measurable_decodeTable : Measurable (decodeTable (X := X) u) :=
  measurable_encodeTable u.symm

theorem measurable_decodeLocal (i : I) : Measurable (decodeLocal (X := X) u U i) :=
  measurable_pi_lambda _ (fun v => measurable_pi_apply ((supportEquiv u U i).symm v))

theorem measurableSet_codedBad (hB : ∀ i, MeasurableSet (B i)) (i : I) :
    MeasurableSet (codedBad u U B i) := (hB i).preimage (measurable_decodeLocal u U i)

/-- The actual infinite table coordinate map is (a,k)↦(u(a),k). -/
theorem table_law (ν : V → Measure X) [∀ v, IsProbabilityMeasure (ν v)] :
    (tableLaw ν).map (encodeTable u)=tableLaw (fun a => ν (u a)) := by
  have hi : Function.Injective (fun p : A×ℕ => (u p.1,p.2)) := by
    intro a b h
    apply Prod.ext
    · exact u.injective (congrArg (fun p : V×ℕ => p.1) h)
    · exact congrArg (fun p : V×ℕ => p.2) h
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun p : V×ℕ => ν p.1) (f := fun p : A×ℕ => (u p.1,p.2)) hi

/-- One concrete full observation. Prefix counts are exact Nat values. -/
abbrev Observation (V I X : Type*) :=
  (ℕ → Counters V) × (ℕ → Option I) × Bool × ℕ × (V → X) ×
    (ℕ → I → ℕ) × (I → ℝ≥0∞) × ℝ≥0∞

def jointObservation (T : HTable V X) : Observation V I X :=
  (counters U B T,selected U B T,if Halts U B T then true else false,
    haltTime U B T,output U B T,prefixCount U B T,totalCount U B T,totalSteps U B T)

/-- Decode only variable fields; every event/clock/count is literally retained. -/
def decodedObservation (T : HTable A X) : Observation V I X :=
  ((fun m => decodeAssignment u (counters (codedSupport u U) (codedBad u U B) T m)),
    selected (codedSupport u U) (codedBad u U B) T,
    if Halts (codedSupport u U) (codedBad u U B) T then true else false,
    haltTime (codedSupport u U) (codedBad u U B) T,
    decodeAssignment u (output (codedSupport u U) (codedBad u U B) T),
    prefixCount (codedSupport u U) (codedBad u U B) T,
    totalCount (codedSupport u U) (codedBad u U B) T,
    totalSteps (codedSupport u U) (codedBad u U B) T)

theorem jointObservation_conjugacy (T : HTable V X) :
    decodedObservation u U B (encodeTable u T)=jointObservation U B T := by
  have hc : (fun m => decodeAssignment u
      (counters (codedSupport u U) (codedBad u U B) (encodeTable u T) m))=
      counters U B T := by
    funext m
    exact (congrArg (decodeAssignment u) (counters_conjugacy u U B T m)).trans
      (decode_encode_assignment u (counters U B T m))
  have hs : selected (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      selected U B T := funext (selected_conjugacy u U B T)
  have hh : (if Halts (codedSupport u U) (codedBad u U B) (encodeTable u T)
      then true else false)=(if Halts U B T then true else false) := by
    by_cases h : Halts U B T
    · have hcode := (halts_conjugacy u U B T).mpr h
      exact (if_pos hcode).trans (if_pos h).symm
    · have hcode : ¬Halts (codedSupport u U) (codedBad u U B) (encodeTable u T) :=
        fun hcode => h ((halts_conjugacy u U B T).mp hcode)
      exact (if_neg hcode).trans (if_neg h).symm
  have ho : decodeAssignment u
      (output (codedSupport u U) (codedBad u U B) (encodeTable u T))=output U B T :=
    (congrArg (decodeAssignment u) (output_conjugacy u U B T)).trans
      (decode_encode_assignment u (output U B T))
  have hp : prefixCount (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      prefixCount U B T := by
    funext m i
    exact prefixCount_conjugacy u U B T m i
  have ht : totalCount (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      totalCount U B T := funext (totalCount_conjugacy u U B T)
  exact Prod.ext hc (Prod.ext hs (Prod.ext hh (Prod.ext (haltTime_conjugacy u U B T)
    (Prod.ext ho (Prod.ext hp (Prod.ext ht (totalSteps_conjugacy u U B T)))))))

theorem decodedObservation_eq (T : HTable A X) :
    decodedObservation u U B T=jointObservation U B (decodeTable u T) := by
  have h := jointObservation_conjugacy u U B (decodeTable u T)
  simpa only [encode_decode_table] using h

theorem measurable_nat_prefixCount (hB : ∀ i, MeasurableSet (B i)) (m : ℕ) (i : I) :
    Measurable (fun T : HTable V X => prefixCount U B T m i) := by
  induction m with
  | zero => simpa only [prefixCount,occurrences,Finset.range_zero,Finset.filter_empty,Finset.card_empty]
      using (measurable_const : Measurable (fun _ : HTable V X => (0 : ℕ)))
  | succ m ih =>
      have hsel : Measurable (fun T : HTable V X => selected U B T m) :=
        measurable_selected (X := fun _ : V => X) U B hB m
      have he : MeasurableSet {T : HTable V X | selected U B T m=some i} :=
        hsel (measurableSet_singleton (some i))
      have hm : Measurable (fun T : HTable V X => if selected U B T m=some i then (1 : ℕ) else 0) :=
        Measurable.ite he measurable_const measurable_const
      have hsum := ih.add hm
      have hpoint : ((fun T : HTable V X => prefixCount U B T m i)+
          (fun T : HTable V X => if selected U B T m=some i then (1 : ℕ) else 0))=
          (fun T : HTable V X => prefixCount U B T m i+
            if selected U B T m=some i then (1 : ℕ) else 0) :=
        funext (fun T => Pi.add_apply _ _ T)
      rw [hpoint] at hsum
      simpa only [prefixCount_succ] using hsum

theorem measurable_jointObservation (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (jointObservation (X := X) U B) := by
  have hc : Measurable (fun T : HTable V X => counters U B T) :=
    measurable_pi_lambda _ (fun m => measurable_counters (X := fun _ : V => X) U B hB m)
  have hs : Measurable (fun T : HTable V X => selected U B T) :=
    measurable_pi_lambda _ (fun m => measurable_selected (X := fun _ : V => X) U B hB m)
  have hh : Measurable (fun T : HTable V X => if Halts U B T then true else false) :=
    Measurable.ite (measurableSet_halts (X := fun _ : V => X) U B hB) measurable_const measurable_const
  have hp : Measurable (fun T : HTable V X => prefixCount U B T) :=
    measurable_pi_lambda _ (fun m => measurable_pi_lambda _ (fun i => measurable_nat_prefixCount U B hB m i))
  have ht : Measurable (fun T : HTable V X => totalCount U B T) :=
    measurable_pi_lambda _ (fun i => measurable_totalCount (X := fun _ : V => X) U B hB i)
  exact hc.prodMk (hs.prodMk (hh.prodMk ((measurable_haltTime (X := fun _ : V => X) U B hB).prodMk
    ((measurable_output (X := fun _ : V => X) U B hB).prodMk (hp.prodMk (ht.prodMk (measurable_totalSteps (X := fun _ : V => X) U B hB)))))))

theorem measurable_decodedObservation (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (decodedObservation (X := X) u U B) := by
  have he : decodedObservation u U B=(jointObservation U B) ∘ decodeTable u :=
    funext (decodedObservation_eq u U B)
  rw [he]
  exact (measurable_jointObservation U B hB).comp (measurable_decodeTable u)

/-- Full joint law is DERIVED from coordinate reindexing, never a marginal assumption. -/
theorem jointObservation_law (hB : ∀ i, MeasurableSet (B i))
    (ν : V → Measure X) [∀ v, IsProbabilityMeasure (ν v)] :
    (tableLaw (fun a => ν (u a))).map (decodedObservation u U B)=
      (tableLaw ν).map (jointObservation U B) := by
  have h := congrArg (fun μ => μ.map (decodedObservation u U B)) (table_law u ν)
  rw [Measure.map_map (measurable_decodedObservation u U B hB) (measurable_encodeTable u)] at h
  have he : (decodedObservation u U B) ∘ encodeTable u=jointObservation U B :=
    funext (jointObservation_conjugacy u U B)
  rw [he] at h
  exact h.symm

end Measurable
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
