import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperiment

/-!
# One finite Borel success event for all actual experimentPrefix geometries

BDL26 v1 `paper.tex:1326–1340,1400–1428,2120–2198,2227–2238,2252–2256`,
approved source gate #841. The continuum of full-H frequency and rate statements
is a deterministic consequence on the same finite Halts-and-Good event. No
uncountable intersection and no operational expected-cost claim is introduced.
-/

noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem outputLaw_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ J ∂outputLaw p n, IsBoundedDensityLocalMap (StagePresentation p n) J p.t := by
  induction n with
  | zero =>
      apply (ae_map_iff (measurable_evaluate p 0).aemeasurable
        (measurableSet_boundedDensityLocalMap (StagePresentation p 0) p.t)).mpr
      exact Filter.Eventually.of_forall (fun _ => BDL26RandomSeedEmbedding.seed_parameter_localMap p)
  | succ n ih =>
      rw [outputLaw_succ]
      exact successorLaw_good_ae p n (outputLaw p n) ih

/-- Pull the actual incoming-law/fresh-table theorem back through the exact stage-pair law. -/
theorem stageFacts_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    ∀ᵐ z ∂experimentLaw p n,
      PhysicalSuccessorFacts p i.val (stageInput p n i z) (tableAt p n i z) := by
  have h := physical_successor_random_input_ae p i.val (outputLaw p i.val)
    (outputLaw_good_ae p i.val)
  rw [← stagePair_law p n i] at h
  exact ae_of_ae_map (measurable_stagePair p n i).aemeasurable h

theorem history_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin (n+1)) :
    ∀ᵐ z ∂experimentLaw p n,
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t := by
  have h := outputLaw_good_ae p i.val
  rw [← prefix_output_law p (show i.val ≤ n by omega)] at h
  exact ae_of_ae_map ((measurable_evaluate p i.val).comp
    (measurable_prefix p (show i.val ≤ n by omega))).aemeasurable h

/-- Only finitely many Borel halting and actual good-map assertions define success. -/
def finiteSuccess {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Set (Experiment p n) :=
  {z | IsBoundedDensityLocalMap (StagePresentation p 0)
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) p.t ∧
    (∀ i : Fin n, stageHalts p n i z) ∧
    ∀ i : Fin (n+1), IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t}

theorem measurableSet_finiteSuccess {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    MeasurableSet (finiteSuccess p n) := by
  have hseed : MeasurableSet {z : Experiment p n |
      IsBoundedDensityLocalMap (StagePresentation p 0)
        (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) p.t} := by
    simpa only [BDL26RandomSeedEmbedding.seed_parameter_localMap, Set.setOf_true]
      using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Experiment p n)))
  have hhalts : MeasurableSet {z : Experiment p n | ∀ i : Fin n, stageHalts p n i z} := by
    have heq : {z : Experiment p n | ∀ i : Fin n, stageHalts p n i z} =
        ⋂ i : Fin n, {z | stageHalts p n i z} := by ext z; simp
    rw [heq]
    exact MeasurableSet.iInter (fun i => measurableSet_stageHalts p n i)
  have hgood : MeasurableSet {z : Experiment p n | ∀ i : Fin (n+1),
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t} := by
    have heq : {z : Experiment p n | ∀ i : Fin (n+1),
        IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t} =
        ⋂ i : Fin (n+1), {z | IsBoundedDensityLocalMap (StagePresentation p i.val)
          (history p n z i) p.t} := by ext z; simp
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_boundedDensityLocalMap (StagePresentation p i.val) p.t).preimage
      ((measurable_pi_apply i).comp (measurable_history p n))
  exact hseed.inter (hhalts.inter hgood)

theorem finiteSuccess_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n := by
  have hhalts : ∀ᵐ z ∂experimentLaw p n, ∀ i : Fin n, stageHalts p n i z := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [stageFacts_ae p n i] with z hz
    exact hz.1
  have hgood : ∀ᵐ z ∂experimentLaw p n, ∀ i : Fin (n+1),
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t :=
    ae_all_iff.mpr (history_good_ae p n)
  filter_upwards [hhalts, hgood] with z hh hg
  exact ⟨BDL26RandomSeedEmbedding.seed_parameter_localMap p, hh, hg⟩

theorem finiteSuccess_measure {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    experimentLaw p n (finiteSuccess p n) = 1 := by
  calc
    experimentLaw p n (finiteSuccess p n) = experimentLaw p n Set.univ := by
      apply measure_congr
      filter_upwards [finiteSuccess_ae p n] with z hz
      exact propext (iff_true_intro hz)
    _ = 1 := measure_univ

theorem finiteSuccess_stageFacts {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin n) :
    PhysicalSuccessorFacts p i.val (stageInput p n i z) (tableAt p n i z) := by
  apply physicalSuccessorFacts_of_halts_localMap p i.val
  · exact hz.2.1 i
  · have hg := hz.2.2 ⟨i.val+1, by omega⟩
    rw [history_stage] at hg
    exact hg

theorem finiteSuccess_geometry {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1)) :
    PhysicalGeometry (perturbationOddScale p) i.val (history p n z i) p.t :=
  physicalGeometry_of_localMap _ _ _ (hz.2.2 i)

/-- Every actual full-H real frequency uses the very same metric region on this event. -/
theorem finiteSuccess_frequency_physical {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1))
    (q : Physical (perturbationOddScale p) i.val) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian (perturbationOddScale p) i.val)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) i.val)
        (BDL26CSSDaviesLocality.coupling (perturbationOddScale p) i.val q a) ω) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      ∀ s ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).selected.card ≤ 50 :=
  frequency_physical _ _ _ (hz.2.2 i) q a ω

theorem finiteSuccess_weightedJump_physical {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1))
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) i.val →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) i.val → ℝ)
    (q : Physical (perturbationOddScale p) i.val) (a : CSSDaviesLocality.Axis)
    (ω : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) i.val) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian (perturbationOddScale p) i.val)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) i.val)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) i.val =>
          BDL26CSSDaviesLocality.coupling (perturbationOddScale p) i.val qa.1 qa.2)
        rate ((q,a),ω)) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      ∀ s ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).selected.card ≤ 50 :=
  weightedJump_physical _ _ _ (hz.2.2 i) rate q a ω

@[simp] theorem history_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) : history p n z (Fin.last n) = evaluate p n z := by
  simp only [history, Fin.val_last, prefix_self]

/-- Source-even levels include zero and keep the same parameters before `k`. -/
theorem source_even_geometry_ae {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    ∀ᵐ z ∂experimentLaw p (2*k), z ∈ finiteSuccess p (2*k) ∧
      PhysicalGeometry (perturbationOddScale p) (2*k) (evaluate p (2*k) z) p.t := by
  filter_upwards [finiteSuccess_ae p (2*k)] with z hz
  refine ⟨hz, ?_⟩
  simpa only [Fin.val_last, history_last] using
    finiteSuccess_geometry p (2*k) hz (Fin.last (2*k))

theorem zero_experiment_seed {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) ∧
    PhysicalGeometry (perturbationOddScale p) 0 (evaluate p 0 z) p.t :=
  ⟨rfl, BDL26RandomSeedEmbedding.seed_physicalGeometry p⟩

/-- One parameter witness works for every finite experiment; its spaces may vary with `n`. -/
theorem exists_fixed_parameters_all_finite (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ n : ℕ,
      MeasurableSet (finiteSuccess p n) ∧
      ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧
        ∀ i : Fin (n+1), PhysicalGeometry (perturbationOddScale p) i.val (history p n z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, fun n => ⟨measurableSet_finiteSuccess p n, ?_⟩⟩
  filter_upwards [finiteSuccess_ae p n] with z hz
  exact ⟨hz, finiteSuccess_geometry p n hz⟩

end QEC.Coding.BDL26FiniteEmbeddingExperiment
