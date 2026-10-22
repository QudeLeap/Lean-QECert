import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountableExperiment
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperimentGeometry

/-!
# One Borel common success event for every actual finite embedding

This derived coupling uses the original finite laws and the approved BDL26
continuous model. Frequencies and rates are quantified deterministically after
membership in the same countable Halts-and-Good event.
-/

noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

/-- A single countable event; no frequency or rate appears in its definition. -/
def allFiniteSuccess {L : ℝ} (p : GeometricParameters L) : Set (Omega p) :=
  {omega | ∀ n, truncate p n omega ∈ finiteSuccess p n}

theorem allFiniteSuccess_eq_iInter {L : ℝ} (p : GeometricParameters L) :
    allFiniteSuccess p = ⋂ n, truncate p n ⁻¹' finiteSuccess p n := by
  ext omega
  simp only [allFiniteSuccess, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]

theorem measurableSet_allFiniteSuccess {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet (allFiniteSuccess p) := by
  rw [allFiniteSuccess_eq_iInter]
  exact MeasurableSet.iInter (fun n =>
    (measurableSet_finiteSuccess p n).preimage (measurable_truncate p n))

theorem allFiniteSuccess_ae {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p := by
  apply ae_all_iff.mpr
  intro n
  have h := finiteSuccess_ae p n
  rw [← truncate_law p n] at h
  exact ae_of_ae_map (measurable_truncate p n).aemeasurable h

theorem allFiniteSuccess_measure {L : ℝ} (p : GeometricParameters L) :
    streamLaw p (allFiniteSuccess p) = 1 := by
  calc
    streamLaw p (allFiniteSuccess p) = streamLaw p Set.univ := by
      apply measure_congr
      filter_upwards [allFiniteSuccess_ae p] with omega h
      exact propext (iff_true_intro h)
    _ = 1 := measure_univ

theorem allFiniteSuccess_halts {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ) :
    streamHalts p n omega := (h (n+1)).2.1 (Fin.last n)

theorem allFiniteSuccess_localMap {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ) :
    IsBoundedDensityLocalMap (StagePresentation p n) (levelMap p omega n) p.t := by
  have hg := (h n).2.2 (Fin.last n)
  simpa only [history_truncate, Fin.val_last] using hg

theorem allFiniteSuccess_stageFacts {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ) :
    PhysicalSuccessorFacts p n (levelMap p omega n) (omega n) := by
  have hf := finiteSuccess_stageFacts p (n+1) (h (n+1)) (Fin.last n)
  simpa only [stageInput_truncate, tableAt_truncate, Fin.val_last] using hf

theorem allFiniteSuccess_geometry {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ) :
    PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t :=
  physicalGeometry_of_localMap _ _ _ (allFiniteSuccess_localMap p h n)

/-- Domain-label counting survives arbitrary collapsed images and duplicate checks. -/
theorem allFiniteSuccess_density {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ) (c : Space) :
    ((qubitHits (StagePresentation p n) (levelMap p omega n)
      (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t :=
  (allFiniteSuccess_geometry p h n).1 c

theorem allFiniteSuccess_checks {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ)
    (j : Sum (ZLabel (perturbationOddScale p) n) (XLabel (perturbationOddScale p) n)) :
    (∀ r ∈ checkSupport (perturbationOddScale p) n j,
      dist (levelMap p omega n (.q r))
        (checkCenter (perturbationOddScale p) n (levelMap p omega n) j) ≤ 1) ∧
    (∀ r ∈ checkSupport (perturbationOddScale p) n j,
      ∀ s ∈ checkSupport (perturbationOddScale p) n j,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 2) ∧
    (checkSupport (perturbationOddScale p) n j).card ≤ 7 :=
  (allFiniteSuccess_geometry p h n).2.1 j

theorem allFiniteSuccess_frequency_physical {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ)
    (q : Physical (perturbationOddScale p) n) (a : CSSDaviesLocality.Axis) (w : ℝ) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.coupling (perturbationOddScale p) n q a) w) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      ∀ s ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).selected.card ≤ 50 :=
  frequency_physical _ _ _ (allFiniteSuccess_localMap p h n) q a w

theorem allFiniteSuccess_weightedJump_physical {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ)
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) n →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) n → ℝ)
    (q : Physical (perturbationOddScale p) n) (a : CSSDaviesLocality.Axis)
    (w : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) n) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) n)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) n =>
          BDL26CSSDaviesLocality.coupling (perturbationOddScale p) n qa.1 qa.2)
        rate ((q,a),w)) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      ∀ s ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).selected.card ≤ 50 :=
  weightedJump_physical _ _ _ (allFiniteSuccess_localMap p h n) rate q a w

/-- This includes `k=0` on the same event, rather than different per-depth events. -/
theorem allFiniteSuccess_source_even {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (k : ℕ) :
    PhysicalGeometry (perturbationOddScale p) (2*k) (levelMap p omega (2*k)) p.t :=
  allFiniteSuccess_geometry p h (2*k)

theorem common_geometry_ae {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
      (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t := by
  filter_upwards [allFiniteSuccess_ae p] with omega h
  exact ⟨h, allFiniteSuccess_stageFacts p h, allFiniteSuccess_geometry p h⟩

theorem seed_sharp {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    Fintype.card (Physical (perturbationOddScale p) 0) = 5 ∧
    (∀ q : Physical (perturbationOddScale p) 0, levelMap p omega 0 (.q q) = 0) ∧
    (∀ r s : Physical (perturbationOddScale p) 0,
      dist (levelMap p omega 0 (.q r)) (levelMap p omega 0 (.q s)) = 0) ∧
    ∀ c, ((qubitHits (StagePresentation p 0) (levelMap p omega 0)
      (Metric.closedBall c 1)).card : ℝ) ≤ 5 :=
  ⟨BDL26RandomSeedEmbedding.seed_physical_card _, fun _ => rfl,
    BDL26RandomSeedEmbedding.seed_physical_distance_zero _,
    BDL26RandomSeedEmbedding.seed_qubit_density _⟩

theorem exists_successful_stream {L : ℝ} (p : GeometricParameters L) :
    ∃ omega : Omega p, omega ∈ allFiniteSuccess p :=
  (allFiniteSuccess_ae p).exists

/-- The parameter, actual common law, and event precede every level and every frequency. -/
theorem exists_fixed_parameters_common_stream (L : ℝ) :
    ∃ p : GeometricParameters L,
      MeasurableSet (allFiniteSuccess p) ∧ streamLaw p (allFiniteSuccess p) = 1 ∧
      (∀ᵐ omega ∂streamLaw p, omega ∈ allFiniteSuccess p ∧
        (∀ n, PhysicalSuccessorFacts p n (levelMap p omega n) (omega n)) ∧
        ∀ n, PhysicalGeometry (perturbationOddScale p) n (levelMap p omega n) p.t) ∧
      ∃ omega : Omega p, omega ∈ allFiniteSuccess p := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, measurableSet_allFiniteSuccess p, allFiniteSuccess_measure p, ?_,
    exists_successful_stream p⟩
  exact common_geometry_ae p

end QEC.Coding.BDL26CountableEmbeddingExperiment
