import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeHamiltonianLocality

/-!
# Actual Davies operators on the same finite native geometric histories

Project-derived internal/API #1641, child of #1422 and #855. Source route:
approved CLBT commuting-check locality (#843), actual labelled CSS application
(#1486), and BDL26 v1 finite native Hamiltonian geometry (#1639).
Every frequency and jump below uses the original full labelled Hamiltonian,
physical couplings and canonical incident-check subsystem. Local restrictions
are semantic postconditions, not additional execution output or paid spectral
matrix enumeration. No bath, protection, Peierls or storage claim is made.
-/

noncomputable section
namespace QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derive the region bound from check diameter and actual labelled incidence,
without using the region-geometry field of PhysicalGeometry. -/
private theorem incident_radius_of_checks (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (q r : Physical S n)
    (hr : r ∈ region S n q) : dist (J (.q r)) (J (.q q)) ≤ 2 := by
  rcases Finset.mem_union.mp hr with hr | hr
  · have he : r=q := Finset.mem_singleton.mp hr
    subst r
    simp
  · obtain ⟨j,hj,hr⟩ := Finset.mem_biUnion.mp hr
    have hq : q ∈ checkSupport S n j := (Finset.mem_filter.mp hj).2
    exact (hJ.2.1 j).2.1 r hr q hq

private theorem incident_diameter_of_checks (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (q r s : Physical S n)
    (hr : r ∈ region S n q) (hs : s ∈ region S n q) :
    dist (J (.q r)) (J (.q s)) ≤ 4 := by
  calc
    _ ≤ dist (J (.q r)) (J (.q q)) + dist (J (.q q)) (J (.q s)) := dist_triangle _ _ _
    _ ≤ 2+2 := add_le_add (incident_radius_of_checks S n J hJ q r hr)
      (by simpa only [dist_comm] using incident_radius_of_checks S n J hJ q s hs)
    _ = 4 := by norm_num

/-- Canonical restriction of the actual coherent full-H frequency at any real omega. -/
def localFrequency (S : OddScale) (n : ℕ) (q : Physical S n)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    Operator (subsystem S n q).selectedSystem :=
  (subsystem S n q).restrictLocalFromRegister
    (actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
      (coupling S n q a) ω)

/-- True identity extension of the canonical restriction on the unchanged region. -/
theorem extend_localFrequency (S : OddScale) (n : ℕ) (q : Physical S n)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (subsystem S n q).extendLocalToRegister (localFrequency S n q a ω) =
      actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
        (coupling S n q a) ω :=
  ((subsystem S n q).operatorSupportedOnRegister_iff_extend_restrict _).mp
    (frequency_supported S n q a ω)

/-- The actual sqrt-rate weighted jump, restricted on the same canonical subsystem. -/
def localJump (S : OddScale) (n : ℕ)
    (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    Operator (subsystem S n q).selectedSystem :=
  (subsystem S n q).restrictLocalFromRegister
    (hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
      (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω))

theorem extend_localJump (S : OddScale) (n : ℕ)
    (rate : CouplingIndex S n → Frequency S n → ℝ)
    (q : Physical S n) (a : CSSDaviesLocality.Axis) (ω : Frequency S n) :
    (subsystem S n q).extendLocalToRegister (localJump S n rate q a ω) =
      hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
        (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) :=
  ((subsystem S n q).operatorSupportedOnRegister_iff_extend_restrict _).mp
    (weightedJump_supported S n rate q a ω)

/-- Simultaneous actual full-H and native Hamiltonian geometry. The region
counts physical labels, even when their coordinates coincide. All original
check labels, including repeated and identity rows, remain in the Hamiltonian.
The predicate is proved from actual geometry below, never supplied to the
randomized result as a certificate. -/
def DaviesGeometry (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (t : ℝ) : Prop :=
  BDL26NativeHamiltonianLocality.HamiltonianGeometry S n J t ∧
  ∀ q : Physical S n,
    (region S n q).card ≤ 50 ∧
    (∀ r ∈ region S n q, dist (J (.q r)) (J (.q q)) ≤ 2) ∧
    (∀ r ∈ region S n q, ∀ s ∈ region S n q, dist (J (.q r)) (J (.q s)) ≤ 4) ∧
    (∀ (a : CSSDaviesLocality.Axis) (ω : ℝ),
      (subsystem S n q).OperatorSupportedOnRegister
        (actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω) ∧
      actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω =
        actualFrequency (incidentHamiltonian S n q) (incidentHamiltonian_symmetric S n q)
          (coupling S n q a) ω ∧
      (subsystem S n q).extendLocalToRegister (localFrequency S n q a ω) =
        actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω) ∧
    (∀ (rate : CouplingIndex S n → Frequency S n → ℝ)
      (a : CSSDaviesLocality.Axis) (ω : Frequency S n),
      (subsystem S n q).OperatorSupportedOnRegister
        (hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
          (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
      hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
          (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω) =
        (Real.sqrt (rate (q,a) ω) : ℂ) •
          actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
            (coupling S n q a) ω.val ∧
      (subsystem S n q).extendLocalToRegister (localJump S n rate q a ω) =
        hamiltonianJump (hamiltonian S n) (hamiltonian_symmetric S n)
          (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ a : CSSDaviesLocality.Axis,
      (∑ ω : Frequency S n,
        actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω.val) = coupling S n q a ∧
      ∃ ω : Frequency S n,
        actualFrequency (hamiltonian S n) (hamiltonian_symmetric S n)
          (coupling S n q a) ω.val ≠ 0)

/-- The check-diameter facts yield radius2/diameter4 on the actual incident region;
existing operator theorems yield full-H support and canonical local restriction.
No support/geometry conclusion is assumed for any individual frequency or jump. -/
theorem daviesGeometry_of_physical (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) : DaviesGeometry S n J t := by
  refine ⟨BDL26NativeHamiltonianLocality.hamiltonianGeometry_of_physical S n J hJ, ?_⟩
  intro q
  refine ⟨region_card_le_fifty S n q, incident_radius_of_checks S n J hJ q,
    (fun r hr s hs => incident_diameter_of_checks S n J hJ q r s hr hs), ?_, ?_, ?_⟩
  · intro a ω
    exact ⟨frequency_supported S n q a ω, frequency_eq_incident S n q a ω,
      extend_localFrequency S n q a ω⟩
  · intro rate a ω
    exact ⟨weightedJump_supported S n rate q a ω, jump_eq_sqrt_smul S n rate q a ω,
      extend_localJump S n rate q a ω⟩
  · intro a
    exact ⟨sum_actualFrequency S n q a, exists_nonzero_actualFrequency S n q a⟩

theorem finiteSuccess_davies {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : BDL26NativeFiniteComposition.Experiment p N}
    (hz : z ∈ BDL26NativeFiniteComposition.finiteSuccess p N) :
    ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t := by
  intro i
  exact daviesGeometry_of_physical _ _ _
    (BDL26NativeFiniteComposition.finiteSuccess_geometry p N hz i)

theorem finite_history_davies_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N, ∀ i : Fin (N+1),
      DaviesGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N] with z hz
  exact finiteSuccess_davies p N hz

/-- An enhanced postcondition event on the original native experiment space. -/
def finiteDaviesSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Set (BDL26NativeFiniteComposition.Experiment p N) :=
  {z | z ∈ BDL26NativeFiniteComposition.finiteSuccess p N ∧
    ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t}

theorem finiteDaviesSuccess_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    finiteDaviesSuccess p N = BDL26NativeFiniteComposition.finiteSuccess p N := by
  ext z
  constructor
  · exact fun hz => hz.1
  · exact fun hz => ⟨hz, finiteSuccess_davies p N hz⟩

theorem measurableSet_finiteDaviesSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    MeasurableSet (finiteDaviesSuccess p N) := by
  rw [finiteDaviesSuccess_eq]
  exact BDL26NativeFiniteComposition.measurableSet_finiteSuccess p N

theorem finiteDaviesSuccess_measure {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    BDL26NativeFiniteComposition.experimentLaw p N (finiteDaviesSuccess p N) = 1 := by
  rw [finiteDaviesSuccess_eq]
  exact BDL26NativeFiniteComposition.finiteSuccess_measure p N

theorem zero_seed_davies {L : ℝ} (p : GeometricParameters L)
    (z : BDL26NativeFiniteComposition.Experiment p 0) :
    BDL26NativeFiniteComposition.evaluate p 0 z =
      BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) ∧
    BDL26NativeFiniteComposition.totalCost p 0 z = 0 ∧
    DaviesGeometry (perturbationOddScale p) 0
      (BDL26NativeFiniteComposition.evaluate p 0 z) p.t := by
  obtain ⟨hs,hc,hg⟩ := BDL26NativeFiniteComposition.zero_experiment_seed p z
  exact ⟨hs,hc,daviesGeometry_of_physical _ _ _ hg⟩

/-- One legal parameter is chosen before all finite depths. The ORIGINAL total
coordinate cost is retained. This asserts no paid computation of spectral
matrices, local restrictions or subsystem certificates. -/
theorem fixed_parameters_all_finite (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) ≤
        (BDL26NativeFiniteComposition.totalCoefficient p*
          (BDL26FiniteEmbeddingExperiment.stageQubits p N+1)^1774 : ℕ) ∧
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) < ∞ ∧
      Integrable (fun z => (BDL26NativeFiniteComposition.totalCost p N z).toReal)
        (BDL26NativeFiniteComposition.experimentLaw p N) ∧
      BDL26NativeFiniteComposition.experimentLaw p N (finiteDaviesSuccess p N) = 1 ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N,
        z ∈ finiteDaviesSuccess p N ∧
        BDL26NativeFiniteComposition.totalCost p N z < ∞ ∧
        ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
          (BDL26NativeFiniteComposition.history p N z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, fun N => ⟨BDL26NativeFiniteComposition.totalCost_integral_le p N,
    (BDL26NativeFiniteComposition.totalCost_integrable p N).1,
    (BDL26NativeFiniteComposition.totalCost_integrable p N).2,
    finiteDaviesSuccess_measure p N, ?_⟩⟩
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N] with z hz
  have hd := finiteSuccess_davies p N hz
  exact ⟨⟨hz,hd⟩, BDL26NativeFiniteComposition.totalCost_finite_on_success p N z hz, hd⟩

theorem source_even_davies {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (2*k),
      DaviesGeometry (perturbationOddScale p) (2*k)
        (BDL26NativeFiniteComposition.evaluate p (2*k) z) p.t := by
  filter_upwards [finite_history_davies_ae p (2*k)] with z hz
  simpa only [BDL26NativeFiniteComposition.history_last, Fin.val_last] using hz (Fin.last (2*k))

end QEC.Coding.BDL26NativeDaviesLocality
