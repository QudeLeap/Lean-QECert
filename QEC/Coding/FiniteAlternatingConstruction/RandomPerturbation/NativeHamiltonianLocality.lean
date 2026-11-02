import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NativeFiniteComposition

/-!
# Actual Hamiltonian terms on finite native embedding histories

Project-derived internal/API #1639, child of #855. Source route: BDL26 v1,
paper.tex:302–309,2221–2258. The existing native coordinate construction and
its paid cost are unchanged. Coordinate-selected subsystems and canonical
local operators below are semantic postconditions, not extra execution output.
No cost for enumerating certificates or serializing dense matrices is claimed.
-/

noncomputable section
namespace QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Select domain labels, including distinct qubits with identical coordinates. -/
def ballSubsystem (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (c : E) (r : ℝ) :
    FiniteSubsystem (Physical S n) :=
  ⟨qubitHits (state S n).presentation J (Metric.closedBall c r)⟩

@[simp] theorem mem_ballSubsystem (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (c : E) (r : ℝ) (q : Physical S n) :
    q ∈ (ballSubsystem S n J c r).selected ↔ dist (J (.q q)) c ≤ r := by
  simp only [ballSubsystem, qubitHits, Finset.mem_filter, Finset.mem_univ,
    true_and, Metric.mem_closedBall]

theorem ballSubsystem_diameter (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (c : E) (r : ℝ)
    (q u : Physical S n)
    (hq : q ∈ (ballSubsystem S n J c r).selected)
    (hu : u ∈ (ballSubsystem S n J c r).selected) :
    dist (J (.q q)) (J (.q u)) ≤ 2*r := by
  have hq' := (mem_ballSubsystem S n J c r q).mp hq
  have hu' := (mem_ballSubsystem S n J c r u).mp hu
  calc
    _ ≤ dist (J (.q q)) c + dist c (J (.q u)) := dist_triangle _ _ _
    _ ≤ r+r := add_le_add hq' (by simpa only [dist_comm] using hu')
    _ = 2*r := by ring

/-- The actual signed summand of the full Z+X-labelled Hamiltonian. -/
def signedCheck (S : OddScale) (n : ℕ) (j : Sum (ZLabel S n) (XLabel S n)) :
    Operator (Qubit.QubitRegister (Physical S n)) :=
  -toQubitOperator (check S n j)

theorem hamiltonian_signed_sum (S : OddScale) (n : ℕ) :
    hamiltonian S n = ∑ j : Sum (ZLabel S n) (XLabel S n), signedCheck S n j := by
  simp only [hamiltonian, signedCheck, Finset.sum_neg_distrib]

/-- Containment is proved from actual check incidences and the same coordinates. -/
theorem checkSupport_subset_ball (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    checkSupport S n j ⊆ (ballSubsystem S n J (checkCenter S n J j) 1).selected := by
  intro q hq
  exact (mem_ballSubsystem S n J (checkCenter S n J j) 1 q).mpr ((hJ.2.1 j).1 q hq)

/-- Genuine tensor identity-extension support, rather than a metric-only assertion. -/
theorem signedCheck_supported_ball (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (ballSubsystem S n J (checkCenter S n J j) 1).OperatorSupportedOnRegister
      (signedCheck S n j) := by
  have hp : (ballSubsystem S n J (checkCenter S n J j) 1).OperatorSupportedOnRegister
      (toQubitOperator (check S n j)) :=
    CSSDaviesLocality.pauli_supported _ _ (checkSupport_subset_ball S n J hJ j)
  simpa only [signedCheck, neg_one_smul] using
    (ballSubsystem S n J (checkCenter S n J j) 1).supported_smul (-1) hp

/-- A canonical local operator is obtained from the existing concrete restriction. -/
def localCheck (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (j : Sum (ZLabel S n) (XLabel S n)) :
    Operator (ballSubsystem S n J (checkCenter S n J j) 1).selectedSystem :=
  (ballSubsystem S n J (checkCenter S n J j) 1).restrictLocalFromRegister (signedCheck S n j)

theorem extend_localCheck (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (ballSubsystem S n J (checkCenter S n J j) 1).extendLocalToRegister
      (localCheck S n J j) = signedCheck S n j :=
  ((ballSubsystem S n J (checkCenter S n J j) 1).operatorSupportedOnRegister_iff_extend_restrict
    (signedCheck S n j)).mp (signedCheck_supported_ball S n J hJ j)

theorem checkBall_card (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (((ballSubsystem S n J (checkCenter S n J j) 1).selected.card : ℕ) : ℝ) ≤ 2*t :=
  hJ.1 (checkCenter S n J j)

/-- The existing physical embedding, and actual tensor-local Hamiltonian terms.
This predicate is proved below; no caller supplies it to the randomized theorem. -/
def HamiltonianGeometry (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) (t : ℝ) : Prop :=
  PhysicalGeometry S n J t ∧
  hamiltonian S n = (∑ j : Sum (ZLabel S n) (XLabel S n), signedCheck S n j) ∧
  ∀ j : Sum (ZLabel S n) (XLabel S n),
    (ballSubsystem S n J (checkCenter S n J j) 1).extendLocalToRegister (localCheck S n J j) =
      signedCheck S n j ∧
    ((((ballSubsystem S n J (checkCenter S n J j) 1).selected.card : ℕ) : ℝ) ≤ 2*t) ∧
    (∀ q ∈ (ballSubsystem S n J (checkCenter S n J j) 1).selected,
      dist (J (.q q)) (checkCenter S n J j) ≤ 1) ∧
    (∀ q ∈ (ballSubsystem S n J (checkCenter S n J j) 1).selected,
      ∀ u ∈ (ballSubsystem S n J (checkCenter S n J j) 1).selected,
      dist (J (.q q)) (J (.q u)) ≤ 2) ∧
    (checkSupport S n j).card ≤ 7

theorem hamiltonianGeometry_of_physical (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) : HamiltonianGeometry S n J t := by
  refine ⟨hJ, hamiltonian_signed_sum S n, ?_⟩
  intro j
  refine ⟨extend_localCheck S n J hJ j, checkBall_card S n J hJ j, ?_, ?_,
    (hJ.2.1 j).2.2⟩
  · intro q hq
    exact (mem_ballSubsystem S n J (checkCenter S n J j) 1 q).mp hq
  · intro q hq u hu
    simpa only [mul_one] using ballSubsystem_diameter S n J (checkCenter S n J j) 1 q u hq hu

theorem finiteSuccess_hamiltonian {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : BDL26NativeFiniteComposition.Experiment p N}
    (hz : z ∈ BDL26NativeFiniteComposition.finiteSuccess p N) :
    ∀ i : Fin (N+1),
      HamiltonianGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by
  intro i
  exact hamiltonianGeometry_of_physical _ _ _
    (BDL26NativeFiniteComposition.finiteSuccess_geometry p N hz i)

theorem finite_history_hamiltonian_ae {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N, ∀ i : Fin (N+1),
      HamiltonianGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N] with z hz
  exact finiteSuccess_hamiltonian p N hz

/-- A simultaneous event for all actual levels, on the unchanged native space. -/
def finiteHamiltonianSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Set (BDL26NativeFiniteComposition.Experiment p N) :=
  {z | z ∈ BDL26NativeFiniteComposition.finiteSuccess p N ∧
    ∀ i : Fin (N+1), HamiltonianGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t}

/-- The new tensor postcondition holds on every original successful history. -/
theorem finiteHamiltonianSuccess_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    finiteHamiltonianSuccess p N = BDL26NativeFiniteComposition.finiteSuccess p N := by
  ext z
  constructor
  · exact fun hz => hz.1
  · exact fun hz => ⟨hz, finiteSuccess_hamiltonian p N hz⟩

theorem measurableSet_finiteHamiltonianSuccess {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    MeasurableSet (finiteHamiltonianSuccess p N) := by
  rw [finiteHamiltonianSuccess_eq]
  exact BDL26NativeFiniteComposition.measurableSet_finiteSuccess p N

theorem finiteHamiltonianSuccess_measure {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    BDL26NativeFiniteComposition.experimentLaw p N (finiteHamiltonianSuccess p N) = 1 := by
  rw [finiteHamiltonianSuccess_eq]
  exact BDL26NativeFiniteComposition.finiteSuccess_measure p N

theorem zero_seed_hamiltonian {L : ℝ} (p : GeometricParameters L)
    (z : BDL26NativeFiniteComposition.Experiment p 0) :
    HamiltonianGeometry (perturbationOddScale p) 0
      (BDL26NativeFiniteComposition.evaluate p 0 z) p.t :=
  hamiltonianGeometry_of_physical _ _ _
    (BDL26NativeFiniteComposition.zero_experiment_seed p z).2.2

/-- The same coordinate construction has the new tensor-locality postcondition.
Its original paid cost is unchanged; this does not charge or emit local matrices. -/
theorem fixed_parameters_all_finite (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) ≤
        (BDL26NativeFiniteComposition.totalCoefficient p*
          (BDL26FiniteEmbeddingExperiment.stageQubits p N+1)^1774 : ℕ) ∧
      Integrable (fun z => (BDL26NativeFiniteComposition.totalCost p N z).toReal)
        (BDL26NativeFiniteComposition.experimentLaw p N) ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N,
        z ∈ BDL26NativeFiniteComposition.finiteSuccess p N ∧
        BDL26NativeFiniteComposition.totalCost p N z < ∞ ∧
        ∀ i : Fin (N+1), HamiltonianGeometry (perturbationOddScale p) i.val
          (BDL26NativeFiniteComposition.history p N z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, fun N => ⟨BDL26NativeFiniteComposition.totalCost_integral_le p N,
    (BDL26NativeFiniteComposition.totalCost_integrable p N).2, ?_⟩⟩
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N,
    finite_history_hamiltonian_ae p N] with z hz hh
  exact ⟨hz, BDL26NativeFiniteComposition.totalCost_finite_on_success p N z hz, hh⟩

theorem source_even_hamiltonian {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (2*k),
      HamiltonianGeometry (perturbationOddScale p) (2*k)
        (BDL26NativeFiniteComposition.evaluate p (2*k) z) p.t := by
  filter_upwards [finite_history_hamiltonian_ae p (2*k)] with z hz
  simpa only [BDL26NativeFiniteComposition.history_last, Fin.val_last] using hz (Fin.last (2*k))

end QEC.Coding.BDL26NativeHamiltonianLocality
