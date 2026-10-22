import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.PhysicalLocality
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.RandomizedEmbeddingStep

/-!
# Physical geometry of the actual randomized successor

BDL26 v1 `paper.tex:2120–2198,2227–2238,2252–2256,302–309`, approved #841.
Numerical parameters precede the level. The output is the actual resampling map
followed by the actual parity-selected replacement. This one-step result does
not count recursive execution cost or construct the level-zero embedding.
-/

noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory

variable {L : ℝ}

/-- Both canonical scales have exactly the same threshold, including odd rounding. -/
theorem physical_scale_eq (p : GeometricParameters L) :
    replacementScale (6*(p.m : ℝ)) (p.lambda : ℝ) p.rounding = perturbationOddScale p := rfl

/-- Transport the domain labels along an equality of the actual constructor states. -/
private theorem localMap_cast (C D : ConstructionState) (h : C = D)
    (J : Vertex D.presentation → Space) (t : ℝ) :
    IsBoundedDensityLocalMap C.presentation
      (fun v => J (cast (congrArg (fun A : ConstructionState => Vertex A.presentation) h) v)) t ↔
      IsBoundedDensityLocalMap D.presentation J t := by
  subst D
  rfl

/-- The literal parity-selected replacement coordinates on the actual successor. -/
def replacementOutput (S : OddScale) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) : Vertex (nextState S n C).presentation → Space :=
  @_root_.dite (Vertex (nextState S n C).presentation → Space) (n % 2 = 0)
    (Nat.decEq (n % 2) 0)
    (fun h v => rxVertexPoint C.presentation S J (nextRXVertex S n C h v))
    (fun h v => rzVertexPoint C.presentation C.admissible.toTannerSquareAdmissible S J
      (nextRZVertex S n C h v))

theorem replacementOutput_rx (S : OddScale) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (h : n % 2 = 0) :
    replacementOutput S n C J =
      fun v => rxVertexPoint C.presentation S J (nextRXVertex S n C h v) := by
  exact @_root_.dif_pos (n % 2 = 0) (Nat.decEq (n % 2) 0) h
    (Vertex (nextState S n C).presentation → Space) _ _

theorem replacementOutput_rz (S : OddScale) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (h : ¬ n % 2 = 0) :
    replacementOutput S n C J =
      fun v => rzVertexPoint C.presentation C.admissible.toTannerSquareAdmissible S J
        (nextRZVertex S n C h v) := by
  exact @_root_.dif_neg (n % 2 = 0) (Nat.decEq (n % 2) 0) h
    (Vertex (nextState S n C).presentation → Space) _ _

private theorem rx_parameter_handoff (p : GeometricParameters L) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (hv : BoundedValence C.presentation)
    (hg : IncomingFaceGeometry C.presentation (perturbationOddScale p) J
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda))
    (hd : ∀ c, ((familyHits (oldTriangleImage C.presentation J)
      (Metric.closedBall c 1)).card : ℝ) ≤ triangleDensityBound) :
    IsBoundedDensityLocalMap (rxReplacementPresentation C.presentation (perturbationOddScale p))
      (rxVertexPoint C.presentation (perturbationOddScale p) J) p.t := by
  have hl : (0 : ℝ) < p.lambda := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hm : (1 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.m_two)
  have hgamma : (0 : ℝ) < 6*(p.m : ℝ)*widthFactor-1 := by linarith [p.width_positive]
  have hg' : IncomingFaceGeometry C.presentation
      (replacementScale (6*(p.m : ℝ)) (p.lambda : ℝ) p.rounding) J
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) := by
    simpa only [physical_scale_eq] using hg
  have hh := rx_canonical_handoff C.presentation C.admissible C.regular hv J
    hl hgamma hm (Nat.cast_nonneg triangleDensityBound) p.rounding hg' hd
  have hout : IsBoundedDensityLocalMap
      (rxReplacementPresentation C.presentation (perturbationOddScale p))
      (rxVertexPoint C.presentation (perturbationOddScale p) J) (densityHandoff p.m) := by
    simpa only [physical_scale_eq, densityHandoff] using hh.2.2.2
  exact localMap_mono _ _ hout p.handoff.le

private theorem rz_parameter_handoff (p : GeometricParameters L) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (hv : BoundedValence C.presentation)
    (hg : IncomingFaceGeometry C.presentation (perturbationOddScale p) J
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda))
    (hd : ∀ c, ((familyHits (oldTriangleImage C.presentation J)
      (Metric.closedBall c 1)).card : ℝ) ≤ triangleDensityBound) :
    IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation C.presentation
        C.admissible.toTannerSquareAdmissible (perturbationOddScale p))
      (rzVertexPoint C.presentation C.admissible.toTannerSquareAdmissible
        (perturbationOddScale p) J) p.t := by
  have hl : (0 : ℝ) < p.lambda := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  have hm : (1 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.m_two)
  have hgamma : (0 : ℝ) < 6*(p.m : ℝ)*widthFactor-1 := by linarith [p.width_positive]
  have hg' : IncomingFaceGeometry C.presentation
      (replacementScale (6*(p.m : ℝ)) (p.lambda : ℝ) p.rounding) J
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) := by
    simpa only [physical_scale_eq] using hg
  have hh := rz_canonical_handoff C.presentation C.admissible C.regular hv J
    hl hgamma hm (Nat.cast_nonneg triangleDensityBound) p.rounding hg' hd
  have hout : IsBoundedDensityLocalMap
      (BDL26RZLocalReplacement.rzReplacementPresentation C.presentation
        C.admissible.toTannerSquareAdmissible (perturbationOddScale p))
      (rzVertexPoint C.presentation C.admissible.toTannerSquareAdmissible
        (perturbationOddScale p) J) (densityHandoff p.m) := by
    simpa only [physical_scale_eq, densityHandoff] using hh.2.2.2
  exact localMap_mono _ _ hout p.handoff.le

/-- Geometry and density of the actual resampled word determine the actual successor. -/
theorem replacementOutput_localMap (p : GeometricParameters L) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (hv : BoundedValence C.presentation)
    (hg : IncomingFaceGeometry C.presentation (perturbationOddScale p) J
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda))
    (hd : ∀ c, ((familyHits (oldTriangleImage C.presentation J)
      (Metric.closedBall c 1)).card : ℝ) ≤ triangleDensityBound) :
    IsBoundedDensityLocalMap (nextState (perturbationOddScale p) n C).presentation
      (replacementOutput (perturbationOddScale p) n C J) p.t := by
  by_cases h : n % 2 = 0
  · rw [replacementOutput_rx _ _ _ _ h]
    exact (localMap_cast _ _ (show nextState (perturbationOddScale p) n C =
      rxState (perturbationOddScale p) C from if_pos h) _ _).mpr
        (rx_parameter_handoff p C J hv hg hd)
  · rw [replacementOutput_rz _ _ _ _ h]
    exact (localMap_cast _ _ (show nextState (perturbationOddScale p) n C =
      rzState (perturbationOddScale p) C from if_neg h) _ _).mpr
        (rz_parameter_handoff p C J hv hg hd)

/-- The same actual cap table law, for a fixed scale and source level. -/
def physicalTableLaw (p : GeometricParameters L) (n : Nat) :
    Measure (Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)) := by
  let P := (state (perturbationOddScale p) n).presentation
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  exact tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))

/-- No successful assignment is selected: run the actual total output on each table. -/
def physicalSuccessorOutput (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)) :
    Vertex (state (perturbationOddScale p) (n+1)).presentation → Space :=
  replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n)
    (perturbationEmbeddingOutput _ J p T)

theorem physicalSuccessorOutput_rx (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (h : n % 2 = 0) : physicalSuccessorOutput p n J T = fun v =>
      rxVertexPoint _ (perturbationOddScale p) (perturbationEmbeddingOutput _ J p T)
        (nextRXVertex _ n (state (perturbationOddScale p) n) h v) :=
  replacementOutput_rx _ _ _ _ h

theorem physicalSuccessorOutput_rz (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (h : ¬ n % 2 = 0) : physicalSuccessorOutput p n J T = fun v =>
      rzVertexPoint _ (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
        (perturbationOddScale p) (perturbationEmbeddingOutput _ J p T)
        (nextRZVertex _ n (state (perturbationOddScale p) n) h v) :=
  replacementOutput_rz _ _ _ _ h

/-- The combined endpoint includes the actual full-H support, not only a graph region. -/
def PhysicalSuccessorFacts (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space)) : Prop :=
  let S := perturbationOddScale p
  Halts (eventSupport (state S n).presentation J (anchorRadius p.m))
    (eventBad (state S n).presentation J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
  IsBoundedDensityLocalMap (state S (n+1)).presentation (physicalSuccessorOutput p n J T) p.t ∧
  PhysicalGeometry S (n+1) (physicalSuccessorOutput p n J T) p.t ∧
  (∀ (q : Physical S (n+1)) (a : CSSDaviesLocality.Axis) (ω : ℝ),
    (BDL26CSSDaviesLocality.subsystem S (n+1) q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S (n+1)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+1))
        (BDL26CSSDaviesLocality.coupling S (n+1) q a) ω)) ∧
  (∀ (rate : BDL26CSSDaviesLocality.CouplingIndex S (n+1) →
      BDL26CSSDaviesLocality.Frequency S (n+1) → ℝ)
      (q : Physical S (n+1)) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S (n+1)),
    (BDL26CSSDaviesLocality.subsystem S (n+1) q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S (n+1)) (BDL26CSSDaviesLocality.hamiltonian_symmetric S (n+1))
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S (n+1) =>
          BDL26CSSDaviesLocality.coupling S (n+1) qa.1 qa.2) rate ((q,a),ω)))

/-- Every guarantee follows from actual resampling and actual replacement, almost surely. -/
theorem physical_successor_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, PhysicalSuccessorFacts p n J T := by
  let P := (state (perturbationOddScale p) n).presentation
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  filter_upwards [geometric_output_geometry_density_ae P J p hJ
    (state_boundedValence (perturbationOddScale p) n)] with T hT
  have hout := replacementOutput_localMap p n (state (perturbationOddScale p) n)
    (perturbationEmbeddingOutput P J p T) (state_boundedValence (perturbationOddScale p) n)
    hT.2.1 hT.2.2
  exact ⟨hT.1, hout, physicalGeometry_of_localMap _ _ _ hout,
    BDL26CSSDaviesLocality.frequency_supported _ _,
    BDL26CSSDaviesLocality.weightedJump_supported _ _⟩

theorem physical_successor_localMap_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n J T) p.t := by
  filter_upwards [physical_successor_ae p n J hJ] with T hT
  exact hT.2.1

theorem physical_successor_halts_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n,
      Halts (eventSupport (state (perturbationOddScale p) n).presentation J (anchorRadius p.m))
        (eventBad (state (perturbationOddScale p) n).presentation J
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T := by
  filter_upwards [physical_successor_ae p n J hJ] with T hT
  exact hT.1

theorem physical_successor_density_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, ∀ c,
      ((qubitHits (state (perturbationOddScale p) (n+1)).presentation
        (physicalSuccessorOutput p n J T) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t := by
  filter_upwards [physical_successor_ae p n J hJ] with T hT
  exact hT.2.2.1.1

theorem physical_successor_checks_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, ∀ j : Sum (ZLabel (perturbationOddScale p) (n+1))
      (XLabel (perturbationOddScale p) (n+1)),
      (∀ r ∈ checkSupport (perturbationOddScale p) (n+1) j,
        dist (physicalSuccessorOutput p n J T (.q r))
          (checkCenter _ _ (physicalSuccessorOutput p n J T) j) ≤ 1) ∧
      (∀ r ∈ checkSupport (perturbationOddScale p) (n+1) j,
        ∀ s ∈ checkSupport (perturbationOddScale p) (n+1) j,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 2) ∧
      (checkSupport (perturbationOddScale p) (n+1) j).card ≤ 7 := by
  filter_upwards [physical_successor_ae p n J hJ] with T hT
  exact hT.2.2.1.2.1

theorem physical_successor_regions_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, ∀ q : Physical (perturbationOddScale p) (n+1),
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q q)) ≤ 2) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        ∀ s ∈ region (perturbationOddScale p) (n+1) q,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 4) ∧
      (region (perturbationOddScale p) (n+1) q).card ≤ 50 := by
  filter_upwards [physical_successor_ae p n J hJ] with T hT
  exact hT.2.2.1.2.2

theorem physical_successor_frequency_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t)
    (q : Physical (perturbationOddScale p) (n+1)) (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    ∀ᵐ T ∂physicalTableLaw p n,
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).OperatorSupportedOnRegister
        (actualFrequency (hamiltonian (perturbationOddScale p) (n+1))
          (BDL26CSSDaviesLocality.hamiltonian_symmetric _ _)
          (BDL26CSSDaviesLocality.coupling _ _ q a) ω) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q q)) ≤ 2) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        ∀ s ∈ region (perturbationOddScale p) (n+1) q,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 4) ∧
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).selected.card ≤ 50 := by
  filter_upwards [physical_successor_localMap_ae p n J hJ] with T hT
  exact frequency_physical _ _ _ hT q a ω

theorem physical_successor_weightedJump_ae (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t)
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) (n+1) →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) (n+1) → ℝ)
    (q : Physical (perturbationOddScale p) (n+1)) (a : CSSDaviesLocality.Axis)
    (ω : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) (n+1)) :
    ∀ᵐ T ∂physicalTableLaw p n,
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).OperatorSupportedOnRegister
        (hamiltonianJump (hamiltonian (perturbationOddScale p) (n+1))
          (BDL26CSSDaviesLocality.hamiltonian_symmetric _ _)
          (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) (n+1) =>
            BDL26CSSDaviesLocality.coupling _ _ qa.1 qa.2) rate ((q,a),ω)) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q q)) ≤ 2) ∧
      (∀ r ∈ region (perturbationOddScale p) (n+1) q,
        ∀ s ∈ region (perturbationOddScale p) (n+1) q,
          dist (physicalSuccessorOutput p n J T (.q r)) (physicalSuccessorOutput p n J T (.q s)) ≤ 4) ∧
      (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) (n+1) q).selected.card ≤ 50 := by
  filter_upwards [physical_successor_localMap_ae p n J hJ] with T hT
  exact weightedJump_physical _ _ _ hT rate q a ω

/-- Numerical constants and the odd scale are chosen before every finite level. -/
theorem exists_physical_successor_parameters (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower, ∀ (n : Nat)
      (J : Vertex (state (perturbationOddScale p) n).presentation → Space),
      IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t →
        ∀ᵐ T ∂physicalTableLaw p n, PhysicalSuccessorFacts p n J T := by
  obtain ⟨p⟩ := geometricParameters_nonempty densityLower
  exact ⟨p, physical_successor_ae p⟩

theorem physical_successor_rx_ae (p : GeometricParameters L) (k : Nat)
    (J : Vertex (state (perturbationOddScale p) (2*k)).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) (2*k)).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p (2*k), PhysicalSuccessorFacts p (2*k) J T :=
  physical_successor_ae p (2*k) J hJ

theorem physical_successor_rz_ae (p : GeometricParameters L) (k : Nat)
    (J : Vertex (state (perturbationOddScale p) (2*k+1)).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) (2*k+1)).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p (2*k+1), PhysicalSuccessorFacts p (2*k+1) J T :=
  physical_successor_ae p (2*k+1) J hJ

/-- Source-even targets are positive; no level-zero base claim is inferred. -/
theorem physical_successor_even_ae (p : GeometricParameters L) (k : Nat) (hk : 1 ≤ k)
    (J : Vertex (state (perturbationOddScale p) (2*k-1)).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) (2*k-1)).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p (2*k-1),
      PhysicalSuccessorFacts p (2*k-1) J T ∧
      PhysicalGeometry (perturbationOddScale p) (2*k)
        (fun v => physicalSuccessorOutput p (2*k-1) J T
          (cast (congrArg (fun m => Vertex (state (perturbationOddScale p) m).presentation)
            (show 2*k = (2*k-1)+1 by omega)) v)) p.t := by
  have he : (2*k-1)+1 = 2*k := by omega
  filter_upwards [physical_successor_ae p (2*k-1) J hJ] with T hT
  exact ⟨hT, physicalGeometry_cast _ _ _ he _ _ hT.2.2.1⟩

end QEC.Coding.BDL26RandomPerturbation
