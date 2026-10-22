import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.PhysicalLocality
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.RandomizedEmbeddingStep

/-!
# The actual five-qubit seed geometry

BDL26 v1 `paper.tex:1326–1340,2200–2260,302–309`, approved source gate #841.
The constant realization is project-derived. Its four face and five qubit
labels are counted with multiplicity, including when every image is zero.
This is the initial condition, not a replacement for the randomized recursion.
-/

noncomputable section
namespace QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap

/-- The literal seed presentation is independent of the later chosen scale. -/
def seedPoint (S : OddScale) : Vertex (state S 0).presentation → Space := fun _ => 0

@[simp] theorem seedPoint_eq_zero (S : OddScale) (v : Vertex (state S 0).presentation) :
    seedPoint S v = 0 := rfl

theorem seed_face_card (S : OddScale) : Fintype.card (state S 0).presentation.Face = 4 := by
  change Fintype.card (Fin 4) = 4
  simp

theorem seed_physical_card (S : OddScale) : Fintype.card (Physical S 0) = 5 := by
  change Fintype.card (Fin 5) = 5
  simp

/-- Both actual affine charts vanish for every affine parameter, without a domain restriction. -/
theorem seed_triangle_zero (S : OddScale) (f : (state S 0).presentation.Face)
    (side : Two) (a b : ℝ) :
    tannerTrianglePoint (state S 0).presentation (seedPoint S) f side a b = 0 := by
  simp [tannerTrianglePoint, seedPoint]

theorem seed_face_image (S : OddScale) (f : (state S 0).presentation.Face) :
    tannerFaceImage (state S 0).presentation (seedPoint S) f = {(0 : Space)} := by
  simp [tannerFaceImage, seedPoint, convexHull_singleton]

theorem seed_face_hit_iff (S : OddScale) (f : (state S 0).presentation.Face)
    (ball : Set Space) :
    (tannerFaceImage (state S 0).presentation (seedPoint S) f ∩ ball).Nonempty ↔
      (0 : Space) ∈ ball := by
  rw [seed_face_image]
  simp

/-- Domain faces are retained even though the image consists of one point. -/
theorem seed_face_count (S : OddScale) (c : Space) :
    (familyHits (tannerFaceImage (state S 0).presentation (seedPoint S))
      (Metric.closedBall c 1)).card =
        if (0 : Space) ∈ Metric.closedBall c 1 then 4 else 0 := by
  simp only [familyHits, seed_face_hit_iff]
  by_cases h : (0 : Space) ∈ Metric.closedBall c 1
  · simp only [h, if_true, Finset.filter_true, Finset.card_univ, seed_face_card]
  · simp [h]

/-- Physical labels, rather than distinct image points, give the exact count five. -/
theorem seed_qubit_count (S : OddScale) (c : Space) :
    (qubitHits (state S 0).presentation (seedPoint S) (Metric.closedBall c 1)).card =
      if (0 : Space) ∈ Metric.closedBall c 1 then 5 else 0 := by
  simp only [qubitHits, seedPoint]
  by_cases h : (0 : Space) ∈ Metric.closedBall c 1
  · simp only [h, if_true, Finset.filter_true, Finset.card_univ]
    exact seed_physical_card S
  · simp [h]

theorem seed_localMap (S : OddScale) :
    IsBoundedDensityLocalMap (state S 0).presentation (seedPoint S) 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x q h
    simp [seedPoint]
  · intro q z h
    simp [seedPoint]
  · intro c
    rw [seed_face_count]
    split_ifs <;> norm_num

/-- Only the existing numerical triangle-density inequality is used. -/
theorem four_le_parameter {L : ℝ} (p : GeometricParameters L) : (4 : ℝ) ≤ p.t := by
  have h := p.triangle_density
  norm_num [triangleDensityBound] at h
  linarith

theorem five_le_twice_parameter {L : ℝ} (p : GeometricParameters L) : (5 : ℝ) ≤ 2*p.t := by
  have h := four_le_parameter p
  linarith

/-- The seed fits the same arbitrary parameters and their same odd scale. -/
theorem seed_parameter_localMap {L : ℝ} (p : GeometricParameters L) :
    IsBoundedDensityLocalMap (state (perturbationOddScale p) 0).presentation
      (seedPoint (perturbationOddScale p)) p.t :=
  localMap_mono _ _ (seed_localMap (perturbationOddScale p)) (four_le_parameter p)

theorem seed_qubit_density (S : OddScale) (c : Space) :
    ((qubitHits (state S 0).presentation (seedPoint S) (Metric.closedBall c 1)).card : ℝ) ≤ 5 := by
  rw [seed_qubit_count]
  split_ifs <;> norm_num

theorem seed_parameter_density {L : ℝ} (p : GeometricParameters L) (c : Space) :
    ((qubitHits (state (perturbationOddScale p) 0).presentation
      (seedPoint (perturbationOddScale p)) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t :=
  (seed_qubit_density (perturbationOddScale p) c).trans (five_le_twice_parameter p)

@[simp] theorem seed_physical_zero (S : OddScale) (q : Physical S 0) :
    seedPoint S (.q q) = 0 := rfl

theorem seed_check_center_zero (S : OddScale) (j : Sum (ZLabel S 0) (XLabel S 0)) :
    checkCenter S 0 (seedPoint S) j = 0 := by
  cases j <;> rfl

/-- The sharper seed geometry holds for all labels, even outside a selected check. -/
theorem seed_check_radius_zero (S : OddScale) (j : Sum (ZLabel S 0) (XLabel S 0))
    (r : Physical S 0) : dist (seedPoint S (.q r)) (checkCenter S 0 (seedPoint S) j) = 0 := by
  rw [seed_check_center_zero, seed_physical_zero, dist_self]

theorem seed_physical_distance_zero (S : OddScale) (r s : Physical S 0) :
    dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0 := by
  simp only [seed_physical_zero, dist_self]

theorem seed_check_card (S : OddScale) (j : Sum (ZLabel S 0) (XLabel S 0)) :
    (checkSupport S 0 j).card ≤ 5 := by
  have h := Finset.card_le_card (Finset.subset_univ (checkSupport S 0 j))
  simpa only [Finset.card_univ, seed_physical_card] using h

/-- The very same full-H subsystem region is a subset of all five physical labels. -/
theorem seed_region_card (S : OddScale) (q : Physical S 0) : (region S 0 q).card ≤ 5 := by
  have h := Finset.card_le_card (Finset.subset_univ (region S 0 q))
  simpa only [Finset.card_univ, seed_physical_card] using h

theorem seed_physicalGeometry {L : ℝ} (p : GeometricParameters L) :
    PhysicalGeometry (perturbationOddScale p) 0 (seedPoint (perturbationOddScale p)) p.t :=
  physicalGeometry_of_localMap _ _ _ (seed_parameter_localMap p)

/-- All real frequencies of the actual full Hamiltonian have zero-diameter seed support. -/
theorem seed_frequency_physical (S : OddScale) (q : Physical S 0)
    (a : CSSDaviesLocality.Axis) (ω : ℝ) :
    (BDL26CSSDaviesLocality.subsystem S 0 q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian S 0) (BDL26CSSDaviesLocality.hamiltonian_symmetric S 0)
        (BDL26CSSDaviesLocality.coupling S 0 q a) ω) ∧
    (∀ r ∈ region S 0 q, dist (seedPoint S (.q r)) (seedPoint S (.q q)) = 0) ∧
    (∀ r ∈ region S 0 q, ∀ s ∈ region S 0 q,
      dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0) ∧
    (BDL26CSSDaviesLocality.subsystem S 0 q).selected.card ≤ 5 :=
  ⟨BDL26CSSDaviesLocality.frequency_supported S 0 q a ω,
    fun r _ => seed_physical_distance_zero S r q,
    fun r _ s _ => seed_physical_distance_zero S r s, seed_region_card S q⟩

/-- No rate hypothesis is needed for the actual square-root-rate jump support. -/
theorem seed_weightedJump_physical (S : OddScale)
    (rate : BDL26CSSDaviesLocality.CouplingIndex S 0 → BDL26CSSDaviesLocality.Frequency S 0 → ℝ)
    (q : Physical S 0) (a : CSSDaviesLocality.Axis) (ω : BDL26CSSDaviesLocality.Frequency S 0) :
    (BDL26CSSDaviesLocality.subsystem S 0 q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian S 0) (BDL26CSSDaviesLocality.hamiltonian_symmetric S 0)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex S 0 =>
          BDL26CSSDaviesLocality.coupling S 0 qa.1 qa.2) rate ((q,a),ω)) ∧
    (∀ r ∈ region S 0 q, dist (seedPoint S (.q r)) (seedPoint S (.q q)) = 0) ∧
    (∀ r ∈ region S 0 q, ∀ s ∈ region S 0 q,
      dist (seedPoint S (.q r)) (seedPoint S (.q s)) = 0) ∧
    (BDL26CSSDaviesLocality.subsystem S 0 q).selected.card ≤ 5 :=
  ⟨BDL26CSSDaviesLocality.weightedJump_supported S 0 rate q a ω,
    fun r _ => seed_physical_distance_zero S r q,
    fun r _ s _ => seed_physical_distance_zero S r s, seed_region_card S q⟩

/-- Parameters are constructed independently of any later level or incoming map. -/
theorem exists_seed_parameters (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) 0).presentation
        (seedPoint (perturbationOddScale p)) p.t ∧
      (∀ c, ((qubitHits (state (perturbationOddScale p) 0).presentation
        (seedPoint (perturbationOddScale p)) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t) ∧
      PhysicalGeometry (perturbationOddScale p) 0 (seedPoint (perturbationOddScale p)) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty densityLower
  exact ⟨p, seed_parameter_localMap p, seed_parameter_density p, seed_physicalGeometry p⟩

end QEC.Coding.BDL26RandomSeedEmbedding
