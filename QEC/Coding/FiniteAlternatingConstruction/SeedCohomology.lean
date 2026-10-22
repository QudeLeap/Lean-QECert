import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDistance
import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoder

/-!
# First cohomology of the actual five-qubit seed

The coefficient w0+w1 classifies every actual seed cocycle modulo the actual
first coboundaries. The inverse uses the already constructed seedCocycle.
This proves the base calculation of [BDL26, paper.tex:2202--2225,2240,2258]
under approved source gate #840; alternating preservation belongs to #548.
-/

namespace QEC.Coding.BDL26SeedCohomology

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance

abbrev Field := ZMod 2
noncomputable abbrev complex :=
  BDL26LevelTwoDecoder.presentationComplex baseTannerSquarePresentation
noncomputable abbrev Cocycle := complex.middleCocycleCode.carrier
noncomputable abbrev H1 := complex.middleCohomology
noncomputable abbrev classOf : Cocycle →ₗ[Field] H1 :=
  complex.middleCoboundaryInCocycles.mkQ

/-- The actual incidence complex has precisely the registered seed matrices. -/
theorem complex_eq_base : complex = baseChainComplex := by
  change (BDL26LevelTwoDecoder.presentationComplex baseTannerSquarePresentation :
    ChainComplexData Field (Word Field BaseX) (Word Field BaseQubit)
      (Word Field BaseZ)) = baseChainComplex
  simp only [BDL26LevelTwoDecoder.presentationComplex, baseChainComplex,
    base_xqIncidenceMatrix_eq, base_qzIncidenceMatrix_eq, baseBoundary1, baseBoundary2]
  rfl

theorem delta0_eq_tanner : wordLinearMapTranspose complex.boundary1 =
    tannerCoboundary0 baseTannerSquarePresentation := by
  apply LinearMap.ext
  intro a
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ a q

theorem delta1_eq_tanner : wordLinearMapTranspose complex.boundary2 =
    tannerCoboundary1 baseTannerSquarePresentation := by
  apply LinearMap.ext
  intro w
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ w z

/-- The coefficient of the explicit logical representative. -/
def coefficient (w : Word Field BaseQubit) : Field := w 0 + w 1

/-- The boundary potential in every actual cocycle's normal form. -/
def normalPotential (w : Word Field BaseQubit) : Word Field BaseX := ![w 1, w 3]

theorem coefficient_coboundary : ∀ a : Word Field BaseX,
    coefficient (tannerCoboundary0 baseTannerSquarePresentation a) = 0 := by
  decide

theorem coefficient_seed : coefficient seedCocycle = 1 := by decide

/-- Exact finite-coordinate calculation for every actual seed cocycle. -/
theorem cocycle_decomposition : ∀ w : Word Field BaseQubit,
    tannerCoboundary1 baseTannerSquarePresentation w = 0 →
    w = fun q => tannerCoboundary0 baseTannerSquarePresentation (normalPotential w) q +
      coefficient w * seedCocycle q := by
  intro w hw
  -- Decide only finite scalar equations. The actual presentation's Z carrier
  -- is definitionally BaseZ, but its function-equality decider is not inferred.
  have coordinates : ∀ v : Word Field BaseQubit,
      tannerCoboundary1 baseTannerSquarePresentation v (0 : BaseZ) = 0 →
      tannerCoboundary1 baseTannerSquarePresentation v (1 : BaseZ) = 0 →
      ∀ q : BaseQubit,
        v q = tannerCoboundary0 baseTannerSquarePresentation (normalPotential v) q +
          coefficient v * seedCocycle q := by
    decide
  funext q
  exact coordinates w (congrFun hw (0 : BaseZ)) (congrFun hw (1 : BaseZ)) q

noncomputable def coefficientMap : Cocycle →ₗ[Field] Field where
  toFun w := coefficient w.1
  map_add' w v := by
    change (w.1 (0 : BaseQubit) + v.1 (0 : BaseQubit)) +
        (w.1 (1 : BaseQubit) + v.1 (1 : BaseQubit)) =
      (w.1 (0 : BaseQubit) + w.1 (1 : BaseQubit)) +
        (v.1 (0 : BaseQubit) + v.1 (1 : BaseQubit))
    ring
  map_smul' c w := by
    change c * w.1 (0 : BaseQubit) + c * w.1 (1 : BaseQubit) =
      c * (w.1 (0 : BaseQubit) + w.1 (1 : BaseQubit))
    ring

theorem boundaries_le_coefficient_kernel : complex.middleCoboundaryInCocycles ≤
    LinearMap.ker coefficientMap := by
  intro w hw
  change w.1 ∈ complex.firstCoboundaryCheckCode.carrier at hw
  obtain ⟨a, ha⟩ := (complex.mem_firstCoboundaryCheckCode_iff w.1).mp hw
  change coefficient w.1 = 0
  rw [← ha, delta0_eq_tanner]
  exact coefficient_coboundary a

/-- Coefficient of a genuine quotient class, independent of its representative. -/
noncomputable def forward : H1 →ₗ[Field] Field :=
  complex.middleCoboundaryInCocycles.liftQ coefficientMap
    boundaries_le_coefficient_kernel

@[simp] theorem forward_classOf (w : Cocycle) :
    forward (classOf w) = coefficient w.1 := rfl

noncomputable def seedElement : Cocycle :=
  ⟨seedCocycle, by
    change wordLinearMapTranspose complex.boundary2
      (seedCocycle : Word Field baseTannerSquarePresentation.Q) = 0
    exact (LinearMap.congr_fun delta1_eq_tanner
      (seedCocycle : Word Field baseTannerSquarePresentation.Q)).trans seedCocycle_coboundary⟩

/-- Literal scalar multiple of the already proved actual seed cocycle. -/
noncomputable def generator : Field →ₗ[Field] Cocycle where
  toFun c := c • seedElement
  map_add' c d := add_smul c d seedElement
  map_smul' c d := by simp [mul_smul]

noncomputable def inverse : Field →ₗ[Field] H1 := classOf.comp generator

@[simp] theorem inverse_representative (c : Field) :
    inverse c = classOf (c • seedElement) := rfl

theorem forward_inverse (c : Field) : forward (inverse c) = c := by
  change coefficient (c • seedCocycle) = c
  simp [coefficient, seedCocycle, Pi.smul_apply]

/-- Every class agrees with the class of its computed logical coefficient. -/
theorem classOf_normal_form (w : Cocycle) :
    classOf w = classOf (coefficient w.1 • seedElement) := by
  apply (Submodule.Quotient.eq complex.middleCoboundaryInCocycles).mpr
  change (fun q : BaseQubit =>
    w.1 q - coefficient w.1 * seedCocycle q) ∈
    complex.firstCoboundaryCheckCode.carrier
  apply (complex.mem_firstCoboundaryCheckCode_iff _).mpr
  refine ⟨normalPotential w.1, ?_⟩
  rw [delta0_eq_tanner]
  have hc : tannerCoboundary1 baseTannerSquarePresentation w.1 = 0 :=
    delta1_eq_tanner ▸ (complex.mem_middleCocycleCode_iff w.1).mp w.2
  funext q
  have hq := congrFun (cocycle_decomposition w.1 hc) q
  exact (eq_sub_iff_add_eq).mpr hq.symm

theorem inverse_forward (x : H1) : inverse (forward x) = x := by
  obtain ⟨w, rfl⟩ := complex.middleCoboundaryInCocycles.mkQ_surjective x
  change classOf (coefficient w.1 • seedElement) = classOf w
  exact (classOf_normal_form w).symm

/-- Actual seed first cohomology, with both maps and both inverse identities. -/
noncomputable def equivalence : H1 ≃ₗ[Field] Field where
  toLinearMap := forward
  invFun := inverse
  left_inv := inverse_forward
  right_inv := forward_inverse

@[simp] theorem equivalence_classOf (w : Cocycle) :
    equivalence (classOf w) = coefficient w.1 := rfl

@[simp] theorem equivalence_symm_apply (c : Field) :
    equivalence.symm c = classOf (c • seedElement) := rfl

theorem finrank_eq_one : Module.finrank Field H1 = 1 := by
  rw [equivalence.finrank_eq]
  exact Module.finrank_self Field

theorem seed_class_nonzero : classOf seedElement ≠ 0 := by
  intro h
  have hcoeff := congrArg forward h
  simp only [forward_classOf, map_zero] at hcoeff
  have hbad : (1 : Field) = 0 := coefficient_seed.symm.trans hcoeff
  exact one_ne_zero hbad

/-- The actual recursive state at depth zero uses this same seed quotient. -/
noncomputable def stateZeroEquivalence (S : OddScale) :
    (BDL26LevelTwoDecoder.presentationComplex
      (BDL26DecodingGraph.state S 0).presentation).middleCohomology ≃ₗ[Field] Field :=
  equivalence

theorem stateZero_finrank (S : OddScale) :
    Module.finrank Field (BDL26LevelTwoDecoder.presentationComplex
      (BDL26DecodingGraph.state S 0).presentation).middleCohomology = 1 :=
  finrank_eq_one

@[simp] theorem stateZeroEquivalence_classOf (S : OddScale) (w : Cocycle) :
    stateZeroEquivalence S (classOf w) = coefficient w.1 := rfl

end QEC.Coding.BDL26SeedCohomology
