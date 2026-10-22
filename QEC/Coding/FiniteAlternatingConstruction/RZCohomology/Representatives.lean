import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDistance
import QEC.Coding.FiniteAlternatingConstruction.LevelTwoDecoder

/-!
# Actual RZ cocycle and quotient maps

The maps below use the existing incidence-complex first cohomology. Its
coboundaries are the transposes of the incidence boundaries. The forward map
is the selected RZ cochain map, not the contravariant action of a forward
chain map. BDL26 `paper.tex:2097–2114` / approved source gate #840.
-/

namespace QEC.Coding.BDL26RZCohomology

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge BDL26LevelTwoDistance

abbrev Field := BDL26FiniteTannerSquare.Field
noncomputable abbrev complex (P : TannerSquarePresentation) :=
  BDL26LevelTwoDecoder.presentationComplex P
noncomputable abbrev Cocycle (P : TannerSquarePresentation) :=
  (complex P).middleCocycleCode.carrier
noncomputable abbrev H1 (P : TannerSquarePresentation) := (complex P).middleCohomology
noncomputable abbrev classOf (P : TannerSquarePresentation) : Cocycle P →ₗ[Field] H1 P :=
  (complex P).middleCoboundaryInCocycles.mkQ

/-- The semantic degree-zero differential is the actual Tanner coboundary. -/
theorem differential0_eq (P : TannerSquarePresentation) :
    wordLinearMapTranspose (complex P).boundary1 = tannerCoboundary0 P := by
  apply LinearMap.ext
  intro word
  funext q
  exact wordLinearMapTranspose_toLin'_apply _ word q

/-- The semantic degree-one differential is the actual Tanner coboundary. -/
theorem differential1_eq (P : TannerSquarePresentation) :
    wordLinearMapTranspose (complex P).boundary2 = tannerCoboundary1 P := by
  apply LinearMap.ext
  intro word
  funext z
  exact wordLinearMapTranspose_toLin'_apply _ word z

theorem mem_cocycle_iff (P : TannerSquarePresentation) (word : Word Field P.Q) :
    word ∈ (complex P).middleCocycleCode.carrier ↔ tannerCoboundary1 P word = 0 := by
  rw [ChainComplexData.mem_middleCocycleCode_iff, differential1_eq]

theorem mem_boundary_iff (P : TannerSquarePresentation) (word : Word Field P.Q) :
    word ∈ (complex P).firstCoboundaryCheckCode.carrier ↔
      ∃ potential, tannerCoboundary0 P potential = word := by
  rw [ChainComplexData.mem_firstCoboundaryCheckCode_iff, differential0_eq]

noncomputable abbrev successor (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :=
  rzReplacementPresentation P A4.toTannerSquareAdmissible S

/-- Every old cocycle maps to a genuine replacement cocycle. -/
noncomputable def forwardCocycle (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    Cocycle P →ₗ[Field] Cocycle (successor P A4 S) where
  toFun v := ⟨map1Coord P A4 S v.1, by
    apply (mem_cocycle_iff _ _).mpr
    have hc := LinearMap.congr_fun (rzMap_commutes_coboundary1 P A4 S) v.1
    change rzCoboundary1 P A4 S (map1Coord P A4 S v.1) =
      map2Coord P A4 S (tannerCoboundary1 P v.1) at hc
    rw [(mem_cocycle_iff P v.1).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((map1Coord P A4 S).map_add _ _)
  map_smul' _ _ := Subtype.ext ((map1Coord P A4 S).map_smul _ _)

/-- Actual Q-cylinder parity sends every replacement cocycle to an old one. -/
noncomputable def backwardCocycle (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    Cocycle (successor P A4 S) →ₗ[Field] Cocycle P where
  toFun w := ⟨rzQParity P S w.1, by
    apply (mem_cocycle_iff P _).mpr
    exact rzQParity_cocycle P A4 S w.1 ((mem_cocycle_iff _ _).mp w.2)⟩
  map_add' _ _ := Subtype.ext ((rzQParity P S).map_add _ _)
  map_smul' _ _ := Subtype.ext ((rzQParity P S).map_smul _ _)

/-- Old coboundaries vanish in the actual forward target quotient. -/
theorem forward_boundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (complex P).middleCoboundaryInCocycles ≤
      LinearMap.ker ((classOf (successor P A4 S)).comp (forwardCocycle P A4 S)) := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  change classOf (successor P A4 S) (forwardCocycle P A4 S v) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change map1Coord P A4 S v.1 ∈ (complex (successor P A4 S)).firstCoboundaryCheckCode.carrier
  change v.1 ∈ (complex P).firstCoboundaryCheckCode.carrier at hv
  obtain ⟨potential, hp⟩ := (mem_boundary_iff P v.1).mp hv
  apply (mem_boundary_iff _ _).mpr
  refine ⟨rzMap0Coord P S potential, ?_⟩
  have hc := LinearMap.congr_fun (rzMap_commutes_coboundary0 P A4 S) potential
  change rzCoboundary0 P A4 S (rzMap0Coord P S potential) =
    map1Coord P A4 S (tannerCoboundary0 P potential) at hc
  rw [hp] at hc
  funext q
  exact congrFun hc q

/-- Parity sends actual replacement coboundaries to old coboundaries. -/
theorem backward_boundary (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (complex (successor P A4 S)).middleCoboundaryInCocycles ≤
      LinearMap.ker ((classOf P).comp (backwardCocycle P A4 S)) := by
  intro w hw
  apply LinearMap.mem_ker.mpr
  change classOf P (backwardCocycle P A4 S w) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change rzQParity P S w.1 ∈ (complex P).firstCoboundaryCheckCode.carrier
  change w.1 ∈ (complex (successor P A4 S)).firstCoboundaryCheckCode.carrier at hw
  obtain ⟨potential, hp⟩ := (mem_boundary_iff _ w.1).mp hw
  apply (mem_boundary_iff _ _).mpr
  refine ⟨rzOldXParity P S potential, ?_⟩
  rw [← rzQParity_coboundary P A4 S potential]
  exact congrArg (rzQParity P S) hp

/-- Forward H¹ map induced by the literal RZ cochain map. -/
noncomputable def forward (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    H1 P →ₗ[Field] H1 (successor P A4 S) :=
  (complex P).middleCoboundaryInCocycles.liftQ
    ((classOf (successor P A4 S)).comp (forwardCocycle P A4 S))
    (forward_boundary P A4 S)

/-- Backward H¹ map induced by the actual finite parity sum. -/
noncomputable def backward (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    H1 (successor P A4 S) →ₗ[Field] H1 P :=
  (complex (successor P A4 S)).middleCoboundaryInCocycles.liftQ
    ((classOf P).comp (backwardCocycle P A4 S)) (backward_boundary P A4 S)

@[simp] theorem forward_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (v : Cocycle P) :
    forward P A4 S (classOf P v) =
      classOf (successor P A4 S) (forwardCocycle P A4 S v) := rfl

@[simp] theorem backward_mk (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) (w : Cocycle (successor P A4 S)) :
    backward P A4 S (classOf (successor P A4 S) w) =
      classOf P (backwardCocycle P A4 S w) := rfl

end QEC.Coding.BDL26RZCohomology
