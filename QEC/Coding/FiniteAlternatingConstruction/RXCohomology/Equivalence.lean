import QEC.Coding.FiniteAlternatingConstruction.RXCohomology.Geometry

/-! # Literal RX first-cohomology equivalence from actual gauge geometry -/

namespace QEC.Coding.BDL26RXCohomology

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
open scoped Classical BigOperators

/-- Identity on the actual coordinates, with an explicit raw-word return type.
The materialized presentation and raw carrier agree definitionally. -/
def coordinateWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (rxReplacementPresentation P S).Q) : Word Field (RX1 P S) :=
  fun q => w q

/-- Identity in the other direction, with the actual semantic carrier explicit. -/
def semanticWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S)) : Word Field (rxReplacementPresentation P S).Q :=
  fun q => w q

@[simp] theorem semanticWord_coordinateWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (rxReplacementPresentation P S).Q) :
    semanticWord P S (coordinateWord P S w) = w := rfl

@[simp] theorem coordinateWord_semanticWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S)) : coordinateWord P S (semanticWord P S w) = w := rfl

theorem semanticWord_sub (P : TannerSquarePresentation) (S : OddScale)
    (u v : Word Field (RX1 P S)) :
    semanticWord P S (u-v) = semanticWord P S u - semanticWord P S v := rfl

/-- Actual matrix comparison in semantic coordinates; no discarded coordinate. -/
theorem semanticWord_delta0 (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (f : Word Field (RX0 P S)) :
    tannerCoboundary0 (rxReplacementPresentation P S) f =
      semanticWord P S (rxCoboundary0 P S f) := by
  rw [differential0_eq P A R S]
  rfl

/-- Every actual cocycle is a literal old lift plus a full constructed boundary. -/
theorem full_gauge_residual (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) :
    ∃ (v : Cocycle P) (f : Word Field (RX0 P S)),
      rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f := by
  have hw : rxCoboundary1 P S w.1 = 0 := by
    rw [← differential1_eq P A R S]
    exact (BDL26RZCohomology.mem_cocycle_iff _ _).mp w.2
  obtain ⟨potentials,hp⟩ := local_potentials P A R S w.1 hw
  let f := ∑ x : P.X, xLift P S x (potentials x)
  let residual : Word Field (RX1 P S) := coordinateWord P S w.1 - rxCoboundary0 P S f
  have hb : semanticWord P S (rxCoboundary0 P S f) ∈
      (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier := by
    apply (BDL26RZCohomology.mem_boundary_iff _ _).mpr
    exact ⟨f, semanticWord_delta0 P A R S f⟩
  have hr : semanticWord P S residual ∈
      (complex (rxReplacementPresentation P S)).middleCocycleCode.carrier := by
    rw [show semanticWord P S residual =
      w.1 - semanticWord P S (rxCoboundary0 P S f) from
        (semanticWord_sub P S _ _).trans (by rw [semanticWord_coordinateWord])]
    exact Submodule.sub_mem _ w.2
      ((complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode_le_middleCocycleCode hb)
  have hraw : rxCoboundary1 P S residual = 0 := by
    have hsemantic := (BDL26RZCohomology.mem_cocycle_iff _ _).mp hr
    rw [differential1_eq P A R S] at hsemantic
    exact hsemantic
  have hx := full_gauge_x_zero P S w.1 potentials hp
  let v : Cocycle P := ⟨coarseWord P S residual,
    (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
      (normalized_cocycle P A.toTannerSquareAdmissible S residual hraw hx)⟩
  exact ⟨v,f, normalized_word P A.toTannerSquareAdmissible S residual hraw hx⟩

/-- The actual forward cocycle map uses the literal selected coordinate map. -/
noncomputable def forwardCocycle (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    Cocycle P →ₗ[Field] Cocycle (rxReplacementPresentation P S) where
  toFun v := ⟨rxMap1Coord P S v.1, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    rw [differential1_eq P A R S]
    have hc := LinearMap.congr_fun (rxMap_commutes_coboundary1 P S) v.1
    change rxCoboundary1 P S (rxMap1Coord P S v.1) =
      rxMap2Coord P S (tannerCoboundary1 P v.1) at hc
    rw [(BDL26RZCohomology.mem_cocycle_iff _ _).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((rxMap1Coord P S).map_add _ _)
  map_smul' _ _ := Subtype.ext ((rxMap1Coord P S).map_smul _ _)

/-- Exact boundary characterization in the existing semantic quotient. -/
theorem boundary_iff (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (v : Word Field P.Q) :
    semanticWord P S (rxMap1Coord P S v) ∈
      (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier ↔
      v ∈ (complex P).firstCoboundaryCheckCode.carrier := by
  constructor
  · intro hb
    obtain ⟨f,hf⟩ := (BDL26RZCohomology.mem_boundary_iff
      (rxReplacementPresentation P S) (semanticWord P S (rxMap1Coord P S v))).mp hb
    have hraw : rxCoboundary0 P S f = rxMap1Coord P S v := by
      have hd := LinearMap.congr_fun (differential0_eq P A R S) f
      funext q
      exact (congrFun hd q).symm.trans (congrFun hf q)
    exact (BDL26RZCohomology.mem_boundary_iff P v).mpr
      ((raw_boundary_iff P A.toTannerSquareAdmissible S v).mp ⟨f,hraw⟩)
  · intro hb
    obtain ⟨old,ho⟩ := (BDL26RZCohomology.mem_boundary_iff P v).mp hb
    obtain ⟨f,hf⟩ := (raw_boundary_iff P A.toTannerSquareAdmissible S v).mpr ⟨old,ho⟩
    apply (BDL26RZCohomology.mem_boundary_iff
      (rxReplacementPresentation P S) (semanticWord P S (rxMap1Coord P S v))).mpr
    exact ⟨f, (semanticWord_delta0 P A R S f).trans (congrArg (semanticWord P S) hf)⟩

theorem forward_boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    (complex P).middleCoboundaryInCocycles ≤
      LinearMap.ker ((classOf (rxReplacementPresentation P S)).comp (forwardCocycle P A R S)) := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (boundary_iff P A R S v.1).mpr hv

/-- Descend the literal selected map, using its proved degree-zero identity. -/
noncomputable def forward (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    H1 P →ₗ[Field] H1 (rxReplacementPresentation P S) :=
  (complex P).middleCoboundaryInCocycles.liftQ
    ((classOf (rxReplacementPresentation P S)).comp (forwardCocycle P A R S))
    (forward_boundary P A R S)

@[simp] theorem forward_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    forward P A R S (classOf P v) =
      classOf (rxReplacementPresentation P S) (forwardCocycle P A R S v) := rfl

/-- A complete gauge equality is an equality of actual quotient classes. -/
theorem gauge_class (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (v : Cocycle P)
    (f : Word Field (RX0 P S))
    (hf : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f) :
    forward P A R S (classOf P v) = classOf (rxReplacementPresentation P S) w := by
  rw [forward_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change semanticWord P S (rxMap1Coord P S v.1 - coordinateWord P S w.1) ∈
    (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier
  apply (BDL26RZCohomology.mem_boundary_iff _ _).mpr
  have hraw : rxCoboundary0 P S (-f) = rxMap1Coord P S v.1 - coordinateWord P S w.1 := by
    rw [map_neg, hf]
    abel
  exact ⟨-f, (semanticWord_delta0 P A R S (-f)).trans (congrArg (semanticWord P S) hraw)⟩

/-- Geometric normalization proves quotient surjectivity. -/
theorem forward_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    Function.Surjective (forward P A R S) := by
  intro h
  obtain ⟨w,rfl⟩ := (complex (rxReplacementPresentation P S)).middleCoboundaryInCocycles.mkQ_surjective h
  obtain ⟨v,f,hf⟩ := full_gauge_residual P A R S w
  exact ⟨classOf P v, gauge_class P A R S w v f hf⟩

/-- Actual CX degree-zero connectedness proves quotient injectivity. -/
theorem forward_injective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    Function.Injective (forward P A R S) := by
  intro u v huv
  obtain ⟨a,rfl⟩ := (complex P).middleCoboundaryInCocycles.mkQ_surjective u
  obtain ⟨b,rfl⟩ := (complex P).middleCoboundaryInCocycles.mkQ_surjective v
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (boundary_iff P A R S (a-b).1).mp
  have hz : forward P A R S (classOf P (a-b)) = 0 := by
    rw [map_sub, map_sub, huv, sub_self]
  rw [forward_mk] at hz
  have hb := (Submodule.Quotient.mk_eq_zero
    (complex (rxReplacementPresentation P S)).middleCoboundaryInCocycles).mp hz
  change semanticWord P S (rxMap1Coord P S (a-b).1) ∈
    (complex (rxReplacementPresentation P S)).firstCoboundaryCheckCode.carrier at hb
  exact hb

/-- Actual RX H¹ equivalence. The inverse is derived only after geometric
surjectivity and injectivity; no caller-supplied equivalence is accepted. -/
noncomputable def equiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale) :
    H1 P ≃ₗ[Field] H1 (rxReplacementPresentation P S) :=
  LinearEquiv.ofBijective (forward P A R S)
    ⟨forward_injective P A R S, forward_surjective P A R S⟩

@[simp] theorem equiv_mk (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : Cocycle P) :
    equiv P A R S (classOf P v) =
      classOf (rxReplacementPresentation P S) (forwardCocycle P A R S v) := forward_mk P A R S v

theorem backward_forward (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (v : H1 P) :
    (equiv P A R S).symm (equiv P A R S v) = v := LinearEquiv.symm_apply_apply _ _

theorem forward_backward (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (w : H1 (rxReplacementPresentation P S)) :
    equiv P A R S ((equiv P A R S).symm w) = w := LinearEquiv.apply_symm_apply _ _

/-- Every complete normalization determines the inverse class. -/
theorem inverse_gauge_class (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (v : Cocycle P)
    (f : Word Field (RX0 P S))
    (hf : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S f) :
    (equiv P A R S).symm (classOf (rxReplacementPresentation P S) w) = classOf P v := by
  apply (equiv P A R S).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (gauge_class P A R S w v f hf).symm

/-- Different local gauge potentials yield old words differing by an actual
old coboundary, rather than merely agreeing on a Q-sector readout. -/
theorem gauge_choice_independent (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S)) (u v : Cocycle P)
    (f g : Word Field (RX0 P S))
    (hf : rxMap1Coord P S u.1 = coordinateWord P S w.1 - rxCoboundary0 P S f)
    (hg : rxMap1Coord P S v.1 = coordinateWord P S w.1 - rxCoboundary0 P S g) :
    u.1 - v.1 ∈ (complex P).firstCoboundaryCheckCode.carrier := by
  have hclasses : classOf P u = classOf P v :=
    (inverse_gauge_class P A R S w u f hf).symm.trans (inverse_gauge_class P A R S w v g hg)
  have hz : classOf P (u-v) = 0 := by rw [map_sub, hclasses, sub_self]
  have hb := (Submodule.Quotient.mk_eq_zero
    (complex P).middleCoboundaryInCocycles).mp hz
  change u.1 - v.1 ∈ (complex P).firstCoboundaryCheckCode.carrier at hb
  exact hb

/-- Inverse action on every actual zero-X cocycle uses the genuine cone-point
readout on both connected copies. -/
theorem inverse_normalized (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P) (S : OddScale)
    (w : Cocycle (rxReplacementPresentation P S))
    (hx : ∀ x, restrictWordLinear ((localX P S).correctionRegion x) w.1 = 0) :
    ∃ v : Cocycle P, v.1 = coarseWord P S w.1 ∧
      (equiv P A R S).symm (classOf (rxReplacementPresentation P S) w) = classOf P v := by
  have hw : rxCoboundary1 P S w.1 = 0 := by
    rw [← differential1_eq P A R S]
    exact (BDL26RZCohomology.mem_cocycle_iff _ _).mp w.2
  let v : Cocycle P := ⟨coarseWord P S w.1,
    (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
      (normalized_cocycle P A.toTannerSquareAdmissible S w.1 hw hx)⟩
  refine ⟨v,rfl,inverse_gauge_class P A R S w v 0 ?_⟩
  rw [map_zero, sub_zero]
  exact normalized_word P A.toTannerSquareAdmissible S w.1 hw hx

end QEC.Coding.BDL26RXCohomology
