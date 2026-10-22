import QEC.Coding.FiniteAlternatingConstruction.SeedCohomology
import QEC.Coding.FiniteAlternatingConstruction.RXCohomology
import QEC.Coding.FiniteAlternatingConstruction.RZCohomology

/-!
# First cohomology of every finite actual alternating prefix

BDL26 v1 `paper.tex:1817–1935,2097–2114,2202–2225,2240,2258`,
approved source gate #840. The every-prefix statement below follows by
composing the actual selected RX and RZ maps, starting from the actual seed.
It supplies an internal H¹ calculation; CSS logical-dimension release is
separate.
-/

namespace QEC.Coding.BDL26FiniteCohomology

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

abbrev Field := ZMod 2
noncomputable abbrev complex (S : OddScale) (n : Nat) :=
  BDL26LevelTwoDecoder.presentationComplex (state S n).presentation
noncomputable abbrev Cocycle (S : OddScale) (n : Nat) :=
  (complex S n).middleCocycleCode.carrier
noncomputable abbrev H1 (S : OddScale) (n : Nat) := (complex S n).middleCohomology
noncomputable abbrev classOf (S : OddScale) (n : Nat) : Cocycle S n →ₗ[Field] H1 S n :=
  (complex S n).middleCoboundaryInCocycles.mkQ

/-- The actual next cochain map on every parity's complete cocycle word. -/
noncomputable def stepCocycle (S : OddScale) (n : Nat) :
    Cocycle S n →ₗ[Field] Cocycle S (n+1) :=
  BDL26RXCohomology.nextCocycle S n (state S n)

@[simp] theorem stepCocycle_value (S : OddScale) (n : Nat) (w : Cocycle S n) :
    (stepCocycle S n w).1 = stepMap1 S n w.1 := rfl

/-- Combine the proved actual replacements using their defining parity branch. -/
noncomputable def stepEquiv (S : OddScale) (n : Nat) : H1 S n ≃ₗ[Field] H1 S (n+1) :=
  @_root_.dite (H1 S n ≃ₗ[Field] H1 S (n+1)) (n % 2 = 0) (Nat.decEq (n % 2) 0)
    (fun h => BDL26RXCohomology.nextEquiv S n (state S n) h)
    (fun h => BDL26RZCohomology.nextEquiv S n (state S n) h)

theorem stepEquiv_rx (S : OddScale) (n : Nat) (h : n % 2 = 0) :
    stepEquiv S n = BDL26RXCohomology.nextEquiv S n (state S n) h := by
  exact @_root_.dif_pos (n % 2 = 0) (Nat.decEq (n % 2) 0) h
    (H1 S n ≃ₗ[Field] H1 S (n+1))
    (fun hp => BDL26RXCohomology.nextEquiv S n (state S n) hp)
    (fun hn => BDL26RZCohomology.nextEquiv S n (state S n) hn)

theorem stepEquiv_rz (S : OddScale) (n : Nat) (h : ¬ n % 2 = 0) :
    stepEquiv S n = BDL26RZCohomology.nextEquiv S n (state S n) h := by
  exact @_root_.dif_neg (n % 2 = 0) (Nat.decEq (n % 2) 0) h
    (H1 S n ≃ₗ[Field] H1 S (n+1))
    (fun hp => BDL26RXCohomology.nextEquiv S n (state S n) hp)
    (fun hn => BDL26RZCohomology.nextEquiv S n (state S n) hn)

theorem stepEquiv_mk (S : OddScale) (n : Nat) (w : Cocycle S n) :
    stepEquiv S n (classOf S n w) = classOf S (n+1) (stepCocycle S n w) := by
  by_cases h : n % 2 = 0
  · rw [stepEquiv_rx S n h]
    exact BDL26RXCohomology.nextEquiv_mk S n (state S n) h w
  · rw [stepEquiv_rz S n h]
    exact BDL26RZCohomology.nextEquiv_mk S n (state S n) h w

theorem step_left_inverse (S : OddScale) (n : Nat) (v : H1 S n) :
    (stepEquiv S n).symm (stepEquiv S n v) = v := (stepEquiv S n).symm_apply_apply v

theorem step_right_inverse (S : OddScale) (n : Nat) (v : H1 S (n+1)) :
    stepEquiv S n ((stepEquiv S n).symm v) = v := (stepEquiv S n).apply_symm_apply v

/-- Finite actual composition, in traversal order from the actual seed. -/
noncomputable def prefixEquiv (S : OddScale) : ∀ n, H1 S 0 ≃ₗ[Field] H1 S n
  | 0 => LinearEquiv.refl Field (H1 S 0)
  | n+1 => (prefixEquiv S n).trans (stepEquiv S n)

@[simp] theorem prefixEquiv_zero (S : OddScale) :
    prefixEquiv S 0 = LinearEquiv.refl Field (H1 S 0) := rfl

theorem prefixEquiv_succ (S : OddScale) (n : Nat) :
    prefixEquiv S (n+1) = (prefixEquiv S n).trans (stepEquiv S n) := rfl

/-- Complete seed-to-prefix word, using the existing finite coordinate map. -/
noncomputable def prefixCocycle (S : OddScale) (n : Nat) :
    Cocycle S 0 →ₗ[Field] Cocycle S n where
  toFun w := ⟨BDL26AlternatingCochain.map1 S n w.1, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have hc := LinearMap.congr_fun (map_commutes1 S n) w.1
    change tannerCoboundary1 (state S n).presentation (BDL26AlternatingCochain.map1 S n w.1) =
      BDL26AlternatingCochain.map2 S n (tannerCoboundary1 (state S 0).presentation w.1) at hc
    rw [(BDL26RZCohomology.mem_cocycle_iff _ _).mp w.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((BDL26AlternatingCochain.map1 S n).map_add _ _)
  map_smul' _ _ := Subtype.ext ((BDL26AlternatingCochain.map1 S n).map_smul _ _)

@[simp] theorem prefixCocycle_value (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    (prefixCocycle S n w).1 = BDL26AlternatingCochain.map1 S n w.1 := rfl

@[simp] theorem prefixCocycle_zero (S : OddScale) (w : Cocycle S 0) :
    prefixCocycle S 0 w = w := by
  apply Subtype.ext
  rfl

/-- This is equality of the entire selected representative, on either parity. -/
theorem prefixCocycle_succ (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    prefixCocycle S (n+1) w = stepCocycle S n (prefixCocycle S n w) := by
  apply Subtype.ext
  rfl

/-- The composed quotient equivalence is induced by that very same prefix map. -/
theorem prefixEquiv_mk (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    prefixEquiv S n (classOf S 0 w) = classOf S n (prefixCocycle S n w) := by
  induction n with
  | zero => rw [prefixCocycle_zero]; rfl
  | succ n ih =>
    change stepEquiv S n (prefixEquiv S n (classOf S 0 w)) = _
    rw [ih, stepEquiv_mk, prefixCocycle_succ]

theorem prefix_left_inverse (S : OddScale) (n : Nat) (v : H1 S 0) :
    (prefixEquiv S n).symm (prefixEquiv S n v) = v := (prefixEquiv S n).symm_apply_apply v

theorem prefix_right_inverse (S : OddScale) (n : Nat) (v : H1 S n) :
    prefixEquiv S n ((prefixEquiv S n).symm v) = v := (prefixEquiv S n).apply_symm_apply v

/-- Actual finite-family first cohomology, with the seed coefficient convention. -/
noncomputable def finiteH1Equiv (S : OddScale) (n : Nat) : H1 S n ≃ₗ[Field] Field :=
  (prefixEquiv S n).symm.trans (BDL26SeedCohomology.stateZeroEquivalence S)

@[simp] theorem finiteH1Equiv_zero (S : OddScale) :
    finiteH1Equiv S 0 = BDL26SeedCohomology.stateZeroEquivalence S := by
  ext v
  rfl

theorem finite_left_inverse (S : OddScale) (n : Nat) (v : H1 S n) :
    (finiteH1Equiv S n).symm (finiteH1Equiv S n v) = v := (finiteH1Equiv S n).symm_apply_apply v

theorem finite_right_inverse (S : OddScale) (n : Nat) (c : Field) :
    finiteH1Equiv S n ((finiteH1Equiv S n).symm c) = c := (finiteH1Equiv S n).apply_symm_apply c

/-- Every arbitrary seed representative has its original computed coefficient. -/
theorem finiteH1Equiv_prefix_mk (S : OddScale) (n : Nat) (w : Cocycle S 0) :
    finiteH1Equiv S n (classOf S n (prefixCocycle S n w)) =
      BDL26SeedCohomology.coefficient w.1 := by
  rw [← prefixEquiv_mk]
  change BDL26SeedCohomology.stateZeroEquivalence S
    ((prefixEquiv S n).symm (prefixEquiv S n (classOf S 0 w))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact BDL26SeedCohomology.stateZeroEquivalence_classOf S w

/-- The inverse on every scalar is the literal selected prefix seed generator. -/
theorem finiteH1Equiv_symm_scalar (S : OddScale) (n : Nat) (c : Field) :
    (finiteH1Equiv S n).symm c = classOf S n
      (prefixCocycle S n (c • BDL26SeedCohomology.seedElement)) := by
  change prefixEquiv S n (BDL26SeedCohomology.equivalence.symm c) = _
  rw [BDL26SeedCohomology.equivalence_symm_apply]
  exact prefixEquiv_mk S n _

/-- Actual canonical logical representative, transported through every sector. -/
noncomputable def generator (S : OddScale) (n : Nat) (c : Field) : Cocycle S n :=
  prefixCocycle S n (c • BDL26SeedCohomology.seedElement)

@[simp] theorem generator_value (S : OddScale) (n : Nat) (c : Field) :
    (generator S n c).1 = BDL26AlternatingCochain.map1 S n
      (c • BDL26SeedCohomology.seedElement).1 := rfl

/-- Every actual global cocycle class has its computed scalar normal form. -/
theorem class_normal_form (S : OddScale) (n : Nat) (v : Cocycle S n) :
    classOf S n v = classOf S n (generator S n (finiteH1Equiv S n (classOf S n v))) := by
  change classOf S n v = classOf S n
    (prefixCocycle S n (finiteH1Equiv S n (classOf S n v) • BDL26SeedCohomology.seedElement))
  rw [← finiteH1Equiv_symm_scalar]
  exact ((finiteH1Equiv S n).symm_apply_apply (classOf S n v)).symm

/-- Extract a real global degree-zero potential from quotient equality. This
is a full-word normal form, including all auxiliary replacement coordinates. -/
theorem global_normal_form (S : OddScale) (n : Nat) (v : Cocycle S n) :
    ∃ f : Word Field (state S n).presentation.X,
      v.1 = tannerCoboundary0 (state S n).presentation f +
        (generator S n (finiteH1Equiv S n (classOf S n v))).1 := by
  let g := generator S n (finiteH1Equiv S n (classOf S n v))
  have hg : classOf S n v = classOf S n g := class_normal_form S n v
  have hz : classOf S n (v-g) = 0 := by
    rw [map_sub, hg, sub_self]
  have hb := (Submodule.Quotient.mk_eq_zero (complex S n).middleCoboundaryInCocycles).mp hz
  change v.1 - g.1 ∈ (complex S n).firstCoboundaryCheckCode.carrier at hb
  obtain ⟨f,hf⟩ := (BDL26RZCohomology.mem_boundary_iff (state S n).presentation _).mp hb
  refine ⟨f, ?_⟩
  funext q
  calc
    v.1 q = (v.1 q - g.1 q) + g.1 q := (sub_add_cancel _ _).symm
    _ = tannerCoboundary0 (state S n).presentation f q + g.1 q :=
      congrArg (fun a => a + g.1 q) (congrFun hf q).symm

theorem finrank_eq_one (S : OddScale) (n : Nat) : Module.finrank Field (H1 S n) = 1 := by
  rw [(finiteH1Equiv S n).finrank_eq]
  exact Module.finrank_self Field

/-- The classification on the exact existing indexed-family level carrier. -/
noncomputable def indexedEquiv (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    ((indexedFamily S depth).complex i).middleCohomology ≃ₗ[Field] Field :=
  finiteH1Equiv S i.val

/-- Both parities of the actual indexed step use the same selected edge. -/
noncomputable def indexedStepEquiv (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    ((indexedFamily S depth).complex i.castSucc).middleCohomology ≃ₗ[Field]
      ((indexedFamily S depth).complex i.succ).middleCohomology := stepEquiv S i.val

noncomputable def indexedStepCocycle (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier →ₗ[Field]
      ((indexedFamily S depth).complex i.succ).middleCocycleCode.carrier := stepCocycle S i.val

theorem indexedStepCocycle_value (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    (indexedStepCocycle S depth i w).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 w.1 := by
  rw [selectedMap_eq]
  rfl

theorem indexedStepEquiv_mk (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier) :
    indexedStepEquiv S depth i
      (((indexedFamily S depth).complex i.castSucc).middleCoboundaryInCocycles.mkQ w) =
      ((indexedFamily S depth).complex i.succ).middleCoboundaryInCocycles.mkQ
        (indexedStepCocycle S depth i w) := stepEquiv_mk S i.val w

theorem indexedEquiv_prefix_mk (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : Cocycle S 0) :
    indexedEquiv S depth i
      (((indexedFamily S depth).complex i).middleCoboundaryInCocycles.mkQ
        (prefixCocycle S i.val w)) = BDL26SeedCohomology.coefficient w.1 :=
  finiteH1Equiv_prefix_mk S i.val w

theorem indexed_left_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (v : ((indexedFamily S depth).complex i).middleCohomology) :
    (indexedEquiv S depth i).symm (indexedEquiv S depth i v) = v :=
  (indexedEquiv S depth i).symm_apply_apply v

theorem indexed_right_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    indexedEquiv S depth i ((indexedEquiv S depth i).symm c) = c :=
  (indexedEquiv S depth i).apply_symm_apply c

end QEC.Coding.BDL26FiniteCohomology
