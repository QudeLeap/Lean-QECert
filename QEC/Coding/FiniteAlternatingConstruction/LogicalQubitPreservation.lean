import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.LogicalDimension

/-!
# Pure-X logical classes of the actual alternating family

[BDL26, Section 3, replacement lemmas and Theorem main, item (2)].
The source-even conclusion uses the actual seed, the selected RX/RZ cochain
maps and the existing complex QubitRegister CSS code. Every-prefix quotient
formulas are an internal strengthening. Public release is a separate gate.
-/

noncomputable section
namespace QEC.Coding.BDL26LogicalQubitPreservation

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical

abbrev Field := ZMod 2
noncomputable abbrev complex := BDL26FiniteCohomology.complex
noncomputable abbrev DualRepresentative (S : OddScale) (n : Nat) :=
  (complex S n).middleBoundaryCode.dual.carrier
noncomputable abbrev LogicalQuotient (S : OddScale) (n : Nat) :=
  (complex S n).pureXLogicalQuotient

/-- The actual pure-X quotient class, retaining the complete coboundary code. -/
noncomputable abbrev logicalClass (S : OddScale) (n : Nat) :
    DualRepresentative S n →ₗ[Field] LogicalQuotient S n :=
  (complex S n).firstCoboundaryInMiddleBoundaryDual.mkQ

/-- The proved M3 identity-on-words adapter, with the actual finite carrier. -/
noncomputable abbrev cocycleEquiv (S : OddScale) (n : Nat) :
    DualRepresentative S n ≃ₗ[Field] BDL26FiniteCohomology.Cocycle S n :=
  (complex S n).middleBoundaryDualEquivMiddleCocycleCode

theorem cocycleEquiv_word (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    (cocycleEquiv S n w).1 = w.1 := by
  simp only [cocycleEquiv, ChainComplexData.middleBoundaryDualEquivMiddleCocycleCode,
    LinearEquiv.coe_ofEq_apply]

theorem cocycleEquiv_symm_word (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S n) :
    ((cocycleEquiv S n).symm w).1 = w.1 := by
  have h := cocycleEquiv_word S n ((cocycleEquiv S n).symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The existing pure-X semantics, specialized to the literal presentation. -/
noncomputable abbrev logicalToH1 (S : OddScale) (n : Nat) :
    LogicalQuotient S n ≃ₗ[Field] BDL26FiniteCohomology.H1 S n :=
  (complex S n).pureXLogicalQuotientEquivMiddleCohomology

theorem logicalToH1_mk (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalToH1 S n (logicalClass S n w) =
      BDL26FiniteCohomology.classOf S n (cocycleEquiv S n w) :=
  (complex S n).pureXLogicalQuotientEquivMiddleCohomology_mk w

/-- No isomorphism is assumed: both composed equivalences are already proved. -/
noncomputable def logicalEquiv (S : OddScale) (n : Nat) :
    LogicalQuotient S n ≃ₗ[Field] Field :=
  (logicalToH1 S n).trans (BDL26FiniteCohomology.finiteH1Equiv S n)

theorem logicalEquiv_mk (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalEquiv S n (logicalClass S n w) =
      BDL26FiniteCohomology.finiteH1Equiv S n
        (BDL26FiniteCohomology.classOf S n (cocycleEquiv S n w)) := by
  change BDL26FiniteCohomology.finiteH1Equiv S n
    (logicalToH1 S n (logicalClass S n w)) = _
  rw [logicalToH1_mk]

theorem logical_left_inverse (S : OddScale) (n : Nat) (v : LogicalQuotient S n) :
    (logicalEquiv S n).symm (logicalEquiv S n v) = v :=
  (logicalEquiv S n).symm_apply_apply v

theorem logical_right_inverse (S : OddScale) (n : Nat) (c : Field) :
    logicalEquiv S n ((logicalEquiv S n).symm c) = c :=
  (logicalEquiv S n).apply_symm_apply c

/-- Equality is exactly a full-word actual coboundary, on arbitrary representatives. -/
theorem logicalClass_eq_iff_boundary (S : OddScale) (n : Nat)
    (u v : DualRepresentative S n) :
    logicalClass S n u = logicalClass S n v ↔
      ∃ f : Word Field (state S n).presentation.X,
        tannerCoboundary0 (state S n).presentation f = fun q => u.1 q - v.1 q := by
  constructor
  · intro h
    have hb := (Submodule.Quotient.eq
      (complex S n).firstCoboundaryInMiddleBoundaryDual).mp h
    change (fun q => u.1 q - v.1 q) ∈ (complex S n).firstCoboundaryCheckCode.carrier at hb
    exact (BDL26RZCohomology.mem_boundary_iff (state S n).presentation _).mp hb
  · intro h
    have hb := (BDL26RZCohomology.mem_boundary_iff (state S n).presentation _).mpr h
    apply (Submodule.Quotient.eq (complex S n).firstCoboundaryInMiddleBoundaryDual).mpr
    exact hb

theorem logicalEquiv_eq_iff_boundary (S : OddScale) (n : Nat)
    (u v : DualRepresentative S n) :
    logicalEquiv S n (logicalClass S n u) = logicalEquiv S n (logicalClass S n v) ↔
      ∃ f : Word Field (state S n).presentation.X,
        tannerCoboundary0 (state S n).presentation f = fun q => u.1 q - v.1 q := by
  constructor
  · intro h
    exact (logicalClass_eq_iff_boundary S n u v).mp ((logicalEquiv S n).injective h)
  · intro h
    exact congrArg (logicalEquiv S n) ((logicalClass_eq_iff_boundary S n u v).mpr h)

/-- Transport an arbitrary actual seed cocycle through the literal selected prefix. -/
noncomputable def prefixRepresentative (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) : DualRepresentative S n :=
  (cocycleEquiv S n).symm (BDL26FiniteCohomology.prefixCocycle S n w)

theorem prefixRepresentative_word (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    (prefixRepresentative S n w).1 = BDL26AlternatingCochain.map1 S n w.1 :=
  cocycleEquiv_symm_word S n (BDL26FiniteCohomology.prefixCocycle S n w)

theorem logicalEquiv_prefix_mk (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    logicalEquiv S n (logicalClass S n (prefixRepresentative S n w)) =
      BDL26SeedCohomology.coefficient w.1 := by
  rw [logicalEquiv_mk]
  change BDL26FiniteCohomology.finiteH1Equiv S n
    (BDL26FiniteCohomology.classOf S n
      (cocycleEquiv S n ((cocycleEquiv S n).symm
        (BDL26FiniteCohomology.prefixCocycle S n w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact BDL26FiniteCohomology.finiteH1Equiv_prefix_mk S n w

/-- The inverse scalar is the complete selected-prefix seed representative. -/
theorem logicalEquiv_symm_scalar (S : OddScale) (n : Nat) (c : Field) :
    (logicalEquiv S n).symm c = logicalClass S n
      (prefixRepresentative S n (c • BDL26SeedCohomology.seedElement)) := by
  apply (logicalToH1 S n).injective
  change logicalToH1 S n ((logicalToH1 S n).symm
    ((BDL26FiniteCohomology.finiteH1Equiv S n).symm c)) = _
  rw [LinearEquiv.apply_symm_apply, BDL26FiniteCohomology.finiteH1Equiv_symm_scalar,
    logicalToH1_mk]
  congr 1

theorem logical_class_normal_form (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalClass S n w = logicalClass S n (prefixRepresentative S n
      (logicalEquiv S n (logicalClass S n w) • BDL26SeedCohomology.seedElement)) := by
  rw [← logicalEquiv_symm_scalar]
  exact ((logicalEquiv S n).symm_apply_apply (logicalClass S n w)).symm

/-- Actual adjacent quotient equivalence, with the proved selected RX/RZ edge. -/
noncomputable def logicalStepEquiv (S : OddScale) (n : Nat) :
    LogicalQuotient S n ≃ₗ[Field] LogicalQuotient S (n+1) :=
  ((logicalToH1 S n).trans (BDL26FiniteCohomology.stepEquiv S n)).trans
    (logicalToH1 S (n+1)).symm

noncomputable def stepRepresentative (S : OddScale) (n : Nat)
    (w : DualRepresentative S n) : DualRepresentative S (n+1) :=
  (cocycleEquiv S (n+1)).symm
    (BDL26FiniteCohomology.stepCocycle S n (cocycleEquiv S n w))

theorem stepRepresentative_word (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    (stepRepresentative S n w).1 = BDL26AlternatingCochain.stepMap1 S n w.1 := by
  rw [stepRepresentative, cocycleEquiv_symm_word,
    BDL26FiniteCohomology.stepCocycle_value, cocycleEquiv_word]

theorem logicalStepEquiv_mk (S : OddScale) (n : Nat) (w : DualRepresentative S n) :
    logicalStepEquiv S n (logicalClass S n w) =
      logicalClass S (n+1) (stepRepresentative S n w) := by
  apply (logicalToH1 S (n+1)).injective
  change logicalToH1 S (n+1) ((logicalToH1 S (n+1)).symm
    (BDL26FiniteCohomology.stepEquiv S n
      (logicalToH1 S n (logicalClass S n w)))) = _
  rw [LinearEquiv.apply_symm_apply, logicalToH1_mk, BDL26FiniteCohomology.stepEquiv_mk,
    logicalToH1_mk]
  congr 1

/-- Both indexed parities use the existing family's actual pure-X quotient. -/
noncomputable def indexedLogicalEquiv (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    ((indexedFamily S depth).complex i).pureXLogicalQuotient ≃ₗ[Field] Field :=
  logicalEquiv S i.val

theorem indexedLogicalEquiv_mk (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : ((indexedFamily S depth).complex i).middleBoundaryCode.dual.carrier) :
    indexedLogicalEquiv S depth i
      (((indexedFamily S depth).complex i).firstCoboundaryInMiddleBoundaryDual.mkQ w) =
      BDL26FiniteCohomology.indexedEquiv S depth i
        (((indexedFamily S depth).complex i).middleCoboundaryInCocycles.mkQ
          (cocycleEquiv S i.val w)) := logicalEquiv_mk S i.val w

theorem indexed_left_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : ((indexedFamily S depth).complex i).pureXLogicalQuotient) :
    (indexedLogicalEquiv S depth i).symm (indexedLogicalEquiv S depth i w) = w :=
  (indexedLogicalEquiv S depth i).symm_apply_apply w

theorem indexed_right_inverse (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    indexedLogicalEquiv S depth i ((indexedLogicalEquiv S depth i).symm c) = c :=
  (indexedLogicalEquiv S depth i).apply_symm_apply c

theorem indexed_prefix_mk (S : OddScale) (depth : Nat) (i : LevelIndex depth)
    (w : BDL26FiniteCohomology.Cocycle S 0) :
    indexedLogicalEquiv S depth i
      (logicalClass S i.val (prefixRepresentative S i.val w)) =
      BDL26SeedCohomology.coefficient w.1 := logicalEquiv_prefix_mk S i.val w

theorem indexed_symm_scalar (S : OddScale) (depth : Nat) (i : LevelIndex depth) (c : Field) :
    (indexedLogicalEquiv S depth i).symm c = logicalClass S i.val
      (prefixRepresentative S i.val (c • BDL26SeedCohomology.seedElement)) :=
  logicalEquiv_symm_scalar S i.val c

noncomputable def indexedLogicalStepEquiv (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    ((indexedFamily S depth).complex i.castSucc).pureXLogicalQuotient ≃ₗ[Field]
      ((indexedFamily S depth).complex i.succ).pureXLogicalQuotient :=
  logicalStepEquiv S i.val

theorem indexed_step_mk (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleBoundaryCode.dual.carrier) :
    indexedLogicalStepEquiv S depth i (logicalClass S i.val w) =
      logicalClass S (i.val+1) (stepRepresentative S i.val w) :=
  logicalStepEquiv_mk S i.val w

theorem indexed_step_word (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (w : ((indexedFamily S depth).complex i.castSucc).middleBoundaryCode.dual.carrier) :
    (stepRepresentative S i.val w).1 =
      ((indexedDecoderData S depth).selectedMap i).map1 w.1 := by
  rw [selectedMap_eq]
  exact stepRepresentative_word S i.val w

/-- The literal source seed retains its two/five/two coordinate spaces. -/
theorem source_seed_coordinates (S : OddScale) :
    Fintype.card (state S 0).presentation.X = 2 ∧
      Fintype.card (state S 0).presentation.Q = 5 ∧
      Fintype.card (state S 0).presentation.Z = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      (@Fintype.card_congr (state S 0).presentation.X (Fin 2) _ _ (Equiv.refl _))
  · simpa only [Fintype.card_fin] using
      (@Fintype.card_congr (state S 0).presentation.Q (Fin 5) _ _ (Equiv.refl _))
  · simpa only [Fintype.card_fin] using
      (@Fintype.card_congr (state S 0).presentation.Z (Fin 2) _ _ (Equiv.refl _))

/-- Source-even one-qubit assembly: semantic H1 and actual complex CSS code.
This internal theorem does not alter the public node's release state. -/
theorem source_even_one_logical_qubit (S : OddScale) (k : Nat) :
    Nonempty ((complex S (2*k)).middleCohomology ≃ₗ[Field] Field) ∧
      Module.finrank ℂ (BDL26CSSHamiltonian.labelledCode S (2*k)).carrier = 2 ∧
      (BDL26CSSHamiltonian.labelledCode S (2*k)).dimension = 2 ∧
      Fintype.card (BDL26CSSHamiltonian.Physical S (2*k)) -
        CSSGibbs.checkRank (BDL26CSSHamiltonian.zSyndrome S (2*k)) -
        CSSGibbs.checkRank (BDL26CSSHamiltonian.xSyndrome S (2*k)) = 1 :=
  ⟨⟨BDL26FiniteCohomology.finiteH1Equiv S (2*k)⟩,
    BDL26CSSHamiltonian.labelled_code_carrier_finrank_two S (2*k),
    BDL26CSSHamiltonian.even_code_dimension_two S k,
    BDL26CSSHamiltonian.even_binary_logical_exponent_one S k⟩

end QEC.Coding.BDL26LogicalQubitPreservation
