import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformWitness
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformRXTail.Input

/-! # Actual top and unparented local-Z consumers

These consume the complete canonical construction on the merged actual
uniform inputs. They do not alter the existing all-component obstruction.
-/
namespace QEC.Coding.BDL26CanonicalHistoryMarks

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

/-- An actual positive-dimensional seed RX face, as a G2 Z-labelled node. -/
noncomputable def localZ (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) : GraphVertex S 2 :=
  Vertex.z (.inl (.inl ⟨x, f⟩))

theorem localZ_unparented (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    parent S 1 (localZ S x f) = none := rfl

/-- The actual RZ root coordinate above this local-Z owner. -/
noncomputable def localZCoordinate (S : OddScale) (n : Nat) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    FamilyZ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) :=
  ⟨.inl (.inl ⟨x, f⟩), BDL26RZMap1CoordinateBridge.rzMap1ZRoot
    (state S 1).presentation (state S 1).admissible (.inl (.inl ⟨x, f⟩)) S⟩

theorem localZCoordinate_owner (S : OddScale) (n : Nat) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    baseSyndromeOwner S n (localZCoordinate S n x f) = localZ S x f := rfl

/-- The guard concerns the real base snapshot of a literal valid actual input;
its owner is intrinsically unparented even when that guard marks it. -/
theorem localZ_actual_guard (S : OddScale) (n : Nat) (sigma : Input S n) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S)
    (h : (baseInput S n sigma).val (localZCoordinate S n x f) ≠ 0) :
    physicalNode S n 0 (localZ S x f) ∈ marks S n sigma ∧
      parent S 1 (localZ S x f) = none := by
  have hm := unparented_base_syndrome_guard S n sigma (localZ S x f)
    (localZ_unparented S x f) (localZCoordinate S n x f)
    (localZCoordinate_owner S n x f) h
  exact ⟨(mem_marks_physical S n sigma 0 _).mpr hm.1, hm.2⟩

/-- A literal valid C1 syndrome from the actual retained seed face. -/
noncomputable def localZWitnessLower (S : OddScale) :
    (indexedFamily S 2).Syndrome (1 : LevelIndex 2) :=
  ⟨(indexedFamily S 2).coboundary1 1
    (BDL26UniformHistoryObstruction.lowerErrorRaw S 0),
    ⟨BDL26UniformHistoryObstruction.lowerErrorRaw S 0, rfl⟩⟩

theorem localZWitnessLower_val (S : OddScale) : (localZWitnessLower S).val =
    BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 := by
  change (indexedFamily S 2).coboundary1 1 _ = _
  rw [indexedFamily_coboundary1]
  rfl

/-- Its image is a genuine valid C2 syndrome, used at physical depth two. -/
noncomputable def localZWitnessInput (S : OddScale) : Input S 0 :=
  BDL26RZDecoderAdapter.embeddedSyndrome S 2 (1 : StepIndex 2) (localZWitnessLower S)

theorem localZWitnessInput_coordinate (S : OddScale) (x : BaseX)
    (f : DoubleCylinderFace baseTannerSquarePresentation x S) :
    (localZWitnessInput S).val (localZCoordinate S 0 x f) =
      BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 (.inl (.inl ⟨x, f⟩)) := by
  change ((indexedDecoderData S 2).selectedMap (1 : StepIndex 2)).map2
    (localZWitnessLower S).val (localZCoordinate S 0 x f) = _
  have hm := (indexedDecoderData_selected_rz S 2 (1 : StepIndex 2) (by decide)).2.2
  have he := eq_of_heq hm
  rw [he, localZWitnessLower_val]
  exact (BDL26OwnerParentObstruction.rzMap2_apply (state S 1).presentation
    (state S 1).admissible S (BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0)
    (.inl (.inl ⟨x, f⟩))
    (BDL26RZMap1CoordinateBridge.rzMap1ZRoot (state S 1).presentation
      (state S 1).admissible (.inl (.inl ⟨x, f⟩)) S)).trans (if_pos rfl)

/-- Nonvacuous actual witness: an unparented G2 local-Z is genuinely marked.
It is not asserted to belong to the root component. -/
theorem localZWitness_marked (S : OddScale) :
    ∃ (x : BaseX) (f : DoubleCylinderFace baseTannerSquarePresentation x S),
      physicalNode S 0 0 (localZ S x f) ∈ marks S 0 (localZWitnessInput S) ∧
        parent S 1 (localZ S x f) = none := by
  let x : BaseX := BDL26UniformHistoryObstruction.retainedX S 0
  let origin : Fin S.half := ⟨0, S.half_pos⟩
  let f : DoubleCylinderFace baseTannerSquarePresentation x S :=
    .inl (0, BDL26UniformHistoryObstruction.retainedStarFace S 0, origin, origin)
  have hi : BDL26UniformRXTail.incidentStarFace S 0
      (BDL26UniformHistoryObstruction.retainedStarFace S 0) := Or.inl rfl
  have hl : BDL26UniformHistoryObstruction.lowerSyndromeRaw S 0 (.inl (.inl ⟨x, f⟩)) = 1 := by
    exact (BDL26UniformRXTail.lower_input_layer S 0
      (BDL26UniformHistoryObstruction.retainedStarFace S 0) 0 origin origin).trans
      (if_pos ⟨rfl, rfl, rfl, hi⟩)
  have hc : (localZWitnessInput S).val (localZCoordinate S 0 x f) ≠ 0 := by
    rw [localZWitnessInput_coordinate, hl]
    exact one_ne_zero
  have hb : (baseInput S 0 (localZWitnessInput S)).val (localZCoordinate S 0 x f) ≠ 0 := by
    rw [baseInput_depthTwo]
    exact hc
  have hactual : physicalNode S 0 0 (localZ S x f) ∈ marks S 0 (localZWitnessInput S) ∧
      parent S 1 (localZ S x f) = none :=
    localZ_actual_guard S 0 (localZWitnessInput S) x f hb
  exact ⟨x, f, hactual⟩

theorem uniform_outputAt_top (S : OddScale) (j : Nat) :
    outputAt S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1)) = BDL26UniformHistoryObstruction.topOutput S j :=
  outputAt_top S (2 * j + 1) _

/-- The complete owner function at an actual input, with its input-dependent
finite index domain. The input is a parameter, not a captured history expression. -/
private noncomputable def ownersAtInput (S : OddScale) (n : Nat) (i : StepIndex n)
    (s : (Data S n).family.Syndrome i.succ) :
    Fin (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) s).localComponents.length →
      GraphVertex S (i.val + 3) :=
  fun a => if h : (LevelTwoHistory.physicalStep i).val % 2 = 0 then
    BDL26RXDecoderAdapter.vertexEquiv (state S (i.val + 2)).presentation
      (BDL26RXDecoderAdapter.componentOwner S (n + 2) (LevelTwoHistory.physicalStep i) h s
        ⟨a.val, by simpa only [actualStep_rx S (n + 2) (LevelTwoHistory.physicalStep i) h]
          using a.isLt⟩)
  else Vertex.z
    (BDL26RZDecoderAdapter.componentOwner S (n + 2) (LevelTwoHistory.physicalStep i) h s
      ⟨a.val, by simpa only [actualStep_rz S (n + 2) (LevelTwoHistory.physicalStep i) h]
        using a.isLt⟩)

private theorem pieceOwner_at_input (S : OddScale) (n : Nat) (sigma : Input S n)
    (i : StepIndex n) : HEq (pieceOwner S n sigma i)
      (ownersAtInput S n i (inputAt S n sigma i.succ)) := HEq.rfl

/-- Dependent ordered-piece labels are transported with the actual output
record, rather than identifying separately expanded list-length expressions. -/
private theorem outputMarks_congr
    {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
    {V : Type} [Fintype V] [DecidableEq V]
    {O P : AssemblyStepOutput D i} {s t : C2 i.succ → V}
    {a : Fin O.localComponents.length → V} {b : Fin P.localComponents.length → V}
    (hO : O = P) (hs : s = t) (hp : HEq a b) :
    outputMarks O s a = outputMarks P t b := by
  cases hO
  cases hs
  cases eq_of_heq hp
  rfl

/-- Exact equality with the merged uniform input's original top-output marks. -/
theorem uniform_topMarks (S : OddScale) (j : Nat) :
    aboveMarks S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1)) = BDL26UniformHistoryObstruction.topMarks S j := by
  have ho := uniform_outputAt_top S j
  have hi := outputAt_input S (2 * j + 2)
    (BDL26UniformHistoryObstruction.upperSyndrome S j) (Fin.last (2 * j + 1))
  rw [ho] at hi
  have hu := (actualStep_relation S (2 * j + 4) ⟨2 * j + 3, by omega⟩).input_eq
    (BDL26UniformHistoryObstruction.upperSyndrome S j)
  change (BDL26UniformHistoryObstruction.topOutput S j).input = _ at hu
  have hs : inputAt S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1)).succ = BDL26UniformHistoryObstruction.upperSyndrome S j :=
    hi.symm.trans hu
  have hodd : ¬(LevelTwoHistory.physicalStep (Fin.last (2 * j + 1))).val % 2 = 0 := by
    simp only [LevelTwoHistory.physicalStep_val, Fin.val_last]
    omega
  have hsyn : syndromeOwner S (2 * j + 2) (Fin.last (2 * j + 1)) =
      BDL26UniformHistoryObstruction.topOwner S j := dif_neg hodd
  have hfamily : HEq
      (ownersAtInput S (2 * j + 2) (Fin.last (2 * j + 1))
        (inputAt S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
          (Fin.last (2 * j + 1)).succ))
      (ownersAtInput S (2 * j + 2) (Fin.last (2 * j + 1))
        (BDL26UniformHistoryObstruction.upperSyndrome S j)) :=
    congr_arg_heq (ownersAtInput S (2 * j + 2) (Fin.last (2 * j + 1))) hs
  have htop : HEq
      (ownersAtInput S (2 * j + 2) (Fin.last (2 * j + 1))
        (BDL26UniformHistoryObstruction.upperSyndrome S j))
      (BDL26UniformHistoryObstruction.topComponentOwner S j) := by
    apply Function.hfunext rfl
    intro a b hab
    have he : a = b := eq_of_heq hab
    subst b
    exact heq_of_eq (dif_neg hodd)
  have hpiece : HEq
      (pieceOwner S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
        (Fin.last (2 * j + 1)))
      (BDL26UniformHistoryObstruction.topComponentOwner S j) :=
    (pieceOwner_at_input S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1))).trans (hfamily.trans htop)
  exact outputMarks_congr ho hsyn hpiece

end QEC.Coding.BDL26CanonicalHistoryMarks
