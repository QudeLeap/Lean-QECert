import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformWeight

/-! # Global syndrome weight of the actual uniform input

The bound counts the actual successor qubit's Z neighbours. The RZ map embeds
these coordinates at distinct labelled roots, without a doubling factor.
-/
namespace QEC.Coding.BDL26UniformHistoryObstruction

open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

/-- A binary basis error has precisely its incident Z checks as syndrome support. -/
theorem basis_coboundary_support (P : TannerSquarePresentation) (q : P.Q) :
    hammingSupport (tannerCoboundary1 P (canonicalBasisWord q)) =
      Finset.univ.filter (fun z => P.qz q z = true) := by
  classical
  ext z
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    tannerCoboundary1_canonicalBasis_apply]
  by_cases h : P.qz q z = true <;> simp [h]

/-- This is a global column degree, including every Z neighbour. -/
theorem basis_coboundary_weight (P : TannerSquarePresentation) (q : P.Q) :
    HammingWeight (tannerCoboundary1 P (canonicalBasisWord q)) = qZDegree P q := by
  classical
  rw [HammingWeight, basis_coboundary_support]
  simp [qZDegree, Fintype.card_subtype]

/-- The actual lower syndrome counts the successor state's measured degree. -/
theorem lowerSyndrome_weight_eq (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val =
      qZDegree (state S (2 * j + 3)).presentation (lowerBasis S j) := by
  change HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
    ⟨2 * j + 3, by omega⟩ (lowerError S j)) = _
  rw [indexedFamily_coboundary1, lowerError_eq_basis]
  exact basis_coboundary_weight _ _

/-- Measured all-state valence bounds the actual lower syndrome uniformly. -/
theorem lowerSyndrome_weight_le_four (S : OddScale) (j : Nat) :
    HammingWeight (lowerSyndrome S j).val ≤ 4 := by
  rw [lowerSyndrome_weight_eq]
  exact ((state_boundedValence S (2 * j + 3)).2.2 (lowerBasis S j)).2.1

/-- Every RZ syndrome coordinate is sent to one distinct labelled root. -/
theorem rz_root_injective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) :
    Function.Injective (fun z : P.Z => (⟨z, rzMap1ZRoot P A z S⟩ : RZZ P S)) := by
  intro z w h
  exact congrArg Sigma.fst h

/-- RZ map2 support is exactly the injective image, not a replicated syndrome. -/
theorem rz_map2_support (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z) :
    hammingSupport (map2Coord P A S s) =
      (hammingSupport s).image (fun z => (⟨z, rzMap1ZRoot P A z S⟩ : RZZ P S)) := by
  classical
  ext p
  rcases p with ⟨z,v⟩
  constructor
  · intro hp
    have hn := (Finset.mem_filter.mp hp).2
    rw [rzMap2_apply] at hn
    by_cases hv : v = rzMap1ZRoot P A z S
    · subst v
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa using hn⟩, rfl⟩
    · simp [hv] at hn
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨w, hw, he⟩
    cases he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [rzMap2_apply] using (Finset.mem_filter.mp hw).2⟩

/-- RZ map2 preserves the global Hamming weight of every word. -/
theorem rz_map2_weight (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z) :
    HammingWeight (map2Coord P A S s) = HammingWeight s := by
  classical
  change (hammingSupport (map2Coord P A S s)).card = (hammingSupport s).card
  rw [rz_map2_support]
  exact Finset.card_image_of_injective _ (rz_root_injective P A S)

private theorem readout_weight_transport
    {I J K : Type} [iJ : Fintype J] [iK : Fintype K] (h : J = K)
    (F : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field J)
    (G : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field K)
    (hFG : HEq F G) (e : Word BDL26Field I) :
    HammingWeight (F e) = HammingWeight (G e) := by
  cases h
  cases Subsingleton.elim iJ iK
  cases hFG
  rfl

private theorem selected_rz_weight_transport
    (P U : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (h : U = rzReplacementPresentation P A.toTannerSquareAdmissible S)
    (F : Word BDL26Field P.Z →ₗ[BDL26Field] Word BDL26Field U.Z)
    (hF : HEq F (map2Coord P A S)) (s : Word BDL26Field P.Z) :
    HammingWeight (F s) = HammingWeight s := by
  exact (readout_weight_transport (K := RZZ P S)
    (congrArg TannerSquarePresentation.Z h) F (map2Coord P A S) hF s).trans
    (rz_map2_weight P A S s)

/-- The indexed canonical upper syndrome has exactly the lower word's weight. -/
theorem upperSyndrome_weight_eq (S : OddScale) (j : Nat) :
    HammingWeight (upperSyndrome S j).val = HammingWeight (lowerSyndrome S j).val := by
  change HammingWeight (((indexedDecoderData S (2 * j + 4)).selectedMap
    ⟨2 * j + 3, by omega⟩).map2 (lowerSyndrome S j).val) = _
  apply selected_rz_weight_transport _ _ (state S (2 * j + 3)).admissible S
  · change (nextState S (2 * j + 3) (state S (2 * j + 3))).presentation = _
    rw [nextState, if_neg (by omega)]
    rfl
  · exact (indexedDecoderData_selected_rz S (2 * j + 4)
      ⟨2 * j + 3, by omega⟩ (by simp)).2.2

/-- The uniform input's syndrome bound is independent of scale and depth. -/
theorem upperSyndrome_weight_le_four (S : OddScale) (j : Nat) :
    HammingWeight (upperSyndrome S j).val ≤ 4 := by
  rw [upperSyndrome_weight_eq]
  exact lowerSyndrome_weight_le_four S j


/-- Exact number of RX steps in the physical-C2 suffix of this even-depth input. -/
theorem uniform_rx_count (j : Nat) : ((2 * j + 2) + 1) / 2 = j + 1 := by omega

/-- Actual canonical selectors discharge every primitive alternating inequality. -/
theorem actualHistory_c2_weight (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    2 ^ ((n + 1) / 2) * HammingWeight
      (LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
        (BDL26OwnerIncidenceMasks.actualHistory S n sigma) ⟨2, by omega⟩) ≤
      HammingWeight sigma.val := by
  apply LevelTwoHistory.stoppedHistory_base_weight _
    (BDL26OwnerIncidenceMasks.actualAboveTwoSteps S n)
    (BDL26OwnerIncidenceMasks.actualBase S n)
  intro i s
  change (if i.val % 2 = 0 then
    2 * HammingWeight (BDL26OwnerIncidenceMasks.actualStep S (n + 2)
      (LevelTwoHistory.physicalStep i) s).coarse.val ≤ HammingWeight s.val
    else HammingWeight (BDL26OwnerIncidenceMasks.actualStep S (n + 2)
      (LevelTwoHistory.physicalStep i) s).coarse.val ≤ HammingWeight s.val)
  by_cases hp : i.val % 2 = 0
  · have hphys : (LevelTwoHistory.physicalStep i).val % 2 = 0 := by
      simpa [LevelTwoHistory.physicalStep, Nat.add_mod] using hp
    rw [if_pos hp, BDL26OwnerIncidenceMasks.actualStep_rx S (n + 2)
      (LevelTwoHistory.physicalStep i) hphys]
    exact BDL26RXDecoderAdapter.rxStepOutput_weight S (n + 2)
      (LevelTwoHistory.physicalStep i) hphys s
  · have hphys : ¬(LevelTwoHistory.physicalStep i).val % 2 = 0 := by
      simpa [LevelTwoHistory.physicalStep, Nat.add_mod] using hp
    rw [if_neg hp, BDL26OwnerIncidenceMasks.actualStep_rz S (n + 2)
      (LevelTwoHistory.physicalStep i) hphys]
    exact BDL26RZDecoderAdapter.rzStepOutput_weight S (n + 2)
      (LevelTwoHistory.physicalStep i) hphys s

/-- The weight contraction is on the literal C2 readout of the uniform history. -/
theorem uniform_c2_weight (S : OddScale) (j : Nat) :
    2 ^ (j + 1) * HammingWeight
      (LevelTwoHistory.syndromeReadout (indexedDecoderData S (2 * j + 4))
        (BDL26OwnerIncidenceMasks.actualHistory S (2 * j + 2) (upperSyndrome S j))
        ⟨2, by omega⟩) ≤ HammingWeight (upperSyndrome S j).val := by
  simpa only [uniform_rx_count] using
    actualHistory_c2_weight S (2 * j + 2) (upperSyndrome S j)

/-- Three or more RX steps force the actual terminal syndrome word to vanish. -/
theorem uniform_c2_readout_zero (S : OddScale) (j : Nat) (hj : 2 ≤ j) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (2 * j + 4))
      (BDL26OwnerIncidenceMasks.actualHistory S (2 * j + 2) (upperSyndrome S j))
      ⟨2, by omega⟩ = 0 := by
  apply (HammingWeight_eq_zero_iff _).mp
  have hw := (uniform_c2_weight S j).trans (upperSyndrome_weight_le_four S j)
  have hp : (2 : Nat) ^ 3 ≤ 2 ^ (j + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  nlinarith

end QEC.Coding.BDL26UniformHistoryObstruction
