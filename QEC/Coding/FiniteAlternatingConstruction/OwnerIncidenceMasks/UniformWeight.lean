import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformWitness

/-! # Measured support bound for the explicit upper error -/
namespace QEC.Coding.BDL26UniformHistoryObstruction

open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

private theorem weight_single_one {I : Type} [Fintype I] (i : I) :
    HammingWeight (Pi.single i (1 : BDL26Field)) = 1 := by
  classical
  have hs : hammingSupport (Pi.single i (1 : BDL26Field)) = {i} := by
    ext j
    by_cases h : j = i
    · subst j; simp [hammingSupport]
    · simp [hammingSupport, Pi.single_apply, h]
  rw [HammingWeight, hs, Finset.card_singleton]

private theorem weight_basis {I : Type} [Fintype I] (i : I) :
    HammingWeight (canonicalBasisWord (F := BDL26Field) i) = 1 :=
  weight_single_one i

private theorem extendZEdgeWord_weight_le (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (e : Word BDL26Field (ZDoubleCylinderEdge P z S)) :
    HammingWeight (extendZEdgeWord P S z e) ≤ HammingWeight e := by
  classical
  let f : ZDoubleCylinderEdge P z S → RZQ P S := fun a => .inl ⟨z,a⟩
  have hs : hammingSupport (extendZEdgeWord P S z e) ⊆ (hammingSupport e).image f := by
    intro q hq
    have hn := (Finset.mem_filter.mp hq).2
    rcases q with ⟨w,a⟩ | ⟨q,v⟩
    · by_cases hw : w = z
      · subst w
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa [extendZEdgeWord] using hn⟩, rfl⟩
      · exact (hn (by simp [extendZEdgeWord, hw])).elim
    · exact (hn rfl).elim
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

private theorem weight_twoSelect_le {I : Type} [Fintype I]
    (a b : Word BDL26Field I) (side : BDL26FiniteTannerSquare.Two) (m : Nat)
    (ha : HammingWeight a ≤ m) (hb : HammingWeight b ≤ m) :
    HammingWeight (BDL26RZLocalReplacement.twoSelect a b side) ≤ m := by
  fin_cases side
  · exact ha
  · exact hb

private theorem connector_weight_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (q : P.Q) (z : P.Z) (h : P.qz q z = true) :
    HammingWeight (rzMap1Connector P A q z h S) ≤ S.half := by
  rw [rzMap1Connector_eq_outerSide]
  unfold rzMap1ConnectorOuterSide
  apply weight_twoSelect_le
  · refine (HammingWeight_univ_sum_le _).trans ?_
    simp only [weight_basis, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, le_refl]
  · refine (HammingWeight_univ_sum_le _).trans ?_
    simp only [weight_basis, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, le_refl]

noncomputable def lowerBasisRaw (S : OddScale) (n : Nat) : RX1 (state S n).presentation S :=
  .inl ⟨retainedX S n, .inl (0, .inl
    (radialEdge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) (faceNeighbor (state S n).presentation (retainedX S n)
        (retainedStarFace S n) 0), rxRadialGridZero S))⟩

private theorem retained_radialGauge_single (S : OddScale) (n : Nat) :
    radialGauge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) S 0 (retainedAlpha S n) =
    Pi.single (.inl (0, .inl
      (radialEdge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
        (retainedX S n) (faceNeighbor (state S n).presentation (retainedX S n)
          (retainedStarFace S n) 0), rxRadialGridZero S))) 1 := by
  classical
  unfold radialGauge
  rw [Finset.sum_eq_single (faceNeighbor (state S n).presentation (retainedX S n)
    (retainedStarFace S n) 0)]
  · simp [retainedAlpha]
  · intro q _ hq
    simp [retainedAlpha, hq]
  · simp

theorem lowerErrorRaw_eq_basis (S : OddScale) (n : Nat) :
    lowerErrorRaw S n = canonicalBasisWord (lowerBasisRaw S n) := by
  classical
  unfold lowerErrorRaw
  rw [retained_radialGauge_single]
  funext target
  rcases target with ⟨x,e⟩ | ⟨q,e⟩
  · by_cases hx : x = retainedX S n
    · subst x
      simp [extendXCorrection, canonicalBasisWord, lowerBasisRaw, Pi.single_apply]
    · simp [extendXCorrection, hx, canonicalBasisWord, lowerBasisRaw, Pi.single_apply,
        Sigma.mk.inj_iff, hx]
  · simp [extendXCorrection, canonicalBasisWord, lowerBasisRaw, Pi.single_apply]

theorem lowerErrorRaw_weight (S : OddScale) (n : Nat) :
    HammingWeight (lowerErrorRaw S n) = 1 := by
  rw [lowerErrorRaw_eq_basis]
  exact weight_basis _

private theorem weight_transport (P U : TannerSquarePresentation) (h : P = U)
    (e : Word BDL26Field U.Q) :
    HammingWeight (Eq.mpr
      (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h) e) =
      HammingWeight e := by
  cases h
  rfl

theorem lowerError_weight (S : OddScale) (j : Nat) :
    HammingWeight (lowerError S j) = 1 := by
  have h := weight_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega)))
    (lowerErrorRaw S (2 * j + 2))
  exact h.trans (lowerErrorRaw_weight S (2 * j + 2))

/-- Each actual incident Z block contributes at most one half-scale path. -/
theorem map1_basis_weight_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (q : P.Q) :
    HammingWeight (map1Coord P A S (canonicalBasisWord q)) ≤
      1 + qZDegree P q * S.half := by
  classical
  rw [map1Coord_canonicalBasis]
  unfold map1BasisImage
  refine (HammingWeight_add_le _ _).trans ?_
  rw [weight_single_one]
  apply Nat.add_le_add_left
  refine (HammingWeight_univ_sum_le _).trans ?_
  calc
    _ ≤ ∑ z : P.Z, if P.qz q z = true then S.half else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with h
      · exact (extendZEdgeWord_weight_le P S z _).trans (connector_weight_le P A S q z h)
      · simp only [HammingWeight_zero, le_refl]
    _ = qZDegree P q * S.half := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, smul_eq_mul, qZDegree, Fintype.card_subtype]

noncomputable def lowerBasis (S : OddScale) (j : Nat) :
    (state S ((2 * j + 2) + 1)).presentation.Q :=
  Eq.mpr (congrArg (fun C : ConstructionState => C.presentation.Q)
    (state_rx S (2 * j + 2) (by omega))) (lowerBasisRaw S (2 * j + 2))

private theorem basis_transport (P U : TannerSquarePresentation) (h : P = U) (q : U.Q) :
    Eq.mpr (congrArg (fun T : TannerSquarePresentation => Word BDL26Field T.Q) h)
      (canonicalBasisWord q) =
    canonicalBasisWord (Eq.mpr (congrArg TannerSquarePresentation.Q h) q) := by
  cases h
  rfl

theorem lowerError_eq_basis (S : OddScale) (j : Nat) :
    lowerError S j = canonicalBasisWord (lowerBasis S j) := by
  unfold lowerError
  rw [lowerErrorRaw_eq_basis]
  exact basis_transport _ _
    (congrArg ConstructionState.presentation (state_rx S (2 * j + 2) (by omega))) _

private theorem weight_linear_apply_transport
    {I J K : Type} [iJ : Fintype J] [iK : Fintype K] (h : J = K)
    (F : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field J)
    (G : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field K)
    (hFG : HEq F G) (e : Word BDL26Field I) :
    HammingWeight (F e) = HammingWeight (G e) := by
  cases h
  cases Subsingleton.elim iJ iK
  cases hFG
  rfl

private theorem selected_basis_weight_transport
    (P U : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P) (S : OddScale)
    (h : U = rzReplacementPresentation P A.toTannerSquareAdmissible S)
    (F : Word BDL26Field P.Q →ₗ[BDL26Field] Word BDL26Field U.Q)
    (hF : HEq F (map1Coord P A S)) (q : P.Q) :
    HammingWeight (F (canonicalBasisWord q)) ≤ 1 + qZDegree P q * S.half := by
  have hw := weight_linear_apply_transport (K := RZQ P S)
    (congrArg TannerSquarePresentation.Q h) F (map1Coord P A S) hF (canonicalBasisWord q)
  exact hw.trans_le (map1_basis_weight_le P A S q)

theorem upperError_weight_le (S : OddScale) (j : Nat) :
    HammingWeight (upperError S j) ≤
      1 + qZDegree (state S (2 * j + 3)).presentation (lowerBasis S j) * S.half := by
  unfold upperError
  rw [lowerError_eq_basis]
  apply selected_basis_weight_transport _ _ (state S (2 * j + 3)).admissible S
  · change (nextState S (2 * j + 3) (state S (2 * j + 3))).presentation = _
    rw [nextState, if_neg (by omega)]
    rfl
  · exact (indexedDecoderData_selected_rz S (2 * j + 4)
      ⟨2 * j + 3, by omega⟩ (by simp)).2.1

/-- A measured actual incidence bound gives a depth-independent upper error budget. -/
theorem upperError_weight_uniform (S : OddScale) (j : Nat) :
    HammingWeight (upperError S j) ≤ 2 * S.ell - 1 := by
  have hd := (state_boundedValence S (2 * j + 3)).2.2 (lowerBasis S j)
  have hm := Nat.mul_le_mul_right S.half hd.2.1
  have he := S.two_half_add_one
  have hw := upperError_weight_le S j
  omega

end QEC.Coding.BDL26UniformHistoryObstruction
