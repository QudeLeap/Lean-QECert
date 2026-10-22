import QEC.Coding.QuantumTanner.LiftedProductTannerBridge

/-!
# The four-part bridge as public Quantum Tanner construction data

The four labelled vertex parts of LZDec22 are packaged using the doubled
vertex group `G × C₂`. Left generators carry the nontrivial `C₂` flag and
right generators the trivial flag. Thus total no-conjugacy for this cover
is proved by the flags, rather than assumed of the original group.

The existing Quantum Tanner API uses Z on its `false` side and X on its
`true` side. Here the false side consists of source parts `10,01`, while
the true side consists of `00,11`. The selected second-boundary family is
Z and the transposed first-boundary family is X. This explicitly records
the Pauli naming and vertex-part convention of the fifth owner receipt.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LiftedProductTannerCode

open Classical LiftedProductTannerBridge LiftedProductTensorBridge
open LiftedProductActionBridge LiftedProductRestriction

abbrev Flag := Multiplicative (ZMod 2)
abbrev VertexGroup (G : Type) := G × Flag

def oddFlag : Flag := Multiplicative.ofAdd 1

def leftFlag (k : Flag) : Bool := decide (k = oddFlag)

def rightFlag (k : Flag) (side : Bool) : Bool :=
  if side then leftFlag k else !(leftFlag k)

@[simp] theorem leftFlag_one : leftFlag 1 = false := by decide
@[simp] theorem leftFlag_odd : leftFlag oddFlag = true := by decide

theorem flag_cases (k : Flag) : k = 1 ∨ k = oddFlag := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  have h := hz k.toAdd
  rcases h with h | h
  · exact Or.inl (congrArg Multiplicative.ofAdd h)
  · exact Or.inr (congrArg Multiplicative.ofAdd h)

variable {G A B : Type} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def coverLink (a : A → G) (b : B → G) (vertex : VertexGroup G × Bool) :
    A × B → A × B × G :=
  chartLink a b (leftFlag vertex.1.2) (rightFlag vertex.1.2 vertex.2) vertex.1.1

theorem coverLink_incident_iff (a : A → G) (b : B → G)
    (u : G) (k : Flag) (side : Bool) (i : A) (j : B) (g : G) :
    (∃ ij, coverLink a b ((u, k), side) ij = (i, j, g)) ↔
      u = chartVertex a b (leftFlag k) (rightFlag k side) i j g := by
  constructor
  · rintro ⟨ij, he⟩
    have hij : ij = (i, j) := by
      apply Prod.ext
      · exact congrArg (fun q : A × B × G => q.1) he
      · exact congrArg (fun q : A × B × G => q.2.1) he
    subst ij
    exact (chartLink_eq_iff _ _ _ _ _ _ _ _).1 he
  · intro h
    exact ⟨(i, j), (chartLink_eq_iff _ _ _ _ _ _ _ _).2 h⟩

/-- There is one incident vertex in each of the two cover flags. -/
def incidentFlagEquiv (a : A → G) (b : B → G) (side : Bool) (q : A × B × G) :
    {v : VertexGroup G // ∃ ij, coverLink a b (v, side) ij = q} ≃ Flag where
  toFun v := v.val.2
  invFun k := ⟨(chartVertex a b (leftFlag k) (rightFlag k side) q.1 q.2.1 q.2.2, k),
    (coverLink_incident_iff a b _ k side q.1 q.2.1 q.2.2).2 rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · exact ((coverLink_incident_iff a b v.val.1 v.val.2 side q.1 q.2.1 q.2.2).1
        v.property).symm
    · rfl
  right_inv k := rfl

/-- Materialized source four-part complex, satisfying the existing public API.
No total-no-conjugacy premise on `G` is needed. -/
def coverComplex (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹) :
    LeftRightCayleySquareComplex (VertexGroup G) A B (A × B × G) where
  leftGenerator i := (a i, oddFlag)
  rightGenerator j := (b j, 1)
  leftInverse := invA
  rightInverse := invB
  leftGenerator_inverse i := by
    apply Prod.ext
    · exact hA i
    · change oddFlag = oddFlag⁻¹
      decide
  rightGenerator_inverse j := by
    apply Prod.ext
    · exact hB j
    · simp
  noConjugacy g i j := by
    intro he
    have hf := congrArg (fun v : VertexGroup G => v.2) he
    have hn : oddFlag ≠ (1 : Flag) := by decide
    apply hn
    apply mul_right_cancel (b := g.2)
    simpa using hf
  link := coverLink a b
  link_injective v := chartLink_injective a b _ _ _
  square_side_degree q side := by
    rw [← Fintype.card_subtype, Fintype.card_congr (incidentFlagEquiv a b side q)]
    decide

/-- The public API local extension is the source's labelled extension by zero. -/
theorem coverComplex_localExtension (a : A → G) (b : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (v : VertexGroup G × Bool) (x : Word (ZMod 2) (A × B)) :
    (coverComplex a b invA invB hA hB).localExtension v x =
      chartExtension a b (leftFlag v.1.2) (rightFlag v.1.2 v.2) v.1.1 x := by
  rw [chartExtension_eq_sum_single]
  ext q
  simp [LeftRightCayleySquareComplex.localExtension, coverComplex, coverLink,
    Pi.single_apply]

/-- Raw public construction data with bases of the actual local tensor spaces. -/
def coverRawData (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) :
    RawData (VertexGroup G) A B (A × B × G)
      (Fin (Dimension (tensorCode CA.dual CB.dual)))
      (Fin (Dimension (tensorCode CA CB))) where
  complex := coverComplex a b invA invB hA hB
  codeA := CA
  codeB := CB
  xBasis := Module.finBasis (ZMod 2) (tensorCode CA.dual CB.dual).carrier
  zBasis := Module.finBasis (ZMod 2) (tensorCode CA CB).carrier

theorem coverRawData_z_range (a : A → G) (b : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) :
    LinearMap.range (coverRawData a b invA invB hA hB CA CB).zGeneratorMap =
      tannerZChecks a b (tensorCode CA CB) := by
  let D := coverRawData a b invA invB hA hB CA CB
  have hComplex : D.complex = coverComplex a b invA invB hA hB := rfl
  apply le_antisymm
  · rintro x ⟨r, rfl⟩
    change (∑ check, r check • D.zGenerator check) ∈ _
    apply Submodule.sum_mem
    intro check _
    apply Submodule.smul_mem
    change D.complex.localExtension (check.1, false) (D.zBasis check.2).val ∈ _
    rw [hComplex, coverComplex_localExtension]
    rcases flag_cases check.1.2 with hk | hk
    · rw [hk]
      exact Submodule.subset_span (Or.inl ⟨(check.1.1, D.zBasis check.2), rfl⟩)
    · rw [hk]
      exact Submodule.subset_span (Or.inr ⟨(check.1.1, D.zBasis check.2), rfl⟩)
  · apply Submodule.span_le.2
    rintro x (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩)
    · have h := D.localExtension_mem_range_zGeneratorMap (u, 1) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h
    · have h := D.localExtension_mem_range_zGeneratorMap (u, oddFlag) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h

theorem coverRawData_x_range (a : A → G) (b : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hA : ∀ i, a (invA i) = (a i)⁻¹) (hB : ∀ j, b (invB j) = (b j)⁻¹)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) :
    LinearMap.range (coverRawData a b invA invB hA hB CA CB).xGeneratorMap =
      tannerXChecks a b (tensorCode CA.dual CB.dual) := by
  let D := coverRawData a b invA invB hA hB CA CB
  have hComplex : D.complex = coverComplex a b invA invB hA hB := rfl
  apply le_antisymm
  · rintro x ⟨r, rfl⟩
    change (∑ check, r check • D.xGenerator check) ∈ _
    apply Submodule.sum_mem
    intro check _
    apply Submodule.smul_mem
    change D.complex.localExtension (check.1, true) (D.xBasis check.2).val ∈ _
    rw [hComplex, coverComplex_localExtension]
    rcases flag_cases check.1.2 with hk | hk
    · rw [hk]
      exact Submodule.subset_span (Or.inl ⟨(check.1.1, D.xBasis check.2), rfl⟩)
    · rw [hk]
      exact Submodule.subset_span (Or.inr ⟨(check.1.1, D.xBasis check.2), rfl⟩)
  · apply Submodule.span_le.2
    rintro x (⟨⟨u, w⟩, rfl⟩ | ⟨⟨u, w⟩, rfl⟩)
    · have h := D.localExtension_mem_range_xGeneratorMap (u, 1) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h
    · have h := D.localExtension_mem_range_xGeneratorMap (u, oddFlag) w.val w.property
      rw [hComplex, coverComplex_localExtension] at h
      simpa [rightFlag] using h

private theorem generators_comp_zero {Q X Z : Type}
    [Fintype Q] [Fintype X] [Fintype Z]
    (gx : X → Word (ZMod 2) Q) (gz : Z → Word (ZMod 2) Q)
    (hOrth : ∀ i j, dotProduct (gz j) (gx i) = 0) :
    (wordLinearMapTranspose (linearMapOfGenerators gx)).comp
      (linearMapOfGenerators gz) = 0 := by
  apply LinearMap.ext
  intro c
  funext i
  change (∑ q, (linearMapOfGenerators gz c) q *
    (linearMapOfGenerators gx (Pi.single i 1)) q) = 0
  have hsingle : linearMapOfGenerators gx (Pi.single i 1) = gx i := by
    simp [linearMapOfGenerators, Pi.single_apply]
  rw [hsingle]
  change dotProduct (∑ j, c j • gz j) (gx i) = 0
  simp_rw [sum_dotProduct, smul_dotProduct, hOrth]
  simp

variable {C D C' D' : Type} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']

theorem coverRawData_boundary_squared
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, a (invA i) = (a i)⁻¹) (hInvB : ∀ j, b (invB j) = (b j)⁻¹)
    (hDualA : parityCheckKernelCode (Matrix.toLin' gA) =
      (parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : parityCheckKernelCode (Matrix.toLin' gB) =
      (parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let T := coverRawData a b invA invB hInvA hInvB
      (parityCheckKernelCode (Matrix.toLin' gA)) (parityCheckKernelCode (Matrix.toLin' hB))
    T.boundary1.comp T.boundary2 = 0 := by
  dsimp only
  let T := coverRawData a b invA invB hInvA hInvB
    (parityCheckKernelCode (Matrix.toLin' gA)) (parityCheckKernelCode (Matrix.toLin' hB))
  have hSpaces := selected_lifted_product_eq_quantum_tanner hA hB gA gB a b hDualA hDualB
  have hZ : Set.range (selectedZWord hA hB gB a b) = (LinearMap.range T.zGeneratorMap).carrier := by
    rw [coverRawData_z_range]
    exact hSpaces.1
  have hX : Set.range (selectedXWord hA hB gA a b) = (LinearMap.range T.xGeneratorMap).carrier := by
    rw [coverRawData_x_range]
    exact hSpaces.2.1
  apply generators_comp_zero T.xGenerator T.zGenerator
  intro i j
  have hz := generator_mem_range_linearMapOfGenerators T.zGenerator j
  have hx := generator_mem_range_linearMapOfGenerators T.xGenerator i
  change T.zGenerator j ∈ (LinearMap.range T.zGeneratorMap).carrier at hz
  change T.xGenerator i ∈ (LinearMap.range T.xGeneratorMap).carrier at hx
  rw [← hZ] at hz
  rw [← hX] at hx
  obtain ⟨U, hU⟩ := hz
  obtain ⟨V, hV⟩ := hx
  rw [← hU, ← hV]
  have hSum := hSpaces.2.2 U V
  rw [Finset.sum_comm] at hSum
  simpa only [dotProduct, Fintype.sum_prod_type] using hSum

/-- Actual public Quantum Tanner data; its CSS law is derived, not an input. -/
def selectedData
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, a (invA i) = (a i)⁻¹) (hInvB : ∀ j, b (invB j) = (b j)⁻¹)
    (hDualA : parityCheckKernelCode (Matrix.toLin' gA) =
      (parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : parityCheckKernelCode (Matrix.toLin' gB) =
      (parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    Data (VertexGroup G) A B (A × B × G)
      (Fin (Dimension (tensorCode (parityCheckKernelCode (Matrix.toLin' gA)).dual
        (parityCheckKernelCode (Matrix.toLin' hB)).dual)))
      (Fin (Dimension (tensorCode (parityCheckKernelCode (Matrix.toLin' gA))
        (parityCheckKernelCode (Matrix.toLin' hB))))) where
  toRawData := coverRawData a b invA invB hInvA hInvB
    (parityCheckKernelCode (Matrix.toLin' gA)) (parityCheckKernelCode (Matrix.toLin' hB))
  boundary_squared := coverRawData_boundary_squared hA hB gA gB a b invA invB
    hInvA hInvB hDualA hDualB

/-- The selected, punctured canonical lifted product has exactly the two
check spaces of the explicitly constructed public Quantum Tanner data.
The lift and the Tanner data are outputs constructed from the scalar input;
neither is an arbitrary code nor a conclusion-bearing certificate premise. -/
theorem quantumTanner_from_liftedProduct
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (bridgeLeft : A → G) (bridgeRight : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hInvA : ∀ i, bridgeLeft (invA i) = (bridgeLeft i)⁻¹) (hInvB : ∀ j, bridgeRight (invB j) = (bridgeRight j)⁻¹)
    (hDualA : _root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA) =
      (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : _root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gB) =
      (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let lifted : _root_.QEC.Coding.LiftedProduct.Data (ZMod 2) G (Bool × D) B A (Bool × C) :=
      LiftedProductActionBridge.canonicalData hA hB bridgeLeft bridgeRight
    let tanner : _root_.QEC.Coding.QuantumTanner.Data (VertexGroup G) A B (A × B × G)
        (Fin (Dimension (tensorCode (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA)).dual
          (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB)).dual)))
        (Fin (Dimension (tensorCode (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
          (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))))) :=
      selectedData hA hB gA gB bridgeLeft bridgeRight invA invB hInvA hInvB hDualA hDualB
    Set.range (fun U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
        Matrix C D' (MonoidAlgebra (ZMod 2) G) => fun (i, j, g) =>
      (LiftedProduct.boundary2Matrix lifted).mulVec
        (zParameter (U.1 * twistedMatrix gB (fun j => (bridgeRight j)⁻¹)) (U.2 * scalarMatrix gB))
        (retainedCoordinate i j g)) = (LinearMap.range tanner.toRawData.zGeneratorMap).carrier ∧
    Set.range (fun V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
        Matrix C' D (MonoidAlgebra (ZMod 2) G) => fun (i, j, g) =>
      (LiftedProduct.boundary1Matrix lifted).transpose.mulVec
        (xParameter ((scalarMatrix gA).transpose * V.1)
          ((twistedMatrix gA (fun i => (bridgeLeft i)⁻¹)).transpose * V.2))
        (retainedCoordinate i j g)) = (LinearMap.range tanner.toRawData.xGeneratorMap).carrier ∧
    tanner.blockLength = Fintype.card G * Fintype.card A * Fintype.card B := by
  dsimp only
  change Set.range (selectedZWord hA hB gB bridgeLeft bridgeRight) = _ ∧
    Set.range (selectedXWord hA hB gA bridgeLeft bridgeRight) = _ ∧ _
  have hSpaces := selected_lifted_product_eq_quantum_tanner hA hB gA gB bridgeLeft bridgeRight hDualA hDualB
  refine ⟨?_, ?_, ?_⟩
  · change Set.range (selectedZWord hA hB gB bridgeLeft bridgeRight) =
      (LinearMap.range (coverRawData bridgeLeft bridgeRight invA invB hInvA hInvB
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))).zGeneratorMap).carrier
    rw [coverRawData_z_range]
    exact hSpaces.1
  · change Set.range (selectedXWord hA hB gA bridgeLeft bridgeRight) =
      (LinearMap.range (coverRawData bridgeLeft bridgeRight invA invB hInvA hInvB
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' gA))
        (_root_.QEC.Coding.parityCheckKernelCode (Matrix.toLin' hB))).xGeneratorMap).carrier
    rw [coverRawData_x_range]
    exact hSpaces.2.1
  · simp [Data.blockLength, Fintype.card_prod, mul_assoc, mul_left_comm, mul_comm]

end QEC.Coding.QuantumTanner.LiftedProductTannerCode
