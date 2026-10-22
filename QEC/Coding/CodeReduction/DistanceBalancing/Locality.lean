import QEC.Coding.CodeReduction.DistanceBalancing.Core
import QEC.Coding.FiberBundle.WeightReductionParameters

/-!
# Locality of the EKZ distance-balancing product

The block formulas below compute every product check row and every product
qubit column.  They turn locality bounds for the source complex and the
classical factor into a locality bound for the product without accepting a
locality conclusion as input.
-/

namespace QEC.Coding.DistanceBalancing

universe u

open QEC.Coding.FiberBundle

variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem matrixToLin_single
    {Row Col : Type u} [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col (ZMod 2)) (c : Col) :
    Matrix.toLin' M (Pi.single c 1) = fun r ↦ M r c := by
  ext r
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc']
  · simp

private theorem canonicalBasisWord_eq_single
    {I : Type u} [DecidableEq I] (i : I) :
    canonicalBasisWord (F := ZMod 2) i = Pi.single i 1 := by
  classical
  ext i'
  by_cases hi : i = i'
  · subst i'
    simp [canonicalBasisWord]
  · simp [canonicalBasisWord, hi]

/-- Canonical-basis version of the chain-complex locality constructor.  This
keeps the chosen `DecidableEq` implementation out of downstream theorem
interfaces, which is important for large construction-owned index types. -/
theorem boundedLocality_of_canonical_boundary_bounds
    {zero one two : Type u}
    [Fintype zero] [DecidableEq zero]
    [Fintype one] [DecidableEq one]
    [Fintype two] [DecidableEq two]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) zero) (Word (ZMod 2) one) (Word (ZMod 2) two))
    {checkBound variableBound : Nat}
    (hZero : ∀ x0,
      HammingWeight
        (wordLinearMapTranspose X.boundary1
          (canonicalBasisWord (F := ZMod 2) x0)) ≤ checkBound)
    (hTwo : ∀ x2,
      HammingWeight
        (X.boundary2 (canonicalBasisWord (F := ZMod 2) x2)) ≤ checkBound)
    (hVariable : ∀ x1,
      ((QEC.QLDPC.chainComplexBoundaryIncidence X).variableSupport x1).card ≤
        variableBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile
      (max checkBound variableBound) := by
  classical
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
    X (w := checkBound) (variableDegree := variableBound)
  · exact hZero
  · exact hTwo
  · exact hVariable

private theorem HammingWeight_reverse_fiber_coordinate_eq
    {B I : Type u} [Fintype B] [Fintype I] [DecidableEq I]
    (x : Word (ZMod 2) B) (i : I) :
    HammingWeight (fun p : B × I ↦ if p.2 = i then x p.1 else 0) =
      HammingWeight x := by
  -- Swap the condition pointwise before transporting it through HammingWeight.
  have hswap : (fun p : B × I ↦ if p.2 = i then x p.1 else 0) =
      (fun p : B × I ↦ if i = p.2 then x p.1 else 0) := by
    funext p
    by_cases hpi : p.2 = i
    · rw [if_pos hpi, if_pos hpi.symm]
    · rw [if_neg hpi, if_neg (Ne.symm hpi)]
  rw [hswap]
  exact HammingWeight_one_fiber_coordinate_eq x (fun _ ↦ Equiv.refl I) i

theorem HammingWeight_transpose_boundary1_single_inl_eq
    (x0 : xZero) (a : classicalBit) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (Pi.single (Sum.inl (x0, a)) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary1 x0 x1) := by
  rw [boundary1, wordLinearMapTranspose_matrixToLin_single]
  have hWord : (fun c ↦ boundary1Matrix D (Sum.inl (x0, a)) c) =
      (Sum.elim
        (fun p : xOne × classicalBit ↦
          if a = p.2 then D.xBoundary1 x0 p.1 else 0)
        (fun _ : xTwo × classicalCheck ↦ 0)) := by
    funext c
    cases c <;> rfl
  rw [hWord]
  rw [HammingWeight_sum_elim_eq]
  have hZero : HammingWeight
      (fun _ : xTwo × classicalCheck ↦ (0 : ZMod 2)) = 0 := by
    rw [HammingWeight_eq_zero_iff]
    rfl
  rw [hZero, Nat.add_zero]
  exact HammingWeight_one_fiber_coordinate_eq
      (fun x1 ↦ D.xBoundary1 x0 x1)
      (fun _ ↦ Equiv.refl classicalBit) a

theorem HammingWeight_transpose_boundary1_single_inr_eq
    (x1 : xOne) (b : classicalCheck) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (Pi.single (Sum.inr (x1, b)) 1)) =
      HammingWeight (fun a ↦ D.classicalBoundary b a) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) := by
  rw [boundary1, wordLinearMapTranspose_matrixToLin_single]
  have hWord : (fun c ↦ boundary1Matrix D (Sum.inr (x1, b)) c) =
      (Sum.elim
        (fun p : xOne × classicalBit ↦
          if x1 = p.1 then D.classicalBoundary b p.2 else 0)
        (fun p : xTwo × classicalCheck ↦
          if b = p.2 then D.xBoundary2 x1 p.1 else 0)) := by
    funext c
    cases c <;> rfl
  rw [hWord]
  rw [HammingWeight_sum_elim_eq]
  rw [HammingWeight_fixed_base_coordinate_eq]
  exact congrArg
    (fun n ↦ HammingWeight (fun a ↦ D.classicalBoundary b a) + n)
    (HammingWeight_one_fiber_coordinate_eq
      (fun x2 ↦ D.xBoundary2 x1 x2)
      (fun _ ↦ Equiv.refl classicalCheck) b)

theorem HammingWeight_boundary2_single_eq
    (x2 : xTwo) (a : classicalBit) :
    HammingWeight (boundary2 D (Pi.single (x2, a) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) +
        HammingWeight (fun b ↦ D.classicalBoundary b a) := by
  rw [boundary2, matrixToLin_single]
  have hWord : (fun r ↦ boundary2Matrix D r (x2, a)) =
      (Sum.elim
        (fun p : xOne × classicalBit ↦
          if p.2 = a then D.xBoundary2 p.1 x2 else 0)
        (fun p : xTwo × classicalCheck ↦
          if p.1 = x2 then D.classicalBoundary p.2 a else 0)) := by
    funext r
    cases r <;> rfl
  rw [hWord]
  rw [HammingWeight_sum_elim_eq]
  have hRight := HammingWeight_fixed_base_coordinate_eq
    x2 (fun b ↦ D.classicalBoundary b a)
  have hLeft' : HammingWeight
      (fun p : xOne × classicalBit ↦
        if p.2 = a then D.xBoundary2 p.1 x2 else 0) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) := by
    exact HammingWeight_reverse_fiber_coordinate_eq (fun x1 ↦ D.xBoundary2 x1 x2) a
  have hRight' : HammingWeight
      (fun p : xTwo × classicalCheck ↦
        if p.1 = x2 then D.classicalBoundary p.2 a else 0) =
      HammingWeight (fun b ↦ D.classicalBoundary b a) := by
    simpa only [eq_comm] using hRight
  rw [hLeft', hRight']

theorem boundaryColumnWeight_inl_eq
    (x1 : xOne) (a : classicalBit) :
    HammingWeight (boundary1 D (Pi.single (Sum.inl (x1, a)) 1)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (Pi.single (Sum.inl (x1, a)) 1)) =
      HammingWeight (fun x0 ↦ D.xBoundary1 x0 x1) +
        HammingWeight (fun b ↦ D.classicalBoundary b a) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) := by
  rw [boundary1, matrixToLin_single]
  rw [boundary2, wordLinearMapTranspose_matrixToLin_single]
  have hWord1 :
      (fun r ↦ boundary1Matrix D r (Sum.inl (x1, a))) =
        (Sum.elim
          (fun p : xZero × classicalBit ↦
            if p.2 = a then D.xBoundary1 p.1 x1 else 0)
          (fun p : xOne × classicalCheck ↦
            if p.1 = x1 then D.classicalBoundary p.2 a else 0)) := by
    funext r
    cases r <;> rfl
  have hWord2 :
      (fun c ↦ boundary2Matrix D (Sum.inl (x1, a)) c) =
        (fun p : xTwo × classicalBit ↦
          if a = p.2 then D.xBoundary2 x1 p.1 else 0) := by
    funext c
    rfl
  rw [hWord1, hWord2]
  rw [HammingWeight_sum_elim_eq]
  have h₂ := HammingWeight_fixed_base_coordinate_eq
    x1 (fun b ↦ D.classicalBoundary b a)
  have h₃ := HammingWeight_one_fiber_coordinate_eq
    (fun x2 ↦ D.xBoundary2 x1 x2)
    (fun _ ↦ Equiv.refl classicalBit) a
  have h₁' : HammingWeight
      (fun p : xZero × classicalBit ↦
        if p.2 = a then D.xBoundary1 p.1 x1 else 0) =
      HammingWeight (fun x0 ↦ D.xBoundary1 x0 x1) := by
    exact HammingWeight_reverse_fiber_coordinate_eq (fun x0 ↦ D.xBoundary1 x0 x1) a
  have h₂' : HammingWeight
      (fun p : xOne × classicalCheck ↦
        if p.1 = x1 then D.classicalBoundary p.2 a else 0) =
      HammingWeight (fun b ↦ D.classicalBoundary b a) := by
    simpa only [eq_comm] using h₂
  have h₃' : HammingWeight
      (fun p : xTwo × classicalBit ↦
        if a = p.2 then D.xBoundary2 x1 p.1 else 0) =
      HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) := by
    exact h₃
  rw [h₁', h₂', h₃']

theorem boundaryColumnWeight_inr_eq
    (x2 : xTwo) (b : classicalCheck) :
    HammingWeight (boundary1 D (Pi.single (Sum.inr (x2, b)) 1)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (Pi.single (Sum.inr (x2, b)) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) +
        HammingWeight (fun a ↦ D.classicalBoundary b a) := by
  rw [boundary1, matrixToLin_single]
  rw [boundary2, wordLinearMapTranspose_matrixToLin_single]
  have hWord1 :
      (fun r ↦ boundary1Matrix D r (Sum.inr (x2, b))) =
        (Sum.elim
          (fun _ : xZero × classicalBit ↦ 0)
          (fun p : xOne × classicalCheck ↦
            if p.2 = b then D.xBoundary2 p.1 x2 else 0)) := by
    funext r
    cases r <;> rfl
  have hWord2 :
      (fun c ↦ boundary2Matrix D (Sum.inr (x2, b)) c) =
        (fun p : xTwo × classicalBit ↦
          if x2 = p.1 then D.classicalBoundary b p.2 else 0) := by
    funext c
    rfl
  rw [hWord1, hWord2]
  rw [HammingWeight_sum_elim_eq]
  have hZero : HammingWeight
      (fun _ : xZero × classicalBit ↦ (0 : ZMod 2)) = 0 := by
    rw [HammingWeight_eq_zero_iff]
    rfl
  rw [hZero, zero_add]
  have hRight := HammingWeight_fixed_base_coordinate_eq
    x2 (fun a ↦ D.classicalBoundary b a)
  have hLeft' : HammingWeight
      (fun p : xOne × classicalCheck ↦
        if p.2 = b then D.xBoundary2 p.1 x2 else 0) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) := by
    exact HammingWeight_reverse_fiber_coordinate_eq (fun x1 ↦ D.xBoundary2 x1 x2) b
  rw [hLeft', hRight]

/-- Exact product variable degree in terms of its two boundary columns. -/
theorem productVariableSupport_card_eq_boundaryColumnWeight
    (q : QubitIndex xOne xTwo classicalBit classicalCheck) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence (chainComplex D)).variableSupport q).card =
      HammingWeight (boundary1 D (canonicalBasisWord (F := ZMod 2) q)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (canonicalBasisWord (F := ZMod 2) q)) := by
  simpa [chainComplex] using
    (chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
      (chainComplex D) q)

/-- Locality bounds for both input factors add under the finite EKZ product. -/
theorem boundedLocality_add
    {sourceBound classicalBound : Nat}
    (hSourceX : ∀ x0,
      HammingWeight (fun x1 ↦ D.xBoundary1 x0 x1) ≤ sourceBound)
    (hSourceZ : ∀ x2,
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) ≤ sourceBound)
    (hSourceVariable : ∀ x1,
      HammingWeight (fun x0 ↦ D.xBoundary1 x0 x1) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) ≤ sourceBound)
    (hClassicalRow : ∀ b,
      HammingWeight (fun a ↦ D.classicalBoundary b a) ≤ classicalBound)
    (hClassicalColumn : ∀ a,
      HammingWeight (fun b ↦ D.classicalBoundary b a) ≤ classicalBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex D)).localityProfile
      (sourceBound + classicalBound) := by
  rw [← max_self (sourceBound + classicalBound)]
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
    (chainComplex D) (w := sourceBound + classicalBound)
      (variableDegree := sourceBound + classicalBound)
  · intro c0
    change HammingWeight
      (wordLinearMapTranspose (boundary1 D)
        (canonicalBasisWord (F := ZMod 2) c0)) ≤ _
    rw [canonicalBasisWord_eq_single]
    cases c0 with
    | inl p =>
        rcases p with ⟨x0, a⟩
        rw [HammingWeight_transpose_boundary1_single_inl_eq]
        exact (hSourceX x0).trans (Nat.le_add_right _ _)
    | inr p =>
        rcases p with ⟨x1, b⟩
        rw [HammingWeight_transpose_boundary1_single_inr_eq]
        have hVariable := hSourceVariable x1
        have hRow := hClassicalRow b
        omega
  · intro c2
    rcases c2 with ⟨x2, a⟩
    change HammingWeight
      (boundary2 D (canonicalBasisWord (F := ZMod 2) (x2, a))) ≤ _
    rw [canonicalBasisWord_eq_single]
    rw [HammingWeight_boundary2_single_eq]
    exact Nat.add_le_add (hSourceZ x2) (hClassicalColumn a)
  · intro q
    rw [productVariableSupport_card_eq_boundaryColumnWeight]
    rw [canonicalBasisWord_eq_single]
    cases q with
    | inl p =>
        rcases p with ⟨x1, a⟩
        rw [boundaryColumnWeight_inl_eq]
        have hVariable := hSourceVariable x1
        have hColumn := hClassicalColumn a
        omega
    | inr p =>
        rcases p with ⟨x2, b⟩
        rw [boundaryColumnWeight_inr_eq]
        exact Nat.add_le_add (hSourceZ x2) (hClassicalRow b)

/-- Map-level version of `boundedLocality_add` for the construction-owned
`Data.ofComplexes` entry point. -/
theorem boundedLocality_add_ofComplexes
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck)
    {sourceBound classicalBound : Nat}
    (hSourceX : ∀ x0,
      HammingWeight
        (wordLinearMapTranspose X.boundary1
          (canonicalBasisWord (F := ZMod 2) x0)) ≤ sourceBound)
    (hSourceZ : ∀ x2,
      HammingWeight
        (X.boundary2 (canonicalBasisWord (F := ZMod 2) x2)) ≤ sourceBound)
    (hSourceVariable : ∀ x1,
      HammingWeight
          (X.boundary1 (canonicalBasisWord (F := ZMod 2) x1)) +
        HammingWeight
          (wordLinearMapTranspose X.boundary2
            (canonicalBasisWord (F := ZMod 2) x1)) ≤ sourceBound)
    (hClassicalRow : ∀ b,
      HammingWeight
        (wordLinearMapTranspose Y (Pi.single b 1)) ≤ classicalBound)
    (hClassicalColumn : ∀ a,
      HammingWeight (Y (Pi.single a 1)) ≤ classicalBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex (Data.ofComplexes X Y))).localityProfile
      (sourceBound + classicalBound) := by
  apply boundedLocality_add (Data.ofComplexes X Y)
  · intro x0
    change HammingWeight
      (fun x1 ↦ (LinearMap.toMatrix' X.boundary1) x0 x1) ≤ sourceBound
    rw [← wordLinearMapTranspose_matrixToLin_single]
    rw [Matrix.toLin'_toMatrix']
    rw [← canonicalBasisWord_eq_single]
    exact hSourceX x0
  · intro x2
    change HammingWeight
      (fun x1 ↦ (LinearMap.toMatrix' X.boundary2) x1 x2) ≤ sourceBound
    rw [← matrixToLin_single]
    rw [Matrix.toLin'_toMatrix']
    rw [← canonicalBasisWord_eq_single]
    exact hSourceZ x2
  · intro x1
    change
      HammingWeight
          (fun x0 ↦ (LinearMap.toMatrix' X.boundary1) x0 x1) +
        HammingWeight
          (fun x2 ↦ (LinearMap.toMatrix' X.boundary2) x1 x2) ≤ sourceBound
    rw [← matrixToLin_single]
    rw [← wordLinearMapTranspose_matrixToLin_single]
    rw [Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    rw [← canonicalBasisWord_eq_single]
    exact hSourceVariable x1
  · intro b
    change HammingWeight
      (fun a ↦ (LinearMap.toMatrix' Y) b a) ≤ classicalBound
    rw [← wordLinearMapTranspose_matrixToLin_single]
    rw [Matrix.toLin'_toMatrix']
    exact hClassicalRow b
  · intro a
    change HammingWeight
      (fun b ↦ (LinearMap.toMatrix' Y) b a) ≤ classicalBound
    rw [← matrixToLin_single]
    rw [Matrix.toLin'_toMatrix']
    exact hClassicalColumn a

theorem checkSupport_card_le_of_boundedLocality
    {check var : Type u} [Fintype check] [Fintype var]
    (I : QEC.QLDPC.CheckIncidence check var) {B : Nat}
    (h : BoundedLocality I.localityProfile B) (c : check) :
    (I.checkSupport c).card ≤ B := by
  have hc : (I.checkSupport c).card ≤
      Finset.univ.sup (fun c' ↦ (I.checkSupport c').card) :=
    Finset.le_sup (f := fun c' ↦ (I.checkSupport c').card)
      (Finset.mem_univ c)
  exact hc.trans h.1

theorem variableSupport_card_le_of_boundedLocality
    {check var : Type u} [Fintype check] [Fintype var]
    (I : QEC.QLDPC.CheckIncidence check var) {B : Nat}
    (h : BoundedLocality I.localityProfile B) (q : var) :
    (I.variableSupport q).card ≤ B := by
  have hq : (I.variableSupport q).card ≤
      Finset.univ.sup (fun q' ↦ (I.variableSupport q').card) :=
    Finset.le_sup (f := fun q' ↦ (I.variableSupport q').card)
      (Finset.mem_univ q)
  exact hq.trans h.2

/-- Finite-coordinate dualization preserves the same incidence-locality
bound, swapping the two kinds of checks and leaving variable degree intact. -/
theorem boundedLocality_dual
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    {B : Nat}
    (h : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile B) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (dualChainComplex X)).localityProfile B := by
  rw [← max_self B]
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
    (dualChainComplex X) (w := B) (variableDegree := B)
  · intro x2
    rw [dualChainComplex_boundary1, wordLinearMapTranspose_transpose]
    rw [HammingWeight_eq_card_hammingSupport]
    rw [← QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr X x2]
    exact checkSupport_card_le_of_boundedLocality _ h (Sum.inr x2)
  · intro x0
    rw [dualChainComplex_boundary2]
    rw [HammingWeight_eq_card_hammingSupport]
    rw [← QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl X x0]
    exact checkSupport_card_le_of_boundedLocality _ h (Sum.inl x0)
  · intro x1
    have hVariable := variableSupport_card_le_of_boundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X) h x1
    rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
      X x1] at hVariable
    rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
      (dualChainComplex X) x1]
    simp only [dualChainComplex_boundary1, dualChainComplex_boundary2,
      wordLinearMapTranspose_transpose]
    omega

/-- If the source complex already carries a bounded incidence-locality proof,
only the classical row and column bounds remain to prove product locality. -/
theorem boundedLocality_add_ofComplexes_of_source_bounded
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck)
    {sourceBound classicalBound : Nat}
    (hSource : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceBound)
    (hClassicalRow : ∀ b,
      HammingWeight
        (wordLinearMapTranspose Y (Pi.single b 1)) ≤ classicalBound)
    (hClassicalColumn : ∀ a,
      HammingWeight (Y (Pi.single a 1)) ≤ classicalBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex (Data.ofComplexes X Y))).localityProfile
      (sourceBound + classicalBound) := by
  apply boundedLocality_add_ofComplexes X Y
  · intro x0
    rw [HammingWeight_eq_card_hammingSupport]
    have hx := checkSupport_card_le_of_boundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X) hSource (Sum.inl x0)
    simpa only [QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl] using hx
  · intro x2
    rw [HammingWeight_eq_card_hammingSupport]
    have hx := checkSupport_card_le_of_boundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X) hSource (Sum.inr x2)
    simpa only [QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr] using hx
  · intro x1
    have hVariable := variableSupport_card_le_of_boundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X) hSource x1
    rw [chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
      X x1] at hVariable
    exact hVariable
  · exact hClassicalRow
  · exact hClassicalColumn

end QEC.Coding.DistanceBalancing
