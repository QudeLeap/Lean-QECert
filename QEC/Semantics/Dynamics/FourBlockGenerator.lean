import QEC.Semantics.Dynamics.Lindblad
/-!
# The CLBT four-block generator estimate

This module formalizes the local estimate in part II of the proof of CLBT10,
Theorem 1.  It is deliberately independent of any syndrome realization: jump
protection is the source equation `[J_a, O] P = 0`, and the conclusion concerns
only the Lindblad dissipator applied to `O ρβ`.

No time integration, encoding/decoding construction, or storage-horizon claim
is made here.
-/

universe u v

namespace QEC.Semantics

open scoped BigOperators ComplexOrder

noncomputable section

variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

/-! ## The source induced trace norm -/

/-- A copy of the finite operator space carrying the Schatten-1 norm. -/
private def TraceNormedOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteQuantumSystem H] := Operator H

private instance : AddCommGroup (TraceNormedOperator H) :=
  inferInstanceAs (AddCommGroup (Operator H))

private instance : Module ℂ (TraceNormedOperator H) :=
  inferInstanceAs (Module ℂ (Operator H))

private def traceNormedOperatorSeminorm : AddGroupSeminorm (TraceNormedOperator H) where
  toFun A := traceNorm (H := H) A
  map_zero' := (traceNorm_eq_zero_iff (H := H) 0).2 rfl
  neg' := traceNorm_neg
  add_le' := traceNorm_add_le

private instance traceNormedOperatorSeminormedAddCommGroup :
    SeminormedAddCommGroup (TraceNormedOperator H) :=
  traceNormedOperatorSeminorm.toSeminormedAddCommGroup

private instance traceNormedOperatorNormedAddCommGroup :
    NormedAddCommGroup (TraceNormedOperator H) :=
  NormedAddCommGroup.ofSeparation fun A hA =>
    (traceNorm_eq_zero_iff (H := H) A).1 hA

private instance traceNormedOperatorNormedSpace :
    NormedSpace ℂ (TraceNormedOperator H) where
  norm_smul_le c A := by
    change traceNorm (c • (A : Operator H)) ≤ ‖c‖ * traceNorm (A : Operator H)
    exact le_of_eq (traceNorm_smul c A)

private def traceNormedOperatorToOperator :
    TraceNormedOperator H →ₗ[ℂ] Operator H :=
  LinearMap.id

private instance traceNormedOperatorFiniteDimensional :
    FiniteDimensional ℂ (TraceNormedOperator H) :=
  FiniteDimensional.of_injective traceNormedOperatorToOperator
    (LinearMap.ker_eq_bot.mp rfl)

/-- Every algebraic superoperator is continuous for the trace norm in finite dimension. -/
private noncomputable def traceNormContinuousSuperoperator (L : Superoperator H) :
    TraceNormedOperator H →L[ℂ] TraceNormedOperator H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => L A
      map_add' := by intro A B; exact L.map_add A B
      map_smul' := by intro c A; exact L.map_smul c A }

private theorem traceNorm_apply_le_continuousNorm
    (L : Superoperator H) (A : Operator H) :
    traceNorm (L A) ≤ ‖traceNormContinuousSuperoperator L‖ * traceNorm A := by
  exact (traceNormContinuousSuperoperator L).le_opNorm A

private theorem selfAdjointTraceNormOneToOne_bddAbove (L : Superoperator H) :
    BddAbove {r : ℝ | ∃ A : Operator H,
      A.IsSymmetric ∧ traceNorm A ≤ 1 ∧ r = traceNorm (L A)} := by
  refine ⟨‖traceNormContinuousSuperoperator L‖, ?_⟩
  rintro r ⟨A, _hA, hnorm, rfl⟩
  calc
    traceNorm (L A) ≤ ‖traceNormContinuousSuperoperator L‖ * traceNorm A :=
      traceNorm_apply_le_continuousNorm L A
    _ ≤ ‖traceNormContinuousSuperoperator L‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = ‖traceNormContinuousSuperoperator L‖ := mul_one _

theorem selfAdjointTraceNormOneToOne_nonneg (L : Superoperator H) :
    0 ≤ selfAdjointTraceNormOneToOne L := by
  apply le_csSup (selfAdjointTraceNormOneToOne_bddAbove L)
  refine ⟨(0 : Operator H), ?_, ?_, ?_⟩
  · intro x y
    simp
  · rw [(traceNorm_eq_zero_iff (0 : Operator H)).2 rfl]
    norm_num
  · rw [L.map_zero, (traceNorm_eq_zero_iff (0 : Operator H)).2 rfl]

/-- The source induced norm bounds a superoperator on every self-adjoint input. -/
theorem traceNorm_apply_le_selfAdjointTraceNormOneToOne
    (L : Superoperator H) (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm (L A) ≤ selfAdjointTraceNormOneToOne L * traceNorm A := by
  by_cases hzero : traceNorm A = 0
  · have hA0 : A = 0 := (traceNorm_eq_zero_iff A).1 hzero
    rw [hA0, L.map_zero, (traceNorm_eq_zero_iff (0 : Operator H)).2 rfl]
    exact mul_nonneg (selfAdjointTraceNormOneToOne_nonneg L) (le_refl 0)
  · have hpos : 0 < traceNorm A := lt_of_le_of_ne (traceNorm_nonneg A) (Ne.symm hzero)
    let c : ℂ := (traceNorm A : ℂ)⁻¹
    let B : Operator H := c • A
    have hBsym : B.IsSymmetric := by
      intro x y
      simp only [B, LinearMap.smul_apply, inner_smul_left, inner_smul_right]
      rw [hA x y]
      congr 1
      simp [c]
    have hc : ‖c‖ = (traceNorm A)⁻¹ := by
      simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hBnorm : traceNorm B ≤ 1 := by
      change traceNorm (c • A) ≤ 1
      rw [traceNorm_smul, hc, inv_mul_cancel₀ hzero]
    have hmember : traceNorm (L B) ∈ {r : ℝ | ∃ C : Operator H,
        C.IsSymmetric ∧ traceNorm C ≤ 1 ∧ r = traceNorm (L C)} :=
      ⟨B, hBsym, hBnorm, rfl⟩
    have hunit : traceNorm (L B) ≤ selfAdjointTraceNormOneToOne L :=
      le_csSup (selfAdjointTraceNormOneToOne_bddAbove L) hmember
    have hscale : L B = c • L A := by
      exact L.map_smul c A
    rw [hscale, traceNorm_smul] at hunit
    rw [hc] at hunit
    calc
      traceNorm (L A) = traceNorm A * ((traceNorm A)⁻¹ * traceNorm (L A)) := by
        field_simp
      _ ≤ traceNorm A * selfAdjointTraceNormOneToOne L :=
        mul_le_mul_of_nonneg_left hunit (traceNorm_nonneg A)
      _ = selfAdjointTraceNormOneToOne L * traceNorm A := mul_comm _ _

/-! ## Protection and the four source blocks -/

/-- CLBT's source-exact abstract jump-protection predicate `[J_a, O] P = 0`. -/
def JumpProtected [Fintype ι]
    (J : ι → Operator H) (O P : Operator H) : Prop :=
  ∀ a, (J a * O - O * J a) * P = 0

theorem JumpProtected.jump_mul_observable_projector [Fintype ι]
    {J : ι → Operator H} {O P : Operator H} (h : JumpProtected J O P) (a : ι) :
    J a * O * P = O * J a * P := by
  have ha := h a
  rw [sub_mul] at ha
  exact sub_eq_zero.mp ha

/-- Taking adjoints supplies the second protection equation used by CLBT. -/
theorem JumpProtected.projector_mul_observable_adjoint [Fintype ι]
    {J : ι → Operator H} {O P : Operator H} (h : JumpProtected J O P)
    (hO : O.IsSymmetric) (hP : IsStarProjection P) (a : ι) :
    P * O * LinearMap.adjoint (J a) =
      P * LinearMap.adjoint (J a) * O := by
  have hPsym : P.IsSymmetric :=
    (LinearMap.isStarProjection_iff_isSymmetricProjection.mp hP).2
  have ha := congrArg LinearMap.adjoint (h a)
  simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, map_sub, map_zero,
    hO.adjoint_eq, hPsym.adjoint_eq] at ha
  change P * (O * LinearMap.adjoint (J a) -
    LinearMap.adjoint (J a) * O) = 0 at ha
  rw [mul_sub] at ha
  exact sub_eq_zero.mp ha

/-- CLBT's first block `P L(O P ρβ)`. -/
def clbtGeneratorBlockOne (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  P * L (O * P * rho)

/-- CLBT's second block `(I-P) L(O P ρβ)`. -/
def clbtGeneratorBlockTwo (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  (1 - P) * L (O * P * rho)

/-- CLBT's third block `P L(O (I-P) ρβ)`. -/
def clbtGeneratorBlockThree (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  P * L (O * (1 - P) * rho)

/-- CLBT's fourth block `(I-P) L(O (I-P) ρβ)`. -/
def clbtGeneratorBlockFour (L : Superoperator H) (O P rho : Operator H) : Operator H :=
  (1 - P) * L (O * (1 - P) * rho)

/-- Inserting `P + (I-P) = I` at the input and output gives the four blocks. -/
theorem clbtGenerator_eq_sum_four_blocks
    (L : Superoperator H) (O P rho : Operator H) :
    L (O * rho) =
      clbtGeneratorBlockOne L O P rho +
      clbtGeneratorBlockTwo L O P rho +
      clbtGeneratorBlockThree L O P rho +
      clbtGeneratorBlockFour L O P rho := by
  have hinput : O * rho = O * P * rho + O * (1 - P) * rho := by
    noncomm_ring
  have hout (A : Operator H) : L A = P * L A + (1 - P) * L A := by
    noncomm_ring
  rw [hinput, map_add, hout (O * P * rho), hout (O * (1 - P) * rho)]
  unfold clbtGeneratorBlockOne clbtGeneratorBlockTwo
    clbtGeneratorBlockThree clbtGeneratorBlockFour
  noncomm_ring

/-! ## Block rewrites from jump protection -/

private theorem jumpTerm_good_input_left [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P) (a : ι) :
    P * lindbladJumpTerm (J a) (O * P * A) =
      O * P * lindbladJumpTerm (J a) (P * A) := by
  have hj := hprotected.jump_mul_observable_projector a
  have hjadj := hprotected.projector_mul_observable_adjoint hO hP a
  have hgain :
      P * (J a * (O * P * A) * LinearMap.adjoint (J a)) =
        O * P * (J a * (P * A) * LinearMap.adjoint (J a)) := by
    calc
      _ = P * ((J a * O * P) * A * LinearMap.adjoint (J a)) := by
        noncomm_ring
      _ = P * ((O * J a * P) * A * LinearMap.adjoint (J a)) := by rw [hj]
      _ = _ := by noncomm_ring [hOP.eq]
  have hlossLeft :
      P * ((LinearMap.adjoint (J a) * J a) * (O * P * A)) =
        O * P * ((LinearMap.adjoint (J a) * J a) * (P * A)) := by
    calc
      _ = P * LinearMap.adjoint (J a) * (J a * O * P) * A := by
        simp only [mul_assoc]
      _ = P * LinearMap.adjoint (J a) * (O * J a * P) * A := by rw [hj]
      _ = (P * LinearMap.adjoint (J a) * O) * J a * P * A := by
        simp only [mul_assoc]
      _ = (P * O * LinearMap.adjoint (J a)) * J a * P * A := by rw [hjadj]
      _ = O * P * LinearMap.adjoint (J a) * J a * P * A := by
        exact congrArg (fun X : Operator H => X * LinearMap.adjoint (J a) *
          J a * P * A) hOP.eq.symm
      _ = _ := by simp only [mul_assoc]
  have hlossRight :
      P * ((O * P * A) * (LinearMap.adjoint (J a) * J a)) =
        O * P * ((P * A) * (LinearMap.adjoint (J a) * J a)) := by
    calc
      _ = P * O * P * A * (LinearMap.adjoint (J a) * J a) := by
        simp only [mul_assoc]
      _ = O * P * P * A * (LinearMap.adjoint (J a) * J a) := by
        exact congrArg (fun X : Operator H => X * P * A *
          (LinearMap.adjoint (J a) * J a)) hOP.eq.symm
      _ = _ := by simp only [mul_assoc]
  rw [lindbladJumpTerm_apply, lindbladJumpTerm_apply]
  simp only [mul_sub, mul_add, mul_smul_comm]
  rw [hgain, hlossLeft, hlossRight]

theorem lindbladDissipator_good_input_left [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P) :
    P * lindbladDissipator J (O * P * A) =
      O * P * lindbladDissipator J (P * A) := by
  rw [lindbladDissipator_apply, lindbladDissipator_apply, Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  exact jumpTerm_good_input_left J O P A hprotected hO hP hOP a

private theorem jumpTerm_good_input_right [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hPA : Commute P A) (hOA : Commute O A) (a : ι) :
    (1 - P) * lindbladJumpTerm (J a) (O * P * A) =
      (1 - P) * lindbladJumpTerm (J a) (P * A) * O := by
  have hjadj := hprotected.projector_mul_observable_adjoint hO hP a
  have hOPA : O * P * A = P * A * O := by
    calc
      O * P * A = P * O * A := congrArg (fun X : Operator H => X * A) hOP.eq
      _ = P * (O * A) := mul_assoc _ _ _
      _ = P * (A * O) := by rw [hOA.eq]
      _ = P * A * O := (mul_assoc _ _ _).symm
  have hOPA' : O * (P * A) = P * (A * O) := by
    simpa only [mul_assoc] using hOPA
  have hPAOJ : P * A * O * LinearMap.adjoint (J a) =
      P * A * LinearMap.adjoint (J a) * O := by
    calc
      _ = A * P * O * LinearMap.adjoint (J a) := by
        exact congrArg (fun X : Operator H => X * O * LinearMap.adjoint (J a)) hPA.eq
      _ = A * (P * O * LinearMap.adjoint (J a)) := by simp only [mul_assoc]
      _ = A * (P * LinearMap.adjoint (J a) * O) := by rw [hjadj]
      _ = A * P * LinearMap.adjoint (J a) * O := by simp only [mul_assoc]
      _ = P * A * LinearMap.adjoint (J a) * O := by
        exact congrArg (fun X : Operator H => X * LinearMap.adjoint (J a) * O)
          hPA.eq.symm
  have hOPAJ : O * (P * (A * LinearMap.adjoint (J a))) =
      P * (A * (LinearMap.adjoint (J a) * O)) := by
    calc
      _ = (O * P * A) * LinearMap.adjoint (J a) := by simp only [mul_assoc]
      _ = (P * A * O) * LinearMap.adjoint (J a) := by rw [hOPA]
      _ = P * A * LinearMap.adjoint (J a) * O := hPAOJ
      _ = _ := by simp only [mul_assoc]
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP.isIdempotentElem.eq, sub_self]
  have hgain :
      (1 - P) * (J a * (O * P * A) * LinearMap.adjoint (J a)) =
        (1 - P) * (J a * (P * A) * LinearMap.adjoint (J a)) * O := by
    simp only [mul_assoc]
    rw [hOPAJ]
  have hlossLeft :
      (1 - P) * ((LinearMap.adjoint (J a) * J a) * (O * P * A)) =
        (1 - P) * ((LinearMap.adjoint (J a) * J a) * (P * A)) * O := by
    simp only [mul_assoc]
    rw [hOPA']
  have hlossRightLeft :
      (1 - P) * ((O * P * A) * (LinearMap.adjoint (J a) * J a)) = 0 := by
    calc
      _ = (1 - P) * ((O * P) * (A * (LinearMap.adjoint (J a) * J a))) := by
        simp only [mul_assoc]
      _ = (1 - P) * ((P * O) * (A * (LinearMap.adjoint (J a) * J a))) := by
        rw [hOP.eq]
      _ = ((1 - P) * P) * (O * (A * (LinearMap.adjoint (J a) * J a))) := by
        simp only [mul_assoc]
      _ = 0 := by rw [hQP, zero_mul]
  have hlossRightBase :
      (1 - P) * ((P * A) * (LinearMap.adjoint (J a) * J a)) = 0 := by
    calc
      _ = ((1 - P) * P) * (A * (LinearMap.adjoint (J a) * J a)) := by
        simp only [mul_assoc]
      _ = 0 := by rw [hQP, zero_mul]
  have hlossRightRight :
      (1 - P) * ((P * A) * (LinearMap.adjoint (J a) * J a)) * O = 0 := by
    rw [hlossRightBase, zero_mul]
  rw [lindbladJumpTerm_apply, lindbladJumpTerm_apply]
  simp only [mul_sub, mul_add, mul_smul_comm]
  rw [hgain, hlossLeft, hlossRightLeft]
  simp only [add_zero, hlossRightBase]
  conv_rhs => rw [sub_mul, smul_mul_assoc]

theorem lindbladDissipator_good_input_right [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hPA : Commute P A) (hOA : Commute O A) :
    (1 - P) * lindbladDissipator J (O * P * A) =
      (1 - P) * lindbladDissipator J (P * A) * O := by
  rw [lindbladDissipator_apply, lindbladDissipator_apply, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  exact jumpTerm_good_input_right J O P A hprotected hO hP hOP hPA hOA a

/-! ## The four independent block bounds -/

private theorem commute_one_sub_right {A P : Operator H} (h : Commute A P) :
    Commute A (1 - P) := by
  rw [Commute]
  change A * (1 - P) = (1 - P) * A
  rw [mul_sub, sub_mul, h.eq]
  simp

private theorem traceNorm_mul_projection_le
    (P A : Operator H) (hP : IsStarProjection P) :
    traceNorm (P * A) ≤ traceNorm A := by
  calc
    traceNorm (P * A) ≤ operatorNorm P * traceNorm A :=
      traceNorm_mul_left_le P A
    _ ≤ 1 * traceNorm A :=
      mul_le_mul_of_nonneg_right (operatorNorm_projection_le P hP)
        (traceNorm_nonneg A)
    _ = traceNorm A := one_mul _

private theorem traceNorm_mul_complement_le
    (P A : Operator H) (hP : IsStarProjection P) :
    traceNorm ((1 - P) * A) ≤ traceNorm A :=
  traceNorm_mul_projection_le (1 - P) A hP.one_sub

private theorem projectedTail_eq_complement_mul_of_commute
    (P A : Operator H) (hP : IsStarProjection P) (hPA : Commute P A) :
    projectedTail P A = (1 - P) * A := by
  rw [projectedTail]
  have hQ : Commute (1 - P) A := commute_one_sub_right hPA.symm |>.symm
  calc
    (1 - P) * A * (1 - P) = (1 - P) * (A * (1 - P)) := mul_assoc _ _ _
    _ = (1 - P) * ((1 - P) * A) := by rw [hQ.eq.symm]
    _ = ((1 - P) * (1 - P)) * A := (mul_assoc _ _ _).symm
    _ = (1 - P) * A := by rw [hP.one_sub.isIdempotentElem.eq]

private theorem traceNorm_complement_mul_density_eq_badMass [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H)
    (hPrho : Commute P rho.toOperator) :
    traceNorm ((1 - P) * rho.toOperator) =
      Complex.re (LinearMap.trace ℂ H ((1 - P) * rho.toOperator)) := by
  calc
    traceNorm ((1 - P) * rho.toOperator) =
        traceNorm (projectedTail P rho.toOperator) := by
      rw [projectedTail_eq_complement_mul_of_commute P rho.toOperator hP hPrho]
    _ = Complex.re (LinearMap.trace ℂ H ((1 - P) * rho.toOperator)) :=
      rho.traceNorm_projectedTail_eq_complementTrace P hP

private theorem tail_symmetric
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H)
    (hPrho : Commute P rho.toOperator) :
    ((1 - P) * rho.toOperator).IsSymmetric := by
  rw [← projectedTail_eq_complement_mul_of_commute P rho.toOperator hP hPrho]
  exact (projectedTail_positive P rho.toOperator hP rho.positive).isSymmetric

private theorem observable_tail_symmetric
    (O P : Operator H) (hO : O.IsSymmetric) (hP : IsStarProjection P)
    (hOP : Commute O P)
    (rho : DensityOperator H) (hOrho : Commute O rho.toOperator)
    (hPrho : Commute P rho.toOperator) :
    (O * (1 - P) * rho.toOperator).IsSymmetric := by
  have htailComm : Commute O ((1 - P) * rho.toOperator) :=
    (commute_one_sub_right hOP).mul_right hOrho
  have htailSym : ((1 - P) * rho.toOperator).IsSymmetric :=
    tail_symmetric P hP rho hPrho
  intro x y
  change inner ℂ (O (((1 - P) * rho.toOperator) x)) y =
    inner ℂ x (O (((1 - P) * rho.toOperator) y))
  calc
    inner ℂ (O (((1 - P) * rho.toOperator) x)) y =
        inner ℂ (((1 - P) * rho.toOperator) x) (O y) := hO _ _
    _ = inner ℂ x (((1 - P) * rho.toOperator) (O y)) := htailSym _ _
    _ = inner ℂ x (O (((1 - P) * rho.toOperator) y)) := by
      apply congrArg (inner ℂ x)
      exact LinearMap.congr_fun htailComm.eq.symm y

private theorem lindbladDissipator_good_input_eq_negative_tail [Fintype ι]
    (J : ι → Operator H) (P : Operator H) (rho : DensityOperator H)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    lindbladDissipator J (P * rho.toOperator) =
      -lindbladDissipator J ((1 - P) * rho.toOperator) := by
  have hrhoSplit :
      rho.toOperator = P * rho.toOperator + (1 - P) * rho.toOperator := by
    noncomm_ring
  have hsum :
      lindbladDissipator J (P * rho.toOperator) +
        lindbladDissipator J ((1 - P) * rho.toOperator) = 0 := by
    rw [← map_add, ← hrhoSplit, hstationary]
  exact eq_neg_of_add_eq_zero_left hsum

/-- CLBT's first good-input block is rewritten onto the Gibbs tail. -/
theorem clbtGeneratorBlockOne_eq_negative_tail [Fintype ι]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    clbtGeneratorBlockOne (lindbladDissipator J) O P rho.toOperator =
      -(O * P * lindbladDissipator J ((1 - P) * rho.toOperator)) := by
  rw [clbtGeneratorBlockOne,
    lindbladDissipator_good_input_left J O P rho.toOperator hprotected hO hP hOP,
    lindbladDissipator_good_input_eq_negative_tail J P rho hstationary]
  simp

/-- CLBT's second good-input block is rewritten onto the Gibbs tail. -/
theorem clbtGeneratorBlockTwo_eq_negative_tail [Fintype ι]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator =
      -((1 - P) * lindbladDissipator J ((1 - P) * rho.toOperator) * O) := by
  rw [clbtGeneratorBlockTwo,
    lindbladDissipator_good_input_right J O P rho.toOperator hprotected hO hP hOP
      hPrho hOrho,
    lindbladDissipator_good_input_eq_negative_tail J P rho hstationary]
  simp

/-- The Gibbs weight outside the protected projector. -/
def clbtGibbsTailMass (P : Operator H) (rho : DensityOperator H) : Real :=
  Complex.re (LinearMap.trace ℂ H ((1 - P) * rho.toOperator))

private theorem clbtGibbsTailMass_nonneg [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H) :
    0 ≤ clbtGibbsTailMass P rho :=
  re_trace_complement_nonneg P rho.toOperator hP rho.positive

/-- Each CLBT block has the common source-local upper bound; block one. -/
theorem clbtGeneratorBlockOne_bound [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0)
    (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockOne (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  let T : Operator H := (1 - P) * rho.toOperator
  have hTsym : T.IsSymmetric := tail_symmetric P hP rho hPrho
  have hTnorm : traceNorm T = clbtGibbsTailMass P rho :=
    traceNorm_complement_mul_density_eq_badMass P hP rho hPrho
  have hLnonneg : 0 ≤ lindbladDissipatorNorm J :=
    selfAdjointTraceNormOneToOne_nonneg (lindbladDissipator J)
  have hmass : 0 ≤ clbtGibbsTailMass P rho :=
    clbtGibbsTailMass_nonneg P hP rho
  rw [clbtGeneratorBlockOne_eq_negative_tail J O P rho hprotected hO hP hOP
    hstationary, traceNorm_neg]
  calc
    traceNorm (O * P * lindbladDissipator J T) ≤
        operatorNorm O * traceNorm (P * lindbladDissipator J T) := by
      simpa only [mul_assoc] using
        traceNorm_mul_left_le O (P * lindbladDissipator J T)
    _ ≤ operatorNorm O * traceNorm (lindbladDissipator J T) :=
      mul_le_mul_of_nonneg_left
        (traceNorm_mul_projection_le P (lindbladDissipator J T) hP)
        (operatorNorm_nonneg O)
    _ ≤ operatorNorm O *
        (lindbladDissipatorNorm J * traceNorm T) :=
      mul_le_mul_of_nonneg_left
        (traceNorm_apply_le_selfAdjointTraceNormOneToOne
          (lindbladDissipator J) T hTsym)
        (operatorNorm_nonneg O)
    _ = operatorNorm O *
        (lindbladDissipatorNorm J * clbtGibbsTailMass P rho) := by rw [hTnorm]
    _ ≤ 2 * (lindbladDissipatorNorm J * clbtGibbsTailMass P rho) :=
      mul_le_mul_of_nonneg_right hOnorm (mul_nonneg hLnonneg hmass)
    _ = 2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring

/-- Each CLBT block has the common source-local upper bound; block two. -/
theorem clbtGeneratorBlockTwo_bound [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0)
    (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  let T : Operator H := (1 - P) * rho.toOperator
  have hTsym : T.IsSymmetric := tail_symmetric P hP rho hPrho
  have hTnorm : traceNorm T = clbtGibbsTailMass P rho :=
    traceNorm_complement_mul_density_eq_badMass P hP rho hPrho
  have hLnonneg : 0 ≤ lindbladDissipatorNorm J :=
    selfAdjointTraceNormOneToOne_nonneg (lindbladDissipator J)
  have hmass : 0 ≤ clbtGibbsTailMass P rho :=
    clbtGibbsTailMass_nonneg P hP rho
  rw [clbtGeneratorBlockTwo_eq_negative_tail J O P rho hprotected hO hP hOP
    hOrho hPrho hstationary, traceNorm_neg]
  calc
    traceNorm ((1 - P) * lindbladDissipator J T * O) ≤
        operatorNorm O * traceNorm ((1 - P) * lindbladDissipator J T) :=
      traceNorm_mul_right_le ((1 - P) * lindbladDissipator J T) O
    _ ≤ operatorNorm O * traceNorm (lindbladDissipator J T) :=
      mul_le_mul_of_nonneg_left
        (traceNorm_mul_complement_le P (lindbladDissipator J T) hP)
        (operatorNorm_nonneg O)
    _ ≤ operatorNorm O *
        (lindbladDissipatorNorm J * traceNorm T) :=
      mul_le_mul_of_nonneg_left
        (traceNorm_apply_le_selfAdjointTraceNormOneToOne
          (lindbladDissipator J) T hTsym)
        (operatorNorm_nonneg O)
    _ = operatorNorm O *
        (lindbladDissipatorNorm J * clbtGibbsTailMass P rho) := by rw [hTnorm]
    _ ≤ 2 * (lindbladDissipatorNorm J * clbtGibbsTailMass P rho) :=
      mul_le_mul_of_nonneg_right hOnorm (mul_nonneg hLnonneg hmass)
    _ = 2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring

/-- Each CLBT block has the common source-local upper bound; block three. -/
theorem clbtGeneratorBlockThree_bound [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hO : O.IsSymmetric) (hP : IsStarProjection P)
    (hOP : Commute O P) (hOrho : Commute O rho.toOperator)
    (hPrho : Commute P rho.toOperator) (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockThree (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  let T : Operator H := (1 - P) * rho.toOperator
  let B : Operator H := O * (1 - P) * rho.toOperator
  have hBsym : B.IsSymmetric :=
    observable_tail_symmetric O P hO hP hOP rho hOrho hPrho
  have hTnorm : traceNorm T = clbtGibbsTailMass P rho :=
    traceNorm_complement_mul_density_eq_badMass P hP rho hPrho
  have hBnorm : traceNorm B ≤ operatorNorm O * traceNorm T := by
    simpa only [B, T, mul_assoc] using traceNorm_mul_left_le O T
  have hLnonneg : 0 ≤ lindbladDissipatorNorm J :=
    selfAdjointTraceNormOneToOne_nonneg (lindbladDissipator J)
  have hmass : 0 ≤ clbtGibbsTailMass P rho :=
    clbtGibbsTailMass_nonneg P hP rho
  change traceNorm (P * lindbladDissipator J B) ≤ _
  calc
    traceNorm (P * lindbladDissipator J B) ≤
        traceNorm (lindbladDissipator J B) :=
      traceNorm_mul_projection_le P (lindbladDissipator J B) hP
    _ ≤ lindbladDissipatorNorm J * traceNorm B :=
      traceNorm_apply_le_selfAdjointTraceNormOneToOne
        (lindbladDissipator J) B hBsym
    _ ≤ lindbladDissipatorNorm J * (operatorNorm O * traceNorm T) :=
      mul_le_mul_of_nonneg_left hBnorm hLnonneg
    _ = lindbladDissipatorNorm J *
        (operatorNorm O * clbtGibbsTailMass P rho) := by rw [hTnorm]
    _ ≤ lindbladDissipatorNorm J * (2 * clbtGibbsTailMass P rho) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hOnorm hmass) hLnonneg
    _ = 2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring

/-- Each CLBT block has the common source-local upper bound; block four. -/
theorem clbtGeneratorBlockFour_bound [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hO : O.IsSymmetric) (hP : IsStarProjection P)
    (hOP : Commute O P) (hOrho : Commute O rho.toOperator)
    (hPrho : Commute P rho.toOperator) (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockFour (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  let T : Operator H := (1 - P) * rho.toOperator
  let B : Operator H := O * (1 - P) * rho.toOperator
  have hBsym : B.IsSymmetric :=
    observable_tail_symmetric O P hO hP hOP rho hOrho hPrho
  have hTnorm : traceNorm T = clbtGibbsTailMass P rho :=
    traceNorm_complement_mul_density_eq_badMass P hP rho hPrho
  have hBnorm : traceNorm B ≤ operatorNorm O * traceNorm T := by
    simpa only [B, T, mul_assoc] using traceNorm_mul_left_le O T
  have hLnonneg : 0 ≤ lindbladDissipatorNorm J :=
    selfAdjointTraceNormOneToOne_nonneg (lindbladDissipator J)
  have hmass : 0 ≤ clbtGibbsTailMass P rho :=
    clbtGibbsTailMass_nonneg P hP rho
  change traceNorm ((1 - P) * lindbladDissipator J B) ≤ _
  calc
    traceNorm ((1 - P) * lindbladDissipator J B) ≤
        traceNorm (lindbladDissipator J B) :=
      traceNorm_mul_complement_le P (lindbladDissipator J B) hP
    _ ≤ lindbladDissipatorNorm J * traceNorm B :=
      traceNorm_apply_le_selfAdjointTraceNormOneToOne
        (lindbladDissipator J) B hBsym
    _ ≤ lindbladDissipatorNorm J * (operatorNorm O * traceNorm T) :=
      mul_le_mul_of_nonneg_left hBnorm hLnonneg
    _ = lindbladDissipatorNorm J *
        (operatorNorm O * clbtGibbsTailMass P rho) := by rw [hTnorm]
    _ ≤ lindbladDissipatorNorm J * (2 * clbtGibbsTailMass P rho) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hOnorm hmass) hLnonneg
    _ = 2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring

/-! ## The source constant-eight estimate -/

private theorem traceNorm_four_sum_le_four_mul
    (A₁ A₂ A₃ A₄ : Operator H) (b : Real)
    (h₁ : traceNorm A₁ ≤ b) (h₂ : traceNorm A₂ ≤ b)
    (h₃ : traceNorm A₃ ≤ b) (h₄ : traceNorm A₄ ≤ b) :
    traceNorm (A₁ + A₂ + A₃ + A₄) ≤ 4 * b := by
  calc
    traceNorm (A₁ + A₂ + A₃ + A₄) ≤
        traceNorm (A₁ + A₂ + A₃) + traceNorm A₄ :=
      traceNorm_add_le _ _
    _ ≤ (traceNorm (A₁ + A₂) + traceNorm A₃) + traceNorm A₄ :=
      add_le_add (traceNorm_add_le (A₁ + A₂) A₃) (le_refl (traceNorm A₄))
    _ ≤ ((traceNorm A₁ + traceNorm A₂) + traceNorm A₃) + traceNorm A₄ :=
      add_le_add
        (add_le_add (traceNorm_add_le A₁ A₂) (le_refl (traceNorm A₃)))
        (le_refl (traceNorm A₄))
    _ ≤ b + b + b + b :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = 4 * b := by ring

/--
CLBT10 proof part II: jump protection and Gibbs stationarity bound the local
generator on the encoded observable by eight times the dissipator norm and the
Gibbs weight outside the protected space.

The constant `8` is obtained below by combining the four independent block
bounds; it is not part of any assumption.
-/
theorem clbtFourBlockGeneratorEstimate [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0)
    (hOnorm : operatorNorm O ≤ 2) :
    traceNorm (lindbladDissipator J (O * rho.toOperator)) ≤
      8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  rw [clbtGenerator_eq_sum_four_blocks]
  calc
    traceNorm
        (clbtGeneratorBlockOne (lindbladDissipator J) O P rho.toOperator +
          clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator +
          clbtGeneratorBlockThree (lindbladDissipator J) O P rho.toOperator +
          clbtGeneratorBlockFour (lindbladDissipator J) O P rho.toOperator) ≤
        4 * (2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho) :=
      traceNorm_four_sum_le_four_mul _ _ _ _ _
        (clbtGeneratorBlockOne_bound J O P rho hprotected hO hP hOP hPrho
          hstationary hOnorm)
        (clbtGeneratorBlockTwo_bound J O P rho hprotected hO hP hOP hOrho hPrho
          hstationary hOnorm)
        (clbtGeneratorBlockThree_bound J O P rho hO hP hOP hOrho hPrho hOnorm)
        (clbtGeneratorBlockFour_bound J O P rho hO hP hOP hOrho hPrho hOnorm)
    _ = 8 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring

end

end QEC.Semantics
