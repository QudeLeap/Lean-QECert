import QEC.Coding.ReedSolomon.Punctured
import QEC.Distillation.PrimeQuditProtocol.CubicCSS

/-!
# The concrete `p = 11` KT19 Reed--Solomon cubic-row bridge

This module realizes the finite Reed--Solomon/CSS slice used by the KT19
prime-qudit construction at the literal parameters `p = 11`, `l = 4`, and
`k = 2`.  The rows are the source's displayed polynomials, evaluated and
punctured on the actual retained coordinate set.  Their carrier equalities,
cubic identities, and transversal conclusion are proved from the evaluation
codes rather than supplied as a parameter bundle.
-/

noncomputable section

namespace QEC.Distillation.KT19P11ReedSolomonCubicBridge

open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators

private local instance p11Prime : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private local instance p11NeZero : NeZero 11 := ⟨by norm_num⟩

noncomputable local instance p11PrimeQuditRegisterLabelFintype
    (Site : Type*) [Fintype Site] : Fintype (PrimeQuditRegisterLabel 11 Site) :=
  Fintype.ofFinite _

/-- The two logical polynomials displayed in the KT19 `p = 11` example. -/
def p11LogicalPolynomial : Fin 2 → Polynomial (ZMod 11)
  | 0 => Polynomial.X - 1
  | 1 => -Polynomial.X

/-- The two stabilizer polynomials displayed in the KT19 `p = 11` example. -/
def p11StabilizerPolynomial : Fin 2 → Polynomial (ZMod 11)
  | 0 => Polynomial.X * (Polynomial.X - 1)
  | 1 => Polynomial.X ^ 2 * (Polynomial.X - 1)

/-- Evaluation followed by restriction to the literal retained coordinate set. -/
def p11RetainedEvaluation (polynomial : Polynomial (ZMod 11)) :
    Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  restrictKept 11 2 (evaluationMap 11 polynomial)

/-- The retained logical rows. -/
def p11LogicalRow : Fin 2 → Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  fun index => p11RetainedEvaluation (p11LogicalPolynomial index)

/-- The retained stabilizer rows. -/
def p11StabilizerRow : Fin 2 → Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  fun index => p11RetainedEvaluation (p11StabilizerPolynomial index)

/-- All four displayed rows, with the logical and stabilizer tags retained. -/
def p11Row : Fin 2 ⊕ Fin 2 → Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  Sum.elim p11LogicalRow p11StabilizerRow

private theorem p11Row_eq_retainedEvaluation (index : Fin 2 ⊕ Fin 2) :
    p11Row index = p11RetainedEvaluation
      (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial index) := by
  rcases index with index | index <;> rfl

/-- The actual span of the two retained stabilizer rows. -/
def p11StabilizerCarrier : Submodule (ZMod 11) (Word (ZMod 11) (KeptPunctureLocation 11 2)) :=
  Submodule.span (ZMod 11) (Set.range p11StabilizerRow)

/-- The actual span of all displayed retained rows. -/
def p11RowCarrier : Submodule (ZMod 11) (Word (ZMod 11) (KeptPunctureLocation 11 2)) :=
  Submodule.span (ZMod 11) (Set.range p11Row)

private theorem p11_logical_degreeLT (index : Fin 2) :
    p11LogicalPolynomial index ∈ Polynomial.degreeLT (ZMod 11) 4 := by
  fin_cases index
  · rw [p11LogicalPolynomial.eq_def, Polynomial.mem_degreeLT]
    calc
      (Polynomial.X - 1 : Polynomial (ZMod 11)).degree ≤
          max Polynomial.X.degree (1 : Polynomial (ZMod 11)).degree :=
        Polynomial.degree_sub_le _ _
      _ < (4 : WithBot ℕ) := by norm_num
  · rw [p11LogicalPolynomial.eq_def, Polynomial.mem_degreeLT]
    simpa using (show (Polynomial.X : Polynomial (ZMod 11)).degree < (4 : WithBot ℕ) by
      norm_num)

private theorem p11_stabilizer_degreeLT (index : Fin 2) :
    p11StabilizerPolynomial index ∈ Polynomial.degreeLT (ZMod 11) 4 := by
  have hXdegree : (Polynomial.X : Polynomial (ZMod 11)).degree = (1 : WithBot ℕ) := by
    norm_num
  have hXsubDegree :
      ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree ≤ (1 : WithBot ℕ) := by
    calc
      _ ≤ max (Polynomial.X : Polynomial (ZMod 11)).degree
          (1 : Polynomial (ZMod 11)).degree := Polynomial.degree_sub_le _ _
      _ = (1 : WithBot ℕ) := by norm_num
  have hXXdegree :
      ((Polynomial.X : Polynomial (ZMod 11)) *
        (Polynomial.X : Polynomial (ZMod 11))).degree ≤ (1 : WithBot ℕ) + 1 := by
    calc
      _ ≤ (Polynomial.X : Polynomial (ZMod 11)).degree +
          (Polynomial.X : Polynomial (ZMod 11)).degree := Polynomial.degree_mul_le _ _
      _ = (1 : WithBot ℕ) + 1 := by rw [hXdegree]
  fin_cases index
  · rw [p11StabilizerPolynomial.eq_def, Polynomial.mem_degreeLT]
    calc
      (Polynomial.X * (Polynomial.X - 1) : Polynomial (ZMod 11)).degree ≤
          (Polynomial.X : Polynomial (ZMod 11)).degree +
            ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree :=
        Polynomial.degree_mul_le _ _
      _ = (1 : WithBot ℕ) + ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree := by
        rw [hXdegree]
      _ ≤ (1 : WithBot ℕ) + 1 :=
        add_le_add_right hXsubDegree (1 : WithBot ℕ)
      _ < (4 : WithBot ℕ) := by norm_num
  · rw [p11StabilizerPolynomial.eq_def, pow_two, Polynomial.mem_degreeLT]
    calc
      ((Polynomial.X * Polynomial.X) * (Polynomial.X - 1) : Polynomial (ZMod 11)).degree ≤
          ((Polynomial.X : Polynomial (ZMod 11)) *
              (Polynomial.X : Polynomial (ZMod 11))).degree +
            ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree :=
        Polynomial.degree_mul_le _ _
      _ ≤ ((1 : WithBot ℕ) + 1) +
          ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree :=
        add_le_add_left hXXdegree ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree
      _ ≤ ((1 : WithBot ℕ) + 1) + 1 :=
        add_le_add_right hXsubDegree ((1 : WithBot ℕ) + 1)
      _ < (4 : WithBot ℕ) := by norm_num

private theorem p11_row_degreeLT (index : Fin 2 ⊕ Fin 2) :
    (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial index) ∈
      Polynomial.degreeLT (ZMod 11) 4 := by
  rcases index with index | index
  · exact p11_logical_degreeLT index
  · exact p11_stabilizer_degreeLT index

private theorem p11_selected_point_eq_zero_or_one
    (point : SelectedPunctureLocation 11 2) : point.1 = 0 ∨ point.1 = 1 := by
  have hlt : point.1.val < 2 := by
    simpa [selectedPunctureLocations] using (Finset.mem_filter.mp point.2).2
  interval_cases hvalue : point.1.val
  · left
    calc
      point.1 = (point.1.val : ZMod 11) := (ZMod.natCast_zmod_val point.1).symm
      _ = 0 := by simp [hvalue]
  · right
    calc
      point.1 = (point.1.val : ZMod 11) := (ZMod.natCast_zmod_val point.1).symm
      _ = 1 := by simp [hvalue]

private noncomputable def p11SelectedPunctureEquivFin :
    SelectedPunctureLocation 11 2 ≃ Fin 2 := by
  refine
    { toFun := fun point => ⟨point.1.val, (Finset.mem_filter.mp point.2).2⟩
      invFun := fun index => ⟨(index.1 : ZMod 11), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (index.2.trans_le (by norm_num : 2 ≤ 11))]
        exact index.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Subtype.ext
    exact ZMod.natCast_zmod_val point.1
  · intro index
    apply Fin.ext
    change ((index.1 : ZMod 11).val) = index.1
    exact ZMod.val_natCast_of_lt (index.2.trans_le (by norm_num : 2 ≤ 11))

private theorem p11_stabilizer_restrictSelected_zero (index : Fin 2) :
    restrictSelected 11 2 (evaluationMap 11 (p11StabilizerPolynomial index)) = 0 := by
  ext point
  rcases p11_selected_point_eq_zero_or_one point with hpoint | hpoint
  · fin_cases index <;>
      simp [p11StabilizerPolynomial, evaluationMap, hpoint]
  · fin_cases index <;>
      simp [p11StabilizerPolynomial, evaluationMap, hpoint]

private theorem p11_stabilizer_mem_shortened (index : Fin 2) :
    p11StabilizerRow index ∈ (shortenedReedSolomonCode 11 4 2).carrier := by
  apply (mem_shortenedReedSolomonCode _).2
  refine ⟨evaluationLinearMap 11 4 ⟨p11StabilizerPolynomial index,
      p11_stabilizer_degreeLT index⟩, ?_, ?_, ?_⟩
  · exact evaluation_mem_reedSolomonCode 11 4 _
  · exact p11_stabilizer_restrictSelected_zero index
  · rfl

private theorem p11_logical_mem_punctured (index : Fin 2) :
    p11LogicalRow index ∈ (puncturedReedSolomonCode 11 4 2).carrier := by
  apply (mem_puncturedReedSolomonCode _).2
  refine ⟨evaluationLinearMap 11 4 ⟨p11LogicalPolynomial index,
      p11_logical_degreeLT index⟩, ?_, ?_⟩
  · exact evaluation_mem_reedSolomonCode 11 4 _
  · rfl

private theorem p11_stabilizerCarrier_le_shortened :
    p11StabilizerCarrier ≤ (shortenedReedSolomonCode 11 4 2).carrier := by
  rw [p11StabilizerCarrier]
  apply Submodule.span_le.2
  rintro word ⟨index, rfl⟩
  exact p11_stabilizer_mem_shortened index

private theorem p11_rowCarrier_le_punctured :
    p11RowCarrier ≤ (puncturedReedSolomonCode 11 4 2).carrier := by
  rw [p11RowCarrier]
  apply Submodule.span_le.2
  rintro word ⟨index, rfl⟩
  rcases index with index | index
  · exact p11_logical_mem_punctured index
  · exact (shortenedReedSolomonCode_le_puncturedReedSolomonCode 11 4 2)
      (p11_stabilizer_mem_shortened index)

private def p11CoefficientPolynomial (u h : Fin 2 → ZMod 11) : Polynomial (ZMod 11) :=
  (∑ index : Fin 2, u index • p11LogicalPolynomial index) +
    ∑ index : Fin 2, h index • p11StabilizerPolynomial index

private theorem p11_coefficient_degreeLT (u h : Fin 2 → ZMod 11) :
    p11CoefficientPolynomial u h ∈ Polynomial.degreeLT (ZMod 11) 4 := by
  apply Submodule.add_mem
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod 11) 4) fun index _ =>
      Submodule.smul_mem _ _ (p11_logical_degreeLT index)
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod 11) 4) fun index _ =>
      Submodule.smul_mem _ _ (p11_stabilizer_degreeLT index)

private theorem p11_coefficient_restrictKept (u h : Fin 2 → ZMod 11) :
    p11RetainedEvaluation (p11CoefficientPolynomial u h) =
      (∑ index : Fin 2, u index • p11LogicalRow index) +
        ∑ index : Fin 2, h index • p11StabilizerRow index := by
  ext point
  simp [p11CoefficientPolynomial, p11RetainedEvaluation, evaluationMap,
    p11LogicalRow, p11StabilizerRow, Finset.sum_apply]

private theorem p11_coefficient_eq_zero_of_restrictKept_zero
    (u h : Fin 2 → ZMod 11)
    (hzero : (∑ index : Fin 2, u index • p11LogicalRow index) +
        ∑ index : Fin 2, h index • p11StabilizerRow index = 0) :
    p11CoefficientPolynomial u h = 0 := by
  have hreduced : p11RetainedEvaluation (p11CoefficientPolynomial u h) = 0 := by
    rw [p11_coefficient_restrictKept]
    exact hzero
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (keptPunctureLocations 11 2)
  · exact (Polynomial.mem_degreeLT.mp (p11_coefficient_degreeLT u h)).trans_le (by
      norm_num [keptPunctureLocations_card])
  · exact WithBot.bot_lt_coe (keptPunctureLocations 11 2).card
  · intro point hpoint
    have hvalue := congrFun hreduced ⟨point, hpoint⟩
    simpa [p11RetainedEvaluation, evaluationMap] using hvalue

private theorem p11_coefficients_zero_of_polynomial_zero (u h : Fin 2 → ZMod 11)
    (hzero : p11CoefficientPolynomial u h = 0) : u = 0 ∧ h = 0 := by
  have hconstant := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 0) hzero
  have hlinear := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 1) hzero
  have hquadratic := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 2) hzero
  have hcubic := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 3) hzero
  norm_num [p11CoefficientPolynomial, p11LogicalPolynomial.eq_def,
    p11StabilizerPolynomial.eq_def, Fin.sum_univ_succ, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_X,
    Polynomial.coeff_X_pow, Polynomial.coeff_one] at hconstant hlinear hquadratic hcubic
  ring_nf at hconstant hlinear hquadratic hcubic
  norm_num [Polynomial.coeff_add, Polynomial.coeff_neg, Polynomial.coeff_X_pow]
    at hconstant hlinear hquadratic hcubic
  have hu0 : u 0 = 0 := hconstant
  have hh1 : h 1 = 0 := hcubic
  have hh0 : h 0 = 0 := by
    simpa [hh1] using hquadratic
  have hu1 : u 1 = 0 := by
    simpa [hu0, hh0] using hlinear
  constructor
  · funext index
    fin_cases index
    · simpa using hu0
    · simpa using hu1
  · funext index
    fin_cases index
    · simpa using hh0
    · simpa using hh1

private theorem p11_rows_independent (u h : Fin 2 → ZMod 11) :
    (∑ index : Fin 2, u index • p11LogicalRow index) +
      ∑ index : Fin 2, h index • p11StabilizerRow index = 0 → u = 0 ∧ h = 0 := by
  intro hzero
  exact p11_coefficients_zero_of_polynomial_zero u h
    (p11_coefficient_eq_zero_of_restrictKept_zero u h hzero)

private theorem p11_stabilizer_rows_linearIndependent :
    LinearIndependent (ZMod 11) p11StabilizerRow := by
  rw [Fintype.linearIndependent_iff]
  intro h hzero index
  have hboth := p11_rows_independent 0 h (by simpa using hzero)
  simpa using congrFun hboth.2 index

private theorem p11_rows_linearIndependent :
    LinearIndependent (ZMod 11) p11Row := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hzero index
  let u : Fin 2 → ZMod 11 := fun logical => coefficient (Sum.inl logical)
  let h : Fin 2 → ZMod 11 := fun stabilizer => coefficient (Sum.inr stabilizer)
  have hsplit :
      (∑ logical : Fin 2, u logical • p11LogicalRow logical) +
        ∑ stabilizer : Fin 2, h stabilizer • p11StabilizerRow stabilizer = 0 := by
    simpa [u, h, p11Row, Fintype.sum_sum_type] using hzero
  rcases p11_rows_independent u h hsplit with ⟨hu, hh⟩
  rcases index with index | index
  · simpa [u] using congrFun hu index
  · simpa [h] using congrFun hh index

private theorem p11_stabilizerCarrier_finrank :
    Module.finrank (ZMod 11) p11StabilizerCarrier = 2 := by
  rw [p11StabilizerCarrier]
  simpa using finrank_span_eq_card p11_stabilizer_rows_linearIndependent

private theorem p11_rowCarrier_finrank :
    Module.finrank (ZMod 11) p11RowCarrier = 4 := by
  rw [p11RowCarrier]
  simpa using finrank_span_eq_card p11_rows_linearIndependent

/-- The literal stabilizer-row span is the actual shortened `RS_4` code. -/
theorem p11_stabilizerCarrier_eq_shortenedReedSolomon :
    p11StabilizerCarrier = (shortenedReedSolomonCode 11 4 2).carrier := by
  apply Submodule.eq_of_le_of_finrank_eq p11_stabilizerCarrier_le_shortened
  rw [p11_stabilizerCarrier_finrank]
  simpa [Dimension_eq_finrank_carrier] using
    (shortenedReedSolomonCode_dimension 11 4 2 (by norm_num) (by norm_num) (by norm_num)).symm

/-- The literal four-row span is the actual punctured `RS_4` code. -/
theorem p11_rowCarrier_eq_puncturedReedSolomon :
    p11RowCarrier = (puncturedReedSolomonCode 11 4 2).carrier := by
  apply Submodule.eq_of_le_of_finrank_eq p11_rowCarrier_le_punctured
  rw [p11_rowCarrier_finrank]
  simpa [Dimension_eq_finrank_carrier] using
    (puncturedReedSolomonCode_dimension 11 4 2 (by norm_num) (by norm_num)).symm

/-- The displayed row carrier is the exact complementary shortened-code dual. -/
theorem p11_rowCarrier_eq_dual_shortenedComplement :
    p11RowCarrier = (shortenedReedSolomonCode 11 7 2).dual.carrier := by
  rw [p11_rowCarrier_eq_puncturedReedSolomon]
  symm
  exact shortenedReedSolomonCode_dual_eq_punctured 11 4 2 (by norm_num [Admissible])

/-- The retained all-ones word belongs to the concrete four-row carrier. -/
theorem p11_retainedAllOnes_mem_rowCarrier :
    (1 : Word (ZMod 11) (KeptPunctureLocation 11 2)) ∈ p11RowCarrier := by
  have hzero : p11LogicalRow 0 ∈ p11RowCarrier := by
    rw [p11RowCarrier]
    exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
  have hone : p11LogicalRow 1 ∈ p11RowCarrier := by
    rw [p11RowCarrier]
    exact Submodule.subset_span ⟨Sum.inl 1, rfl⟩
  have hcombination : -p11LogicalRow 0 - p11LogicalRow 1 ∈ p11RowCarrier :=
    p11RowCarrier.sub_mem (p11RowCarrier.neg_mem hzero) hone
  convert hcombination using 1
  ext point
  simp [p11LogicalRow, p11RetainedEvaluation, p11LogicalPolynomial, evaluationMap]

private theorem p11_full_cubic_zero (left middle right : Fin 2 ⊕ Fin 2) :
    cubicPairing 11
      (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
      (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
      (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right)) = 0 := by
  let leftBounded : Polynomial.degreeLT (ZMod 11) 4 :=
    ⟨Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left, p11_row_degreeLT left⟩
  let middleBounded : Polynomial.degreeLT (ZMod 11) 4 :=
    ⟨Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle, p11_row_degreeLT middle⟩
  let rightBounded : Polynomial.degreeLT (ZMod 11) 4 :=
    ⟨Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right, p11_row_degreeLT right⟩
  have hleft : evaluationLinearMap 11 4 leftBounded ∈ (reedSolomonCode 11 4).carrier :=
    evaluation_mem_reedSolomonCode 11 4 leftBounded
  have hmiddle : evaluationLinearMap 11 4 middleBounded ∈ (reedSolomonCode 11 4).carrier :=
    evaluation_mem_reedSolomonCode 11 4 middleBounded
  have hright : evaluationLinearMap 11 4 rightBounded ∈ (reedSolomonCode 11 4).carrier :=
    evaluation_mem_reedSolomonCode 11 4 rightBounded
  have hproduct : coordinatewiseProduct (evaluationLinearMap 11 4 leftBounded)
      (evaluationLinearMap 11 4 middleBounded) ∈ (reedSolomonCode 11 4).dual.carrier := by
    apply reedSolomonCode_product_le_dual 11 4 (by norm_num)
    rw [coordinatewiseProductCode]
    exact Submodule.subset_span ⟨evaluationLinearMap 11 4 leftBounded, hleft,
      evaluationLinearMap 11 4 middleBounded, hmiddle, rfl⟩
  have horthogonal := ((reedSolomonCode 11 4).mem_dual _).1 hproduct
    (evaluationLinearMap 11 4 rightBounded) hright
  simpa [leftBounded, middleBounded, rightBounded, cubicPairing, wordPairing_apply, dotProduct,
    coordinatewiseProduct, evaluationLinearMap_apply, evaluationMap] using horthogonal

private theorem p11_retained_cubic_add_selected_cubic_eq_full
    (left middle right : Word (ZMod 11) (ZMod 11)) :
    cubicPairing 11 (restrictKept 11 2 left) (restrictKept 11 2 middle)
      (restrictKept 11 2 right) +
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) = cubicPairing 11 left middle right := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun point : ZMod 11 => point ∈ selectedPunctureLocations 11 2)
    (fun point => left point * middle point * right point)
  let complementKept :
      {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2} ≃
        KeptPunctureLocation 11 2 :=
    { toFun := fun point => ⟨point.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, point.2⟩⟩
      invFun := fun point => ⟨point.1, (Finset.mem_sdiff.mp point.2).2⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change (∑ point : KeptPunctureLocation 11 2,
      left point.1 * middle point.1 * right point.1) +
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) =
    ∑ point : ZMod 11, left point * middle point * right point
  have hequiv :
      (∑ point : {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) =
        ∑ point : KeptPunctureLocation 11 2, left point.1 * middle point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  calc
    (∑ point : KeptPunctureLocation 11 2, left point.1 * middle point.1 * right point.1) +
        (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
          left point.1 * middle point.1 * right point.1) =
        (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
          left point.1 * middle point.1 * right point.1) +
          (∑ point : KeptPunctureLocation 11 2,
            left point.1 * middle point.1 * right point.1) := by ac_rfl
    _ = (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
          left point.1 * middle point.1 * right point.1) +
          (∑ point : {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2},
            left point.1 * middle point.1 * right point.1) := by rw [hequiv]
    _ = ∑ point : ZMod 11, left point * middle point * right point := hsplit

private theorem p11_cubic_restrict_eq_full_of_selected_sum_zero
    (left middle right : Word (ZMod 11) (ZMod 11))
    (hselectedSum :
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) = 0) :
    cubicPairing 11 (restrictKept 11 2 left) (restrictKept 11 2 middle)
      (restrictKept 11 2 right) = cubicPairing 11 left middle right := by
  have hsplit := p11_retained_cubic_add_selected_cubic_eq_full left middle right
  rw [hselectedSum, add_zero] at hsplit
  exact hsplit

private theorem p11_selected_cubic_sum_zero_of_restrictSelected_zero
    (left middle right : Word (ZMod 11) (ZMod 11))
    (hselected : restrictSelected 11 2 left = 0) :
    (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
      left point.1 * middle point.1 * right point.1) = 0 := by
  apply Finset.sum_eq_zero
  intro point _
  have hpoint : left point.1 = 0 := by
    simpa using congrFun hselected
      (⟨point.1, point.2⟩ : SelectedPunctureLocation 11 2)
  rw [hpoint]
  simp

private theorem p11_stabilizer_triple_zero (left middle right : Fin 2 ⊕ Fin 2)
    (hcontains : (∃ index, left = Sum.inr index) ∨ (∃ index, middle = Sum.inr index) ∨
      (∃ index, right = Sum.inr index)) :
    cubicPairing 11 (p11Row left) (p11Row middle) (p11Row right) = 0 := by
  rcases hcontains with ⟨index, rfl⟩ | ⟨index, rfl⟩ | ⟨index, rfl⟩
  · rw [p11Row_eq_retainedEvaluation (Sum.inr index),
      p11Row_eq_retainedEvaluation middle,
      p11Row_eq_retainedEvaluation right]
    simp only [p11RetainedEvaluation, Sum.elim_inr]
    calc
      _ = cubicPairing 11 (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right)) :=
        p11_cubic_restrict_eq_full_of_selected_sum_zero
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right))
          (p11_selected_cubic_sum_zero_of_restrictSelected_zero _ _ _
            (p11_stabilizer_restrictSelected_zero index))
      _ = 0 := p11_full_cubic_zero (Sum.inr index) middle right
  · rw [p11Row_eq_retainedEvaluation left,
      p11Row_eq_retainedEvaluation (Sum.inr index),
      p11Row_eq_retainedEvaluation right]
    simp only [p11RetainedEvaluation, Sum.elim_inr]
    calc
      _ = cubicPairing 11
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right)) :=
        p11_cubic_restrict_eq_full_of_selected_sum_zero
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (p11_selected_cubic_sum_zero_of_restrictSelected_zero
                (evaluationMap 11 (p11StabilizerPolynomial index))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right))
                (p11_stabilizer_restrictSelected_zero index)))
      _ = 0 := p11_full_cubic_zero left (Sum.inr index) right
  · rw [p11Row_eq_retainedEvaluation left,
      p11Row_eq_retainedEvaluation middle,
      p11Row_eq_retainedEvaluation (Sum.inr index)]
    simp only [p11RetainedEvaluation, Sum.elim_inr]
    calc
      _ = cubicPairing 11
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (p11StabilizerPolynomial index)) :=
        p11_cubic_restrict_eq_full_of_selected_sum_zero
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (p11_selected_cubic_sum_zero_of_restrictSelected_zero
                (evaluationMap 11 (p11StabilizerPolynomial index))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
                (p11_stabilizer_restrictSelected_zero index)))
      _ = 0 := p11_full_cubic_zero left middle (Sum.inr index)

private theorem p11_logical_offDiagonal_zero (left middle right : Fin 2)
    (hnot : ¬ (left = middle ∧ middle = right)) :
    cubicPairing 11 (p11LogicalRow left) (p11LogicalRow middle) (p11LogicalRow right) = 0 := by
  have hselected :
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        evaluationMap 11 (p11LogicalPolynomial left) point.1 *
          evaluationMap 11 (p11LogicalPolynomial middle) point.1 *
            evaluationMap 11 (p11LogicalPolynomial right) point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    rcases p11_selected_point_eq_zero_or_one
      (⟨point.1, point.2⟩ : SelectedPunctureLocation 11 2) with hpoint | hpoint
    · rw [hpoint]
      fin_cases left <;> fin_cases middle <;> fin_cases right <;>
        simp_all [p11LogicalPolynomial, evaluationMap]
    · rw [hpoint]
      fin_cases left <;> fin_cases middle <;> fin_cases right <;>
        simp_all [p11LogicalPolynomial, evaluationMap]
  have htransport := p11_cubic_restrict_eq_full_of_selected_sum_zero
    (evaluationMap 11 (p11LogicalPolynomial left))
    (evaluationMap 11 (p11LogicalPolynomial middle))
    (evaluationMap 11 (p11LogicalPolynomial right)) hselected
  simpa [p11LogicalRow, p11RetainedEvaluation] using htransport.trans
    (p11_full_cubic_zero (Sum.inl left) (Sum.inl middle) (Sum.inl right))

private theorem p11_logical_selected_cube_sum (index : Fin 2) :
    (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
      evaluationMap 11 (p11LogicalPolynomial index) point.1 *
        evaluationMap 11 (p11LogicalPolynomial index) point.1 *
          evaluationMap 11 (p11LogicalPolynomial index) point.1) = -1 := by
  calc
    (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
      evaluationMap 11 (p11LogicalPolynomial index) point.1 *
        evaluationMap 11 (p11LogicalPolynomial index) point.1 *
          evaluationMap 11 (p11LogicalPolynomial index) point.1) =
        ∑ coordinate : Fin 2,
          evaluationMap 11 (p11LogicalPolynomial index)
              (p11SelectedPunctureEquivFin.symm coordinate).1 *
            evaluationMap 11 (p11LogicalPolynomial index)
              (p11SelectedPunctureEquivFin.symm coordinate).1 *
              evaluationMap 11 (p11LogicalPolynomial index)
                (p11SelectedPunctureEquivFin.symm coordinate).1 :=
      Fintype.sum_equiv p11SelectedPunctureEquivFin _ _ (fun point => by simp)
    _ = -1 := by
      fin_cases index <;>
        simp [p11SelectedPunctureEquivFin, p11LogicalPolynomial, evaluationMap,
          Fin.sum_univ_succ]

/-- The actual cubic-row family induced by the four p=11 KT19 rows. -/
noncomputable def p11CubicRowFamily :
    CubicRowFamily 11 (Fin 2) (Fin 2) (KeptPunctureLocation 11 2) where
  logicalRow := p11LogicalRow
  stabilizerRow := p11StabilizerRow
  rowIndependent := p11_rows_independent
  stabilizerTriple_zero := p11_stabilizer_triple_zero
  logicalTriple_offDiagonal_zero := p11_logical_offDiagonal_zero

/-- Each displayed logical row has retained cubic coefficient one. -/
theorem p11_epsilon (index : Fin 2) : p11CubicRowFamily.epsilon index = 1 := by
  change cubicPairing 11 (p11LogicalRow index) (p11LogicalRow index)
    (p11LogicalRow index) = 1
  have hsplit := p11_retained_cubic_add_selected_cubic_eq_full
    (evaluationMap 11 (p11LogicalPolynomial index))
    (evaluationMap 11 (p11LogicalPolynomial index))
    (evaluationMap 11 (p11LogicalPolynomial index))
  have hfullLogical : cubicPairing 11
      (evaluationMap 11 (p11LogicalPolynomial index))
      (evaluationMap 11 (p11LogicalPolynomial index))
      (evaluationMap 11 (p11LogicalPolynomial index)) = 0 := by
    simpa only [Sum.elim_inl] using
      (p11_full_cubic_zero (Sum.inl index) (Sum.inl index) (Sum.inl index))
  have hselected := p11_logical_selected_cube_sum index
  change cubicPairing 11 (restrictKept 11 2 (evaluationMap 11 (p11LogicalPolynomial index)))
    (restrictKept 11 2 (evaluationMap 11 (p11LogicalPolynomial index)))
    (restrictKept 11 2 (evaluationMap 11 (p11LogicalPolynomial index))) = 1
  rw [hselected, hfullLogical] at hsplit
  linear_combination hsplit

private theorem p11_primeAtLeastFive : PrimeAtLeastFive 11 := by
  constructor <;> norm_num

/-- The actual transversal physical `U_{1,3}` implements the constructed
inverse logical `U_{1,3}` on the p=11 KT19 cubic CSS code. -/
theorem p11_physicalU13_implements_inverse :
    p11CubicRowFamily.encodedCode.ImplementsLogicalGate
      p11CubicRowFamily.physicalU13 p11CubicRowFamily.logicalInverseU13 :=
  CubicRowFamily.physicalU13_implements_inverseLogicalU13 p11CubicRowFamily
    p11_primeAtLeastFive

end QEC.Distillation.KT19P11ReedSolomonCubicBridge
