import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ActualExecutionCost

/-! # Expected actual operation cost in the source's ideal continuous primitive model -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

/-- An explicit fixed-degree polynomial, with only the fixed numerical grid parameter K. -/
def executionOperationBudget (n v K : ℕ) : ℕ :=
  eventUniverseBudget n+54*v+n^4*(stateQueryBudget n v K+1)+
    (n^4*(stateQueryBudget n v K+1)+378+32*v)*n^4

theorem geometric_expected_operations_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T
      ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
        (executionOperationBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P))
          ((6*p.m+2)*p.lambda) : ℕ) := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  let n := Fintype.card (Triangle P)
  let K := (6*p.m+2)*p.lambda
  let A : ℕ := eventUniverseBudget n+54*Fintype.card (Vertex P)+n^4*(stateQueryBudget n (Fintype.card (Vertex P)) K+1)
  let B : ℕ := n^4*(stateQueryBudget n (Fintype.card (Vertex P)) K+1)+378+32*Fintype.card (Vertex P)
  have hsteps := geometric_expected_steps_le P J p hJ hv
  calc
    _ ≤ ∫⁻ T, (A : ℝ≥0∞)+(B : ℝ≥0∞)*totalSteps
        (eventSupport P J (anchorRadius p.m)) (eventBad P J (anchorRadius p.m) p.lambda K) T
        ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)) := by
      apply lintegral_mono_ae
      filter_upwards [geometric_halts_and_avoids_ae P J p hJ hv] with T hT
      exact actualExecutionCost_le P J (by positivity) p.lambda K T hT.1
    _ = (A : ℝ≥0∞)+(B : ℝ≥0∞)*(∫⁻ T, totalSteps
        (eventSupport P J (anchorRadius p.m)) (eventBad P J (anchorRadius p.m) p.lambda K) T
        ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) := by
      rw [lintegral_add_left measurable_const]
      rw [lintegral_const_mul' (μ := tableLaw
        (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) (B : ℝ≥0∞)
        (fun T : Table (X := fun _ : Vertex P => Space) =>
          totalSteps (eventSupport P J (anchorRadius p.m))
            (eventBad P J (anchorRadius p.m) p.lambda K) T) (by simp)]
      simp
    _ ≤ (A : ℝ≥0∞)+(B : ℝ≥0∞)*(n^4 : ℕ) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hsteps)
    _ = _ := by
      dsimp only [A,B,n,K,executionOperationBudget]
      push_cast
      ring

/-- The actual typed vertex cardinality, independent of its derived Fintype instance. -/
def vertexSumEquiv (P : TannerSquarePresentation) : Vertex P ≃ P.X ⊕ (P.Q ⊕ P.Z) where
  toFun
    | .x x => .inl x
    | .q q => .inr (.inl q)
    | .z z => .inr (.inr z)
  invFun
    | .inl x => .x x
    | .inr (.inl q) => .q q
    | .inr (.inr z) => .z z
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; rcases v with x|(q|z) <;> rfl

theorem vertex_card (P : TannerSquarePresentation) :
    Fintype.card (Vertex P) = Fintype.card P.X+Fintype.card P.Q+Fintype.card P.Z := by
  rw [Fintype.card_congr (vertexSumEquiv P),Fintype.card_sum,Fintype.card_sum]
  omega

/-- Genuine admissibility roots and incidence bounds control both source input arrays. -/
theorem operation_input_size_le_qubits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (hv : BoundedValence P) : Fintype.card (Vertex P)+Fintype.card (Triangle P) ≤ 65*Fintype.card P.Q := by
  rw [vertex_card]
  exact input_labels_le_qubits P A hv

/-- The coefficient depends only on the jointly fixed net parameter. -/
def operationConstant (K : ℕ) : ℕ := 1000000+2*(fullQueryBudget 0 K+9+24*(2*K+1)^3)+540

theorem executionOperationBudget_polynomial (n v K : ℕ) :
    executionOperationBudget n v K ≤ operationConstant K*(n+v+1)^10 := by
  let s := n+v+1
  let a := fullQueryBudget 0 K+9+24*(2*K+1)^3
  have hs : 0 < s := by dsimp [s]; omega
  have hn : n+1 ≤ s := by dsimp [s]; omega
  have hnv : v ≤ s := by dsimp [s]; omega
  have hc : stateQueryBudget n v K+1 ≤ a*s := by
    let b := fullQueryBudget 0 K
    let g := 24*(2*K+1)^3
    have hs1 : 1 ≤ s := by omega
    have hn0 : n ≤ s := by omega
    have hb := Nat.mul_le_mul_left (b+1) hs1
    simp only [Nat.mul_one] at hb
    have h8 := Nat.mul_le_mul_left 8 hn0
    have hg := Nat.mul_le_mul_left g hnv
    calc
      _ = (b+1)+8*n+g*v := by
        dsimp [stateQueryBudget,fullQueryBudget,b,g]
        ring
      _ ≤ (b+1)*s+8*s+g*s := Nat.add_le_add (Nat.add_le_add hb h8) hg
      _ = a*s := by dsimp [a,b,g]; ring
  have hn4 : n^4 ≤ s^4 := Nat.pow_le_pow_left (by dsimp [s]; omega) 4
  have hp4 : s^4 ≤ s^10 := Nat.pow_le_pow_right hs (by norm_num)
  have hp5 : s^5 ≤ s^10 := Nat.pow_le_pow_right hs (by norm_num)
  have hp9 : s^9 ≤ s^10 := Nat.pow_le_pow_right hs (by norm_num)
  have hp1 : s ≤ s^10 := by simpa using Nat.pow_le_pow_right hs (show 1 ≤ 10 by norm_num)
  have hquery : n^4*(stateQueryBudget n v K+1) ≤ a*s^5 := by
    calc
      _ ≤ s^4*(a*s) := Nat.mul_le_mul hn4 hc
      _ = _ := by ring
  have hrepeat : n^4*(stateQueryBudget n v K+1)*n^4 ≤ a*s^9 := by
    calc
      _ ≤ (a*s^5)*s^4 := Nat.mul_le_mul hquery hn4
      _ = _ := by ring
  have hu : eventUniverseBudget n ≤ 1000000*s^10 :=
    (eventUniverseBudget_polynomial n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 10))
  have hquery' := hquery.trans (Nat.mul_le_mul_left a hp5)
  have hrepeat' := hrepeat.trans (Nat.mul_le_mul_left a hp9)
  have hvertices := Nat.mul_le_mul_left 54 (hnv.trans hp1)
  have hrefresh := Nat.mul_le_mul_left 378 (hn4.trans hp4)
  have hrowrefresh : 32*v*n^4 ≤ 32*s^10 := by
    calc
      _ ≤ 32*s*s^4 := Nat.mul_le_mul (Nat.mul_le_mul_left 32 hnv) hn4
      _ = 32*s^5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left 32 hp5
  have hsum := Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu hvertices) hquery')
      hrepeat') hrefresh) hrowrefresh
  calc
    _ = eventUniverseBudget n+54*v+n^4*(stateQueryBudget n v K+1)+
        n^4*(stateQueryBudget n v K+1)*n^4+378*n^4+32*v*n^4 := by
      dsimp only [executionOperationBudget]
      ring
    _ ≤ 1000000*s^10+54*s^10+a*s^10+a*s^10+378*s^10+32*s^10 := hsum
    _ = (1000000+2*a+464)*s^10 := by ring
    _ ≤ _ := by
      change (1000000+2*a+464)*s^10 ≤ (1000000+2*a+540)*s^10
      exact Nat.mul_le_mul_right _ (by omega)

/-- All preprocessing and executed primitives are polynomial in the actual source qubit size. -/
theorem geometric_expected_operations_le_qubits (P : TannerSquarePresentation) (J : Vertex P → Space)
    (A : TannerSquareAdmissible P) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T
      ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
        (operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 : ℕ) := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hsize := operation_input_size_le_qubits P A hv
  have hpoly := executionOperationBudget_polynomial (Fintype.card (Triangle P))
    (Fintype.card (Vertex P)) ((6*p.m+2)*p.lambda)
  have hb : executionOperationBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P))
      ((6*p.m+2)*p.lambda) ≤ operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 := by
    apply hpoly.trans
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 10
  exact (geometric_expected_operations_le P J p hJ hv).trans ((Nat.cast_le (α := ℝ≥0∞)).mpr hb)

end QEC.Coding.BDL26RandomPerturbation
