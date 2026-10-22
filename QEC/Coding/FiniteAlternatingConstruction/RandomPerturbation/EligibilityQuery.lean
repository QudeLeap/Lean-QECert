import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ColorQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventQuery
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedDedup

/-! # Counted arithmetic eligibility tests for four input triangle labels -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

noncomputable def triangleLabelEqQuery (P : TannerSquarePresentation) (a b : Triangle P) : Bool × ℕ :=
  let A := indexQuery a (triangleInputList P)
  let B := indexQuery b (triangleInputList P)
  (decide (A.1 = B.1),A.2+B.2+1)

theorem triangleLabelEqQuery_correct (P : TannerSquarePresentation) (a b : Triangle P) :
    (triangleLabelEqQuery P a b).1 = true ↔ a = b := by
  classical
  simp only [triangleLabelEqQuery,indexQuery_value,triangleInputList_index,decide_eq_true_eq]
  exact (triangleKey_injective P).eq_iff

theorem triangleLabelEqQuery_cost_le (P : TannerSquarePresentation) (a b : Triangle P) :
    (triangleLabelEqQuery P a b).2 ≤ 2*Fintype.card (Triangle P)+1 := by
  classical
  have ha := indexQuery_cost_le a (triangleInputList P)
  have hb := indexQuery_cost_le b (triangleInputList P)
  rw [triangleInputList_length] at ha hb
  dsimp only [triangleLabelEqQuery]
  omega

noncomputable def colorMatchQuery (P : TannerSquarePresentation) (a b : Triangle P) : Bool × ℕ :=
  let A := triangleColorQuery P a
  let B := triangleColorQuery P b
  let q := listAllQuery (fun i : Fin 3 => (decide (A.1 i = B.1 i),1)) [0,1,2]
  (q.1,A.2+B.2+q.2)

theorem colorMatchQuery_correct (P : TannerSquarePresentation) (a b : Triangle P) :
    (colorMatchQuery P a b).1 = true ↔ triangleColor P a = triangleColor P b := by
  simp only [colorMatchQuery,listAllQuery_correct,triangleColorQuery_value,decide_eq_true_eq]
  constructor
  · intro h
    funext i
    fin_cases i <;> exact h _ (by simp)
  · intro h i _
    exact congrFun h i

theorem colorMatchQuery_cost_le (P : TannerSquarePresentation) (a b : Triangle P) :
    (colorMatchQuery P a b).2 ≤ 6*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6)+6 := by
  have ha := triangleColorQuery_cost_le P a
  have hb := triangleColorQuery_cost_le P b
  have hq := listAllQuery_cost_le (fun i : Fin 3 =>
    (decide ((triangleColorQuery P a).1 i = (triangleColorQuery P b).1 i),1)) [0,1,2] 1
    (by intro i hi; exact le_rfl)
  norm_num only [List.length_cons,List.length_nil] at hq
  dsimp only [colorMatchQuery]
  nlinarith

noncomputable def anchorCloseProgram : RealTest :=
  let d := subExpr (smulExpr (.constant (1/2)) centerExpr)
    (smulExpr (.constant (1/2)) (vertexExpr 0))
  .le (dotExpr d d) (.mul .radius .radius)

noncomputable def anchorCloseQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (a b : Triangle P) : Bool × ℕ :=
  anchorCloseProgram.run (fun _ => J (.x (P.faceX b.1))) (J (.x (P.faceX a.1))) radius

theorem anchorCloseQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    {radius : ℝ} (hr : 0 ≤ radius) (a b : Triangle P) :
    (anchorCloseQuery P J radius a b).1 = true ↔
      dist (oldAnchor P J a) (oldAnchor P J b) ≤ radius := by
  let A := J (.x (P.faceX a.1))
  let B := J (.x (P.faceX b.1))
  let d := subExpr (smulExpr (.constant (1/2)) centerExpr)
    (smulExpr (.constant (1/2)) (vertexExpr 0))
  have hd (j : Fin 3) : (d j).eval (fun _ => B) A radius = ((1/2 : ℝ) • A-(1/2 : ℝ) • B) j := rfl
  have hdd := dotExpr_eval d d (fun _ => B) A radius _ _ hd hd
  rw [real_inner_self_eq_norm_sq] at hdd
  rw [anchorCloseQuery,RealTest.run_value]
  change (RealTest.le (dotExpr d d) (.mul .radius .radius)).eval (fun _ => B) A radius = true ↔ _
  simp only [RealTest.eval,RealExpr.eval,hdd,decide_eq_true_eq]
  change ‖(1/2 : ℝ) • A-(1/2 : ℝ) • B‖^2 ≤ radius*radius ↔ _
  rw [dist_eq_norm]
  change _ ↔ ‖(1/2 : ℝ) • A-(1/2 : ℝ) • B‖ ≤ radius
  constructor
  · intro h; nlinarith [norm_nonneg ((1/2 : ℝ) • A-(1/2 : ℝ) • B)]
  · intro h; nlinarith [norm_nonneg ((1/2 : ℝ) • A-(1/2 : ℝ) • B)]

theorem anchorCloseProgram_cost_le : anchorCloseProgram.cost ≤ 1000 := by decide

theorem anchorCloseQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (a b : Triangle P) : (anchorCloseQuery P J radius a b).2 ≤ 2000 := by
  have h := anchorCloseProgram.run_cost_le (fun _ => J (.x (P.faceX b.1)))
    (J (.x (P.faceX a.1))) radius
  have hc := anchorCloseProgram_cost_le
  dsimp only [anchorCloseQuery]
  omega

noncomputable def eligiblePairQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (a b : Triangle P) : Bool × ℕ :=
  let color := colorMatchQuery P a b
  let close := anchorCloseQuery P J r a b
  (color.1 && close.1,color.2+close.2+1)

theorem eligiblePairQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (a b : Triangle P) :
    (eligiblePairQuery P J r a b).1 = true ↔
      triangleColor P a = triangleColor P b ∧ dist (oldAnchor P J a) (oldAnchor P J b) ≤ r := by
  simp only [eligiblePairQuery,Bool.and_eq_true,colorMatchQuery_correct,anchorCloseQuery_correct P J hr]

theorem eligiblePairQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (a b : Triangle P) :
    (eligiblePairQuery P J r a b).2 ≤ 6*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6)+2007 := by
  have hc := colorMatchQuery_cost_le P a b
  have hd := anchorCloseQuery_cost_le P J r a b
  dsimp only [eligiblePairQuery]
  omega

end QEC.Coding.BDL26RandomPerturbation
