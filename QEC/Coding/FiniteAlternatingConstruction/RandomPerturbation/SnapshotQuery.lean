import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExactRealProgram
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Events

/-! # Counted formation of the actual query-point coordinates

The same arithmetic evaluator forms lambda*(J/2)+p before a triangle query.
-/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def snapshotCoordinateExpr (lambda : ℝ) (j : Fin 3) : RealExpr :=
  .add (.mul (.constant lambda) (.mul (.constant (1/2)) (.vertex 0 j))) (.vertex 1 j)

noncomputable def pointSnapshotQuery (lambda : ℝ) (a b : Space) : Space × ℕ :=
  let q0 := (snapshotCoordinateExpr lambda 0).run ![a,b,0] 0 0
  let q1 := (snapshotCoordinateExpr lambda 1).run ![a,b,0] 0 0
  let q2 := (snapshotCoordinateExpr lambda 2).run ![a,b,0] 0 0
  (WithLp.toLp 2 ![q0.1,q1.1,q2.1],q0.2+q1.2+q2.2+3)

theorem pointSnapshotQuery_value (lambda : ℝ) (a b : Space) :
    (pointSnapshotQuery lambda a b).1 = lambda • ((1/2 : ℝ) • a)+b := by
  ext j
  fin_cases j <;> simp only [pointSnapshotQuery,RealExpr.run_value,snapshotCoordinateExpr,RealExpr.eval]
  all_goals rfl

theorem snapshotCoordinateExpr_cost (lambda : ℝ) (j : Fin 3) :
    (snapshotCoordinateExpr lambda j).cost = 7 := rfl

theorem pointSnapshotQuery_cost_le (lambda : ℝ) (a b : Space) :
    (pointSnapshotQuery lambda a b).2 ≤ 45 := by
  have h0 := (snapshotCoordinateExpr lambda 0).run_cost_le ![a,b,0] 0 0
  have h1 := (snapshotCoordinateExpr lambda 1).run_cost_le ![a,b,0] 0 0
  have h2 := (snapshotCoordinateExpr lambda 2).run_cost_le ![a,b,0] 0 0
  rw [snapshotCoordinateExpr_cost] at h0 h1 h2
  dsimp only [pointSnapshotQuery]
  omega

noncomputable def triangleSnapshotQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) : (Fin 3 → Space) × ℕ :=
  let q0 := pointSnapshotQuery lambda (J (triangleVertex P a.val 0)) (p (eventVertex P J r e a 0))
  let q1 := pointSnapshotQuery lambda (J (triangleVertex P a.val 1)) (p (eventVertex P J r e a 1))
  let q2 := pointSnapshotQuery lambda (J (triangleVertex P a.val 2)) (p (eventVertex P J r e a 2))
  (![q0.1,q1.1,q2.1],q0.2+q1.2+q2.2+3)

theorem triangleSnapshotQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) :
    (triangleSnapshotQuery P J r lambda e a p).1 =
      fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i))+p (eventVertex P J r e a i) := by
  funext i
  fin_cases i <;> simp [triangleSnapshotQuery,pointSnapshotQuery_value]

theorem triangleSnapshotQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (e : Event P J r) (a : e.val)
    (p : eventSupport P J r e → Space) : (triangleSnapshotQuery P J r lambda e a p).2 ≤ 138 := by
  have h0 := pointSnapshotQuery_cost_le lambda (J (triangleVertex P a.val 0)) (p (eventVertex P J r e a 0))
  have h1 := pointSnapshotQuery_cost_le lambda (J (triangleVertex P a.val 1)) (p (eventVertex P J r e a 1))
  have h2 := pointSnapshotQuery_cost_le lambda (J (triangleVertex P a.val 2)) (p (eventVertex P J r e a 2))
  dsimp only [triangleSnapshotQuery]
  omega

noncomputable def centerSnapshotQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) : Space × ℕ :=
  pointSnapshotQuery lambda (J (.x (P.faceX (eventAnchor P J r e).1))) (gridPoint K g)

theorem centerSnapshotQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) :
    (centerSnapshotQuery P J r lambda K e g).1 = eventCenter P J r lambda K e g := by
  rw [centerSnapshotQuery,pointSnapshotQuery_value]
  rfl

theorem centerSnapshotQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) :
    (centerSnapshotQuery P J r lambda K e g).2 ≤ 45 := pointSnapshotQuery_cost_le _ _ _

end QEC.Coding.BDL26RandomPerturbation
