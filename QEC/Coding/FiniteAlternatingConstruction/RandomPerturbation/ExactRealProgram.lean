import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.TriangleDecision

/-! # Counted exact-real arithmetic program for a closed triangle query

Every input read, arithmetic operation and real comparison has unit cost.
The program contains no geometric predicate oracle. Division uses the total
real operation; zero denominators are harmless in discarded singular branches.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators

inductive RealExpr where
  | constant (x : ℝ)
  | vertex (i j : Fin 3)
  | center (j : Fin 3)
  | radius
  | add (a b : RealExpr)
  | sub (a b : RealExpr)
  | mul (a b : RealExpr)
  | div (a b : RealExpr)
  | min (a b : RealExpr)
  | max (a b : RealExpr)

noncomputable def RealExpr.eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealExpr → ℝ
  | .constant x => x
  | .vertex i j => a i j
  | .center j => z j
  | .radius => ρ
  | .add x y => x.eval a z ρ+y.eval a z ρ
  | .sub x y => x.eval a z ρ-y.eval a z ρ
  | .mul x y => x.eval a z ρ*y.eval a z ρ
  | .div x y => x.eval a z ρ/y.eval a z ρ
  | .min x y => Min.min (x.eval a z ρ) (y.eval a z ρ)
  | .max x y => Max.max (x.eval a z ρ) (y.eval a z ρ)

def RealExpr.cost : RealExpr → ℕ
  | .constant _ | .vertex _ _ | .center _ | .radius => 1
  | .add x y | .sub x y | .mul x y | .div x y | .min x y | .max x y =>
    1+x.cost+y.cost

inductive RealTest where
  | le (a b : RealExpr)
  | ne (a b : RealExpr)
  | both (a b : RealTest)
  | either (a b : RealTest)

noncomputable def RealTest.eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealTest → Bool
  | .le x y => decide (x.eval a z ρ ≤ y.eval a z ρ)
  | .ne x y => decide (x.eval a z ρ ≠ y.eval a z ρ)
  | .both x y => x.eval a z ρ && y.eval a z ρ
  | .either x y => x.eval a z ρ || y.eval a z ρ

def RealTest.cost : RealTest → ℕ
  | .le x y | .ne x y => 1+x.cost+y.cost
  | .both x y | .either x y => 1+x.cost+y.cost

abbrev VecExpr := Fin 3 → RealExpr

def dotExpr (b c : VecExpr) : RealExpr :=
  .add (.mul (b 0) (c 0)) (.add (.mul (b 1) (c 1)) (.mul (b 2) (c 2)))
def subExpr (b c : VecExpr) : VecExpr := fun j => .sub (b j) (c j)
def addExpr (b c : VecExpr) : VecExpr := fun j => .add (b j) (c j)
def smulExpr (x : RealExpr) (b : VecExpr) : VecExpr := fun j => .mul x (b j)
def vertexExpr (i : Fin 3) : VecExpr := .vertex i
def centerExpr : VecExpr := .center

def segmentExpr (i j : Fin 3) : VecExpr :=
  let b := subExpr (vertexExpr j) (vertexExpr i)
  let d := subExpr centerExpr (vertexExpr i)
  let t := RealExpr.max (.constant 0) (.min (.constant 1) (.div (dotExpr d b) (dotExpr b b)))
  addExpr (vertexExpr i) (smulExpr t b)

def determinantExpr : RealExpr :=
  let b := subExpr (vertexExpr 1) (vertexExpr 0)
  let c := subExpr (vertexExpr 2) (vertexExpr 0)
  .sub (.mul (dotExpr b b) (dotExpr c c)) (.mul (dotExpr b c) (dotExpr b c))

def planeUExpr : RealExpr :=
  let b := subExpr (vertexExpr 1) (vertexExpr 0)
  let c := subExpr (vertexExpr 2) (vertexExpr 0)
  let d := subExpr centerExpr (vertexExpr 0)
  .div (.sub (.mul (dotExpr c c) (dotExpr d b)) (.mul (dotExpr b c) (dotExpr d c))) determinantExpr

def planeVExpr : RealExpr :=
  let b := subExpr (vertexExpr 1) (vertexExpr 0)
  let c := subExpr (vertexExpr 2) (vertexExpr 0)
  let d := subExpr centerExpr (vertexExpr 0)
  .div (.sub (.mul (dotExpr b b) (dotExpr d c)) (.mul (dotExpr b c) (dotExpr d b))) determinantExpr

def planeExpr : VecExpr := addExpr
  (addExpr (vertexExpr 0) (smulExpr planeUExpr (subExpr (vertexExpr 1) (vertexExpr 0))))
  (smulExpr planeVExpr (subExpr (vertexExpr 2) (vertexExpr 0)))

def distanceTest (b : VecExpr) : RealTest :=
  let d := subExpr centerExpr b
  .le (dotExpr d d) (.mul .radius .radius)

def triangleQueryProgram : RealTest :=
  .both (.le (.constant 0) .radius)
  (.either (distanceTest (vertexExpr 0))
  (.either (distanceTest (vertexExpr 1))
  (.either (distanceTest (vertexExpr 2))
  (.either (distanceTest (segmentExpr 0 1))
  (.either (distanceTest (segmentExpr 0 2))
  (.either (distanceTest (segmentExpr 1 2))
    (.both (.ne determinantExpr (.constant 0))
      (.both (.le (.constant 0) planeUExpr)
        (.both (.le (.constant 0) planeVExpr)
          (.both (.le (.add planeUExpr planeVExpr) (.constant 1)) (distanceTest planeExpr)))))))))))

-- Correctness is proved by the previously established seven-face coverage,
-- after coordinate evaluation identities; cost is the fixed program syntax.

theorem dotExpr_eval (b c : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x y : Space) (hx : ∀ j, (b j).eval a z ρ = x j)
    (hy : ∀ j, (c j).eval a z ρ = y j) :
    (dotExpr b c).eval a z ρ = inner ℝ x y := by
  simp only [dotExpr,RealExpr.eval,hx,hy,PiLp.inner_apply,Real.inner_apply,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

@[simp] theorem vertexExpr_eval (i j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (vertexExpr i j).eval a z ρ = a i j := rfl
@[simp] theorem centerExpr_eval (j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (centerExpr j).eval a z ρ = z j := rfl

theorem subExpr_eval (b c : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x y : Space) (hx : ∀ j, (b j).eval a z ρ = x j)
    (hy : ∀ j, (c j).eval a z ρ = y j) (j : Fin 3) :
    (subExpr b c j).eval a z ρ = (x-y) j := by
  change (b j).eval a z ρ-(c j).eval a z ρ = x j-y j
  rw [hx,hy]

theorem segmentExpr_eval (i j l : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (segmentExpr i j l).eval a z ρ = segmentPoint (a i) (a j) z l := by
  have hb := subExpr_eval (vertexExpr j) (vertexExpr i) a z ρ (a j) (a i)
    (fun _ => rfl) (fun _ => rfl)
  have hd := subExpr_eval centerExpr (vertexExpr i) a z ρ z (a i)
    (fun _ => rfl) (fun _ => rfl)
  have hdb := dotExpr_eval _ _ a z ρ _ _ hd hb
  have hbb := dotExpr_eval _ _ a z ρ _ _ hb hb
  rw [real_inner_self_eq_norm_sq] at hbb
  simp only [segmentExpr,addExpr,smulExpr,RealExpr.eval,hdb,hbb,vertexExpr_eval]
  change a i l+max 0 (min 1 (inner ℝ (z-a i) (a j-a i)/‖a j-a i‖^2))*(a j l-a i l) = _
  rfl

theorem determinantExpr_eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    determinantExpr.eval a z ρ = gramDet (a 1-a 0) (a 2-a 0) := by
  have hb := subExpr_eval (vertexExpr 1) (vertexExpr 0) a z ρ (a 1) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hc := subExpr_eval (vertexExpr 2) (vertexExpr 0) a z ρ (a 2) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hbb := dotExpr_eval _ _ a z ρ _ _ hb hb
  have hcc := dotExpr_eval _ _ a z ρ _ _ hc hc
  have hbc := dotExpr_eval _ _ a z ρ _ _ hb hc
  simp only [determinantExpr,RealExpr.eval,hbb,hcc,hbc,real_inner_self_eq_norm_sq,gramDet,pow_two]

-- These are syntax-size bounds, derived from this concrete program.
theorem triangleQueryProgram_cost_le : triangleQueryProgram.cost ≤ 100000 := by decide

theorem planeUExpr_eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    planeUExpr.eval a z ρ = planeU (a 1-a 0) (a 2-a 0) (z-a 0) := by
  have hb := subExpr_eval (vertexExpr 1) (vertexExpr 0) a z ρ (a 1) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hc := subExpr_eval (vertexExpr 2) (vertexExpr 0) a z ρ (a 2) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hd := subExpr_eval centerExpr (vertexExpr 0) a z ρ z (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hcc := dotExpr_eval _ _ a z ρ _ _ hc hc
  have hdb := dotExpr_eval _ _ a z ρ _ _ hd hb
  have hdc := dotExpr_eval _ _ a z ρ _ _ hd hc
  have hbc := dotExpr_eval _ _ a z ρ _ _ hb hc
  simp only [planeUExpr,RealExpr.eval,hcc,hdb,hdc,hbc,determinantExpr_eval,
    real_inner_self_eq_norm_sq,planeU]

theorem planeVExpr_eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    planeVExpr.eval a z ρ = planeV (a 1-a 0) (a 2-a 0) (z-a 0) := by
  have hb := subExpr_eval (vertexExpr 1) (vertexExpr 0) a z ρ (a 1) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hc := subExpr_eval (vertexExpr 2) (vertexExpr 0) a z ρ (a 2) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hd := subExpr_eval centerExpr (vertexExpr 0) a z ρ z (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hbb := dotExpr_eval _ _ a z ρ _ _ hb hb
  have hdb := dotExpr_eval _ _ a z ρ _ _ hd hb
  have hdc := dotExpr_eval _ _ a z ρ _ _ hd hc
  have hbc := dotExpr_eval _ _ a z ρ _ _ hb hc
  simp only [planeVExpr,RealExpr.eval,hbb,hdb,hdc,hbc,determinantExpr_eval,
    real_inner_self_eq_norm_sq,planeV]

theorem planeExpr_eval (j : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (planeExpr j).eval a z ρ = planePoint a z j := by
  simp only [planeExpr,addExpr,smulExpr,subExpr,RealExpr.eval,
    planeUExpr_eval,planeVExpr_eval,vertexExpr_eval]
  rfl

theorem distanceTest_eval (b : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x : Space) (hx : ∀ j, (b j).eval a z ρ = x j) (hρ : 0 ≤ ρ) :
    (distanceTest b).eval a z ρ = true ↔ dist z x ≤ ρ := by
  have hd := subExpr_eval centerExpr b a z ρ z x (fun _ => rfl) hx
  have hdd := dotExpr_eval _ _ a z ρ _ _ hd hd
  simp only [distanceTest,RealTest.eval,RealExpr.eval,hdd,decide_eq_true_eq,
    real_inner_self_eq_norm_sq]
  rw [dist_eq_norm]
  constructor
  · intro h; nlinarith [norm_nonneg (z-x)]
  · intro h; nlinarith [norm_nonneg (z-x)]

theorem triangleQueryProgram_correct (a : Fin 3 → Space) (z : Space) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : triangleQueryProgram.eval a z ρ = true ↔
      ∃ y ∈ convexHull ℝ (Set.range a), dist y z ≤ ρ := by
  have hv (i : Fin 3) := distanceTest_eval (vertexExpr i) a z ρ (a i) (fun _ => rfl) hρ
  have hs (i j : Fin 3) := distanceTest_eval (segmentExpr i j) a z ρ
    (segmentPoint (a i) (a j) z) (fun l => segmentExpr_eval i j l a z ρ) hρ
  have hp := distanceTest_eval planeExpr a z ρ (planePoint a z)
    (fun j => planeExpr_eval j a z ρ) hρ
  rw [← triangleBallTest_iff]
  simp only [triangleQueryProgram,RealTest.eval,RealExpr.eval,Bool.and_eq_true,
    Bool.or_eq_true,decide_eq_true_eq,hρ,true_and,determinantExpr_eval,
    planeUExpr_eval,planeVExpr_eval,hv,hs,hp]
  unfold triangleBallTest planeFeasible
  constructor
  · rintro (h | h | h | h | h | h | h)
    · exact Or.inl ⟨0,h⟩
    · exact Or.inl ⟨1,h⟩
    · exact Or.inl ⟨2,h⟩
    · exact Or.inr (Or.inl ⟨0,1,by decide,h⟩)
    · exact Or.inr (Or.inl ⟨0,2,by decide,h⟩)
    · exact Or.inr (Or.inl ⟨1,2,by decide,h⟩)
    · exact Or.inr (Or.inr ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩,h.2.2.2.2⟩)
  · rintro (⟨i,hi⟩ | ⟨i,j,hij,hd⟩ | ⟨h,hp⟩)
    · fin_cases i <;> aesop
    · fin_cases i <;> fin_cases j <;> norm_num at hij <;> aesop
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hp⟩)))))


/-- Actual recursive evaluator, carrying each executed arithmetic/read cost. -/
noncomputable def RealExpr.run (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealExpr → ℝ × ℕ
  | .constant x => (x,1)
  | .vertex i j => (a i j,1)
  | .center j => (z j,1)
  | .radius => (ρ,1)
  | .add x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1+Y.1,1+X.2+Y.2)
  | .sub x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1-Y.1,1+X.2+Y.2)
  | .mul x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1*Y.1,1+X.2+Y.2)
  | .div x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      if Y.1 = 0 then (0,1+X.2+Y.2) else (X.1/Y.1,2+X.2+Y.2)
  | .min x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (Min.min X.1 Y.1,1+X.2+Y.2)
  | .max x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (Max.max X.1 Y.1,1+X.2+Y.2)

theorem RealExpr.run_value (e : RealExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).1 = e.eval a z ρ := by
  induction e <;> simp_all only [RealExpr.run,RealExpr.eval]
  split_ifs with h
  · simp_all
  · rfl

theorem RealExpr.run_cost_le (e : RealExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).2 ≤ 2*e.cost := by
  induction e <;> simp_all only [RealExpr.run,RealExpr.cost]
  all_goals try omega
  split_ifs <;> omega

noncomputable def RealTest.run (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealTest → Bool × ℕ
  | .le x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (decide (X.1 ≤ Y.1),1+X.2+Y.2)
  | .ne x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (decide (X.1 ≠ Y.1),1+X.2+Y.2)
  | .both x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1 && Y.1,1+X.2+Y.2)
  | .either x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1 || Y.1,1+X.2+Y.2)

theorem RealTest.run_value (e : RealTest) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).1 = e.eval a z ρ := by
  induction e <;> simp_all [RealTest.run,RealTest.eval,RealExpr.run_value]

theorem RealTest.run_cost_le (e : RealTest) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).2 ≤ 2*e.cost := by
  induction e with
  | le x y =>
    have hx := x.run_cost_le a z ρ
    have hy := y.run_cost_le a z ρ
    simp only [RealTest.run,RealTest.cost]; omega
  | ne x y =>
    have hx := x.run_cost_le a z ρ
    have hy := y.run_cost_le a z ρ
    simp only [RealTest.run,RealTest.cost]; omega
  | both x y ihx ihy => simp only [RealTest.run,RealTest.cost]; omega
  | either x y ihx ihy => simp only [RealTest.run,RealTest.cost]; omega

noncomputable def triangleQuery (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : Bool × ℕ :=
  triangleQueryProgram.run a z ρ

theorem triangleQuery_correct (a : Fin 3 → Space) (z : Space) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (triangleQuery a z ρ).1 = true ↔
      ∃ y ∈ convexHull ℝ (Set.range a), dist y z ≤ ρ := by
  rw [triangleQuery,RealTest.run_value,triangleQueryProgram_correct a z hρ]

theorem triangleQuery_cost_le (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (triangleQuery a z ρ).2 ≤ 200000 := by
  have h := triangleQueryProgram.run_cost_le a z ρ
  have hc := triangleQueryProgram_cost_le
  dsimp [triangleQuery]
  omega

end QEC.Coding.BDL26RandomPerturbation
