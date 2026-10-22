import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.FiniteExperimentCost
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountableExperimentGeometry

/-!
# Paid materialization of the actual replacement coordinates

The interpreter scans the original emitted rows and executes the original
piecewise affine RX/RZ formulas. Scalar arithmetic and each visited row are
charged. Ranked label/incidence generation and incoming-map access in the old
perturbation program remain outside this model. [BDL26, Section 3, replacement
interpolation and randomized embedding induction].
-/

noncomputable section
namespace QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

/-- Two operations per visited row: compare the label and read the row. -/
def pointRowQuery {A : Type*} [DecidableEq A] (v : A) : List (A × Space) → Space × ℕ
  | [] => (0,0)
  | (a,x)::R => if a = v then (x,2) else
      let q := pointRowQuery v R
      (q.1,q.2+2)

def labelReadCost {A : Type*} [DecidableEq A] (v : A) : List A → ℕ
  | [] => 0
  | a::R => if a = v then 2 else labelReadCost v R+2

theorem pointRowQuery_cost_labels {A : Type*} [DecidableEq A] (v : A)
    (R : List (A × Space)) : (pointRowQuery v R).2 = labelReadCost v (R.map Prod.fst) := by
  induction R with
  | nil => rfl
  | cons a R ih => simp only [pointRowQuery,List.map_cons,labelReadCost]; split_ifs <;> simp_all

theorem pointRowQuery_cost_le {A : Type*} [DecidableEq A] (v : A)
    (R : List (A × Space)) : (pointRowQuery v R).2 ≤ 2*R.length := by
  induction R with
  | nil => simp [pointRowQuery]
  | cons a R ih => simp only [pointRowQuery,List.length_cons]; split_ifs <;> simp_all; omega

theorem pointRowQuery_map {A : Type*} [DecidableEq A] (J : A → Space)
    (v : A) (L : List A) (h : v ∈ L) :
    (pointRowQuery v (L.map (fun a => (a,J a)))).1 = J v := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
      by_cases ha : a = v
      · subst a; simp [pointRowQuery]
      · have hva : v ≠ a := Ne.symm ha
        have hv : v ∈ L := by simpa only [List.mem_cons, hva, false_or] using h
        simpa [pointRowQuery,ha] using ih hv

/-- The program contains only paid label reads, scalar arithmetic, vector operations
and static-coordinate comparisons. No geometry-map callback is a constructor. -/
inductive PointCode (A : Type*) where
  | read (v : A)
  | add (a b : PointCode A)
  | scale (r : RealExpr) (a : PointCode A)
  | choose (test : RealTest) (a b : PointCode A)
  | tag (a : PointCode A)

namespace PointCode
variable {A B : Type*}

def eval (J : A → Space) : PointCode A → Space
  | .read v => J v
  | .add a b => a.eval J + b.eval J
  | .scale r a => r.eval (fun _ => 0) 0 0 • a.eval J
  | .choose t a b => if t.eval (fun _ => 0) 0 0 then a.eval J else b.eval J
  | .tag a => a.eval J

def run [DecidableEq A] (R : List (A × Space)) : PointCode A → Space × ℕ
  | .read v => let q := pointRowQuery v R; (q.1,q.2+1)
  | .add a b => let x := a.run R; let y := b.run R; (x.1+y.1,x.2+y.2+4)
  | .scale r a => let x := r.run (fun _ => 0) 0 0; let y := a.run R
                  (x.1 • y.1,x.2+y.2+4)
  | .choose t a b => let q := t.run (fun _ => 0) 0 0
                     let out := if q.1 then a.run R else b.run R
                     (out.1,q.2+out.2+1)
  | .tag a => let out := a.run R; (out.1,out.2+1)

def reads : PointCode A → ℕ
  | .read _ => 1
  | .add a b => a.reads+b.reads
  | .scale _ a => a.reads
  | .choose _ a b => max a.reads b.reads
  | .tag a => a.reads

def work : PointCode A → ℕ
  | .read _ => 1
  | .add a b => a.work+b.work+4
  | .scale r a => 2*r.cost+a.work+4
  | .choose t a b => 2*t.cost+max a.work b.work+1
  | .tag a => a.work+1

def rename (f : A → B) : PointCode A → PointCode B
  | .read v => .read (f v)
  | .add a b => .add (a.rename f) (b.rename f)
  | .scale r a => .scale r (a.rename f)
  | .choose t a b => .choose t (a.rename f) (b.rename f)
  | .tag a => .tag (a.rename f)

@[simp] theorem eval_rename (f : A → B) (J : B → Space) (c : PointCode A) :
    (c.rename f).eval J = c.eval (J ∘ f) := by
  induction c <;> simp_all [rename,eval]

@[simp] theorem reads_rename (f : A → B) (c : PointCode A) : (c.rename f).reads = c.reads := by
  induction c <;> simp_all [rename,reads]

@[simp] theorem work_rename (f : A → B) (c : PointCode A) : (c.rename f).work = c.work := by
  induction c <;> simp_all [rename,work]

theorem run_value [DecidableEq A] (J : A → Space) (L : List A)
    (hL : ∀ v, v ∈ L) (c : PointCode A) :
    (c.run (L.map (fun v => (v,J v)))).1 = c.eval J := by
  induction c with
  | read v => exact pointRowQuery_map J v L (hL v)
  | add a b ia ib => simp only [run,eval,ia,ib]
  | scale r a ia => simp only [run,eval,RealExpr.run_value,ia]
  | choose t a b ia ib => simp only [run,eval,RealTest.run_value]; split_ifs <;> simp_all
  | tag a ia => exact ia

theorem run_cost_le [DecidableEq A] (R : List (A × Space)) (c : PointCode A) :
    (c.run R).2 ≤ 2*R.length*c.reads+c.work := by
  induction c with
  | read v => have h := pointRowQuery_cost_le v R; simp only [run,reads,work]; omega
  | add a b ia ib => simp only [run,reads,work]; nlinarith
  | scale r a ia =>
      have hr := r.run_cost_le (fun _ => 0) 0 0
      simp only [run,reads,work]; omega
  | choose t a b ia ib =>
      have ht := t.run_cost_le (fun _ => 0) 0 0
      have hra := Nat.le_max_left a.reads b.reads
      have hrb := Nat.le_max_right a.reads b.reads
      have hwa := Nat.le_max_left a.work b.work
      have hwb := Nat.le_max_right a.work b.work
      have hma := Nat.mul_le_mul_left (2*R.length) hra
      have hmb := Nat.mul_le_mul_left (2*R.length) hrb
      simp only [run,reads,work]; split_ifs <;> nlinarith
  | tag a ia => simp only [run,reads,work]; omega

def costOnLabels [DecidableEq A] (L : List A) : PointCode A → ℕ
  | .read v => labelReadCost v L+1
  | .add a b => a.costOnLabels L+b.costOnLabels L+4
  | .scale r a => (r.run (fun _ => 0) 0 0).2+a.costOnLabels L+4
  | .choose t a b => let q := t.run (fun _ => 0) 0 0
                     q.2+(if q.1 then a.costOnLabels L else b.costOnLabels L)+1
  | .tag a => a.costOnLabels L+1

theorem run_cost_labels [DecidableEq A] (R : List (A × Space)) (c : PointCode A) :
    (c.run R).2 = c.costOnLabels (R.map Prod.fst) := by
  induction c <;> simp_all only [run,costOnLabels,pointRowQuery_cost_labels]
  split_ifs <;> simp_all
end PointCode

def ratioExpr (a b : ℕ) : RealExpr := .div (.constant a) (.constant b)
def contractionExpr (S : OddScale) : RealExpr :=
  .div (.mul (.constant 2) (.constant S.half)) (.constant S.ell)
def stepExpr (S : OddScale) (i : ℕ) : RealExpr :=
  .div (.mul (.constant 2) (.add (.constant i) (.constant 1))) (.constant S.ell)
def centerExpr (S : OddScale) (i : ℕ) : RealExpr :=
  .div (.add (.mul (.constant 2) (.constant i)) (.constant 1)) (.constant S.ell)

def blendCode {A : Type*} (t : RealExpr) (a b : PointCode A) : PointCode A :=
  .add (.scale (.sub (.constant 1) t) a) (.scale t b)

@[simp] theorem blendCode_reads {A : Type*} (t : RealExpr) (a b : PointCode A) :
    (blendCode t a b).reads = a.reads+b.reads := rfl

@[simp] theorem blendCode_work {A : Type*} (t : RealExpr) (a b : PointCode A) :
    (blendCode t a b).work = 4*t.cost+a.work+b.work+16 := by
  simp only [blendCode,PointCode.work,RealExpr.cost]; omega

def faceCode (P : TannerSquarePresentation) (f : P.Face) (u v : RealExpr) :
    PointCode (Vertex P) :=
  let x := PointCode.read (.x (P.faceX f))
  let q0 := PointCode.read (.q (P.faceQ f 0))
  let q1 := PointCode.read (.q (P.faceQ f 1))
  let z := PointCode.read (.z (P.faceZ f))
  .tag (.choose (.le v u)
    (.add (.add (.scale (.sub (.constant 1) u) x) (.scale (.sub u v) q0)) (.scale v z))
    (.add (.add (.scale (.sub (.constant 1) v) x) (.scale (.sub v u) q1)) (.scale u z)))

theorem faceCode_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (f : P.Face) (u v : RealExpr) :
    (faceCode P f u v).eval J =
      facePoint P J f (u.eval (fun _ => 0) 0 0) (v.eval (fun _ => 0) 0 0) := by
  simp [faceCode,PointCode.eval,facePoint,foldedSquare,RealTest.eval,RealExpr.eval]

theorem faceCode_bounds (P : TannerSquarePresentation) (f : P.Face) (u v : RealExpr)
    (hu : u.cost ≤ 7) (hv : v.cost ≤ 7) :
    (faceCode P f u v).reads ≤ 4 ∧ (faceCode P f u v).work ≤ 128 := by
  simp only [faceCode,PointCode.reads,PointCode.work,RealExpr.cost,RealTest.cost]
  omega

def starCode (P : TannerSquarePresentation) (S : OddScale) (x : P.X)
    (v : XStarVertex P x) : PointCode (Vertex P) :=
  .tag (blendCode (contractionExpr S) (.read (.x x)) (.read v.1))

theorem starCode_value (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → Space) (x : P.X) (v : XStarVertex P x) :
    (starCode P S x v).eval J = starVertexPoint P S J x v := by
  simp [starCode,blendCode,PointCode.eval,contractionExpr,RealExpr.eval,starVertexPoint,contractionRatio]

theorem starCode_bounds (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (v : XStarVertex P x) :
    (starCode P S x v).reads ≤ 2 ∧ (starCode P S x v).work ≤ 40 := by
  norm_num [starCode,blendCode,PointCode.reads,PointCode.work,contractionExpr,RealExpr.cost]

def subdivisionCode (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    SubdivisionVertex P x S → PointCode (Vertex P)
  | .inl v => .tag (starCode P S x v)
  | .inr (.inl (e,i)) => .tag (blendCode
      (.div (.add (.constant i.val) (.constant 1)) (.constant S.half))
      (starCode P S x (xStarEdgeStart P x e)) (starCode P S x (xStarEdgeEnd P x e)))
  | .inr (.inr (f,i,j)) => .tag (faceCode P f.1 (stepExpr S i.val) (stepExpr S j.val))

theorem subdivisionCode_value (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → Space) (x : P.X) (v : SubdivisionVertex P x S) :
    (subdivisionCode P S x v).eval J = subdivisionVertexPoint P S J x v := by
  rcases v with v | (⟨e,i⟩ | ⟨f,i,j⟩)
  · simp [subdivisionCode,PointCode.eval,subdivisionVertexPoint,starCode_value]
  · simp [subdivisionCode,blendCode,PointCode.eval,RealExpr.eval,subdivisionVertexPoint,starCode_value]
  · simp [subdivisionCode,PointCode.eval,faceCode_value,stepExpr,RealExpr.eval,subdivisionVertexPoint]

theorem subdivisionCode_bounds (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (v : SubdivisionVertex P x S) :
    (subdivisionCode P S x v).reads ≤ 4 ∧ (subdivisionCode P S x v).work ≤ 256 := by
  rcases v with v | (⟨e,i⟩ | ⟨f,i,j⟩)
  · have h := starCode_bounds P S x v
    simp only [subdivisionCode,PointCode.reads,PointCode.work]; omega
  · have h0 := starCode_bounds P S x (xStarEdgeStart P x e)
    have h1 := starCode_bounds P S x (xStarEdgeEnd P x e)
    simp only [subdivisionCode,PointCode.reads,PointCode.work,blendCode_reads,blendCode_work,RealExpr.cost]
    omega
  · have h := faceCode_bounds P f.1 (stepExpr S i.val) (stepExpr S j.val)
      (by norm_num [stepExpr,RealExpr.cost]) (by norm_num [stepExpr,RealExpr.cost])
    simp only [subdivisionCode,PointCode.reads,PointCode.work]; omega

def qSubdivisionCode (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    QSubdivisionVertex P q S → PointCode (Vertex P)
  | .inl (.inl _) => .tag (.read (.q q))
  | .inl (.inr e) => .tag (blendCode (contractionExpr S) (.read (.q q)) (.read (.z e.1)))
  | .inr (e,i) => .tag (blendCode (stepExpr S i.val) (.read (.q q)) (.read (.z e.1)))

theorem qSubdivisionCode_value (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → Space) (q : P.Q) (v : QSubdivisionVertex P q S) :
    (qSubdivisionCode P S q v).eval J = qSubdivisionVertexPoint P S J q v := by
  rcases v with (v | e) | ⟨e,i⟩ <;>
    simp [qSubdivisionCode,blendCode,PointCode.eval,RealExpr.eval,contractionExpr,
      stepExpr,qSubdivisionVertexPoint,contractionRatio]

theorem qSubdivisionCode_bounds (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (v : QSubdivisionVertex P q S) :
    (qSubdivisionCode P S q v).reads ≤ 2 ∧ (qSubdivisionCode P S q v).work ≤ 48 := by
  rcases v with (v | e) | ⟨e,i⟩ <;>
    norm_num [qSubdivisionCode,blendCode,PointCode.reads,PointCode.work,
      contractionExpr,stepExpr,RealExpr.cost]

def rxZeroCode (P : TannerSquarePresentation) (S : OddScale) (v : RX0 P S) : PointCode (Vertex P) :=
  .tag (subdivisionCode P S v.1 v.2.2)

def rxOneCode (P : TannerSquarePresentation) (S : OddScale) : RX1 P S → PointCode (Vertex P)
  | .inl ⟨x,e⟩ => .tag (.scale (ratioExpr 1 2) (.add
      (subdivisionCode P S x (tannerDoubleCylinderEdgeStart P x S e).2)
      (subdivisionCode P S x (tannerDoubleCylinderEdgeEnd P x S e).2)))
  | .inr ⟨q,_,v⟩ => .tag (qSubdivisionCode P S q v)

def rxTwoCode (P : TannerSquarePresentation) (S : OddScale) : RX2 P S → PointCode (Vertex P)
  | .inl (.inl ⟨_, .inl (_,f,i,j)⟩) => .tag (faceCode P f.1 (centerExpr S i.val) (centerExpr S j.val))
  | .inl (.inl ⟨x, .inr e⟩) => .tag (.scale (ratioExpr 1 2) (.add
      (subdivisionCode P S x (subdivisionEdgeStart P x S e.1))
      (subdivisionCode P S x (subdivisionEdgeEnd P x S e.1))))
  | .inl (.inr ⟨q,e⟩) => .tag (.scale (ratioExpr 1 2) (.add
      (qSubdivisionCode P S q (qDoubleCylinderEdgeStart P q S e).2)
      (qSubdivisionCode P S q (qDoubleCylinderEdgeEnd P q S e).2)))
  | .inr (z,_) => .tag (.read (.z z))

theorem rxZeroCode_value (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : RX0 P S) : (rxZeroCode P S v).eval J = rxZeroPoint P S J v := by
  simp [rxZeroCode,PointCode.eval,subdivisionCode_value,rxZeroPoint]

theorem rxOneCode_value (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : RX1 P S) : (rxOneCode P S v).eval J = rxOnePoint P S J v := by
  rcases v with ⟨x,e⟩ | ⟨q,c,v⟩ <;>
    simp [rxOneCode,PointCode.eval,ratioExpr,RealExpr.eval,
      subdivisionCode_value,qSubdivisionCode_value,rxOnePoint]

theorem rxTwoCode_value (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : RX2 P S) : (rxTwoCode P S v).eval J = rxTwoPoint P S J v := by
  rcases v with (⟨x,⟨c,f,i,j⟩ | e⟩ | ⟨q,e⟩) | ⟨z,c⟩ <;>
    simp [rxTwoCode,PointCode.eval,ratioExpr,RealExpr.eval,centerExpr,faceCode_value,
      subdivisionCode_value,qSubdivisionCode_value,rxTwoPoint]

theorem rxZeroCode_bounds (P : TannerSquarePresentation) (S : OddScale) (v : RX0 P S) :
    (rxZeroCode P S v).reads ≤ 4 ∧ (rxZeroCode P S v).work ≤ 257 := by
  have h := subdivisionCode_bounds P S v.1 v.2.2
  simp only [rxZeroCode,PointCode.reads,PointCode.work]; omega

theorem rxOneCode_bounds (P : TannerSquarePresentation) (S : OddScale) (v : RX1 P S) :
    (rxOneCode P S v).reads ≤ 8 ∧ (rxOneCode P S v).work ≤ 1024 := by
  rcases v with ⟨x,e⟩ | ⟨q,c,v⟩
  · have h0 := subdivisionCode_bounds P S x (tannerDoubleCylinderEdgeStart P x S e).2
    have h1 := subdivisionCode_bounds P S x (tannerDoubleCylinderEdgeEnd P x S e).2
    simp only [rxOneCode,PointCode.reads,PointCode.work,ratioExpr,RealExpr.cost]; omega
  · have h := qSubdivisionCode_bounds P S q v
    simp only [rxOneCode,PointCode.reads,PointCode.work]; omega

theorem rxTwoCode_bounds (P : TannerSquarePresentation) (S : OddScale) (v : RX2 P S) :
    (rxTwoCode P S v).reads ≤ 8 ∧ (rxTwoCode P S v).work ≤ 1024 := by
  rcases v with (⟨x,⟨c,f,i,j⟩ | e⟩ | ⟨q,e⟩) | ⟨z,c⟩
  · have h := faceCode_bounds P f.1 (centerExpr S i.val) (centerExpr S j.val)
      (by norm_num [centerExpr,RealExpr.cost]) (by norm_num [centerExpr,RealExpr.cost])
    simp only [rxTwoCode,PointCode.reads,PointCode.work]; omega
  · have h0 := subdivisionCode_bounds P S x (subdivisionEdgeStart P x S e.1)
    have h1 := subdivisionCode_bounds P S x (subdivisionEdgeEnd P x S e.1)
    simp only [rxTwoCode,PointCode.reads,PointCode.work,ratioExpr,RealExpr.cost]; omega
  · have h0 := qSubdivisionCode_bounds P S q (qDoubleCylinderEdgeStart P q S e).2
    have h1 := qSubdivisionCode_bounds P S q (qDoubleCylinderEdgeEnd P q S e).2
    simp only [rxTwoCode,PointCode.reads,PointCode.work,ratioExpr,RealExpr.cost]; omega
  · norm_num [rxTwoCode,PointCode.reads,PointCode.work]

def rxCode (P : TannerSquarePresentation) (S : OddScale) :
    Vertex (rxReplacementPresentation P S) → PointCode (Vertex P)
  | .x x => .tag (rxZeroCode P S x)
  | .q q => .tag (rxOneCode P S q)
  | .z z => .tag (rxTwoCode P S z)

def rzCode (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S) → PointCode (Vertex P)
  | .x x => .tag ((rxTwoCode (transposePresentation P) S x).rename (transposeVertexEquiv P))
  | .q q => .tag ((rxOneCode (transposePresentation P) S q).rename (transposeVertexEquiv P))
  | .z z => .tag ((rxZeroCode (transposePresentation P) S z).rename (transposeVertexEquiv P))

theorem rxCode_value (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : Vertex (rxReplacementPresentation P S)) : (rxCode P S v).eval J = rxVertexPoint P S J v := by
  cases v with
  | x v => exact rxZeroCode_value P S J v
  | q v => exact rxOneCode_value P S J v
  | z v => exact rxTwoCode_value P S J v

theorem rzCode_value (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (J : Vertex P → Space) (v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)) :
    (rzCode P A S v).eval J = rzVertexPoint P A S J v := by
  cases v with
  | x v =>
      change ((rxTwoCode (transposePresentation P) S v).rename (transposeVertexEquiv P)).eval J =
        rxTwoPoint (transposePresentation P) S (J ∘ transposeVertexEquiv P) v
      rw [PointCode.eval_rename]
      exact rxTwoCode_value (transposePresentation P) S (J ∘ transposeVertexEquiv P) v
  | q v =>
      change ((rxOneCode (transposePresentation P) S v).rename (transposeVertexEquiv P)).eval J =
        rxOnePoint (transposePresentation P) S (J ∘ transposeVertexEquiv P) v
      rw [PointCode.eval_rename]
      exact rxOneCode_value (transposePresentation P) S (J ∘ transposeVertexEquiv P) v
  | z v =>
      change ((rxZeroCode (transposePresentation P) S v).rename (transposeVertexEquiv P)).eval J =
        rxZeroPoint (transposePresentation P) S (J ∘ transposeVertexEquiv P) v
      rw [PointCode.eval_rename]
      exact rxZeroCode_value (transposePresentation P) S (J ∘ transposeVertexEquiv P) v

theorem rxCode_bounds (P : TannerSquarePresentation) (S : OddScale)
    (v : Vertex (rxReplacementPresentation P S)) :
    (rxCode P S v).reads ≤ 8 ∧ (rxCode P S v).work ≤ 2048 := by
  cases v with
  | x v => have h := rxZeroCode_bounds P S v; simp only [rxCode,PointCode.reads,PointCode.work]; omega
  | q v => have h := rxOneCode_bounds P S v; simp only [rxCode,PointCode.reads,PointCode.work]; omega
  | z v => have h := rxTwoCode_bounds P S v; simp only [rxCode,PointCode.reads,PointCode.work]; omega

theorem rzCode_bounds (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)) :
    (rzCode P A S v).reads ≤ 8 ∧ (rzCode P A S v).work ≤ 2048 := by
  cases v with
  | x v => have h := rxTwoCode_bounds (transposePresentation P) S v
           simp only [rzCode,PointCode.reads,PointCode.work,PointCode.reads_rename,PointCode.work_rename]; omega
  | q v => have h := rxOneCode_bounds (transposePresentation P) S v
           simp only [rzCode,PointCode.reads,PointCode.work,PointCode.reads_rename,PointCode.work_rename]; omega
  | z v => have h := rxZeroCode_bounds (transposePresentation P) S v
           simp only [rzCode,PointCode.reads,PointCode.work,PointCode.reads_rename,PointCode.work_rename]; omega

/-- Select the exact successor carrier; RZ reads are renamed, never copied into a new input list. -/
def successorCode {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (v : Vertex (StagePresentation p (n+1))) : PointCode (Vertex (StagePresentation p n)) :=
  if h : n % 2 = 0 then
    rxCode _ (perturbationOddScale p) (nextRXVertex _ n (state (perturbationOddScale p) n) h v)
  else rzCode _ (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
    (perturbationOddScale p) (nextRZVertex _ n (state (perturbationOddScale p) n) h v)

theorem successorCode_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (v : Vertex (StagePresentation p (n+1))) :
    (successorCode p n v).eval J =
      replacementOutput (perturbationOddScale p) n (state (perturbationOddScale p) n) J v := by
  by_cases h : n % 2 = 0
  · rw [replacementOutput_rx _ _ _ _ h]
    simpa only [successorCode,dif_pos h] using
      rxCode_value _ (perturbationOddScale p) J (nextRXVertex _ n _ h v)
  · rw [replacementOutput_rz _ _ _ _ h]
    simpa only [successorCode,dif_neg h] using
      rzCode_value _ (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
        (perturbationOddScale p) J (nextRZVertex _ n _ h v)

theorem successorCode_bounds {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (v : Vertex (StagePresentation p (n+1))) :
    (successorCode p n v).reads ≤ 8 ∧ (successorCode p n v).work ≤ 2048 := by
  by_cases h : n % 2 = 0
  · simpa only [successorCode,dif_pos h] using
      rxCode_bounds _ (perturbationOddScale p) (nextRXVertex _ n _ h v)
  · simpa only [successorCode,dif_neg h] using
      rzCode_bounds _ (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
        (perturbationOddScale p) (nextRZVertex _ n _ h v)

/-- The exact stopped row-output expression already executed by the perturbation program. -/
def emittedRows {L : ℝ} (p : GeometricParameters L) (n : ℕ) (J : StageMaps p n)
    (T : StageTables p n) : List (Vertex (StagePresentation p n) × Space) :=
  (outputStateRowsQuery (StagePresentation p n) J p.lambda
    (actualPrefixQuery (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
      (eventUniverseQuery (StagePresentation p n) J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1 T
      (haltTime (eventSupport (StagePresentation p n) J (anchorRadius p.m))
        (eventBad (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)).1).1

theorem emittedRows_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    emittedRows p n J T = (vertexInputList (StagePresentation p n)).map
      (fun v => (v,perturbationEmbeddingOutput (StagePresentation p n) J p T v)) :=
  actual_emitted_embedding_rows (StagePresentation p n) J p T

theorem emittedRows_labels {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (emittedRows p n J T).map Prod.fst = vertexInputList (StagePresentation p n) := by
  rw [emittedRows_value]
  simp [List.map_map,Function.comp_def]

theorem emittedRows_length {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (emittedRows p n J T).length = Fintype.card (Vertex (StagePresentation p n)) := by
  rw [emittedRows_value,List.length_map,vertexInputList_length]

theorem emittedRows_labels_nodup {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) : ((emittedRows p n J T).map Prod.fst).Nodup := by
  rw [emittedRows_labels]
  exact List.nodup_ofFn_ofInjective (Fintype.equivFin (Vertex (StagePresentation p n))).symm.injective

/-- Each successor output is a paid interpretation followed by a labelled row emission. -/
def materializeRows {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    List (Vertex (StagePresentation p (n+1)) × Space) × ℕ :=
  mapQuery (fun v => let q := (successorCode p n v).run R
                     ((v,q.1),q.2+1)) (vertexInputList (StagePresentation p (n+1)))

theorem materializeRows_value {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (materializeRows p n (emittedRows p n J T)).1 =
      (vertexInputList (StagePresentation p (n+1))).map (fun v => (v,physicalSuccessorOutput p n J T v)) := by
  rw [emittedRows_value]
  simp only [materializeRows,mapQuery_value]
  apply List.map_congr_left
  intro v _
  have h := PointCode.run_value (perturbationEmbeddingOutput (StagePresentation p n) J p T)
    (vertexInputList (StagePresentation p n)) (vertexInputList_complete _) (successorCode p n v)
  rw [h,successorCode_value]
  rfl

theorem materializeRows_labels {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    ((materializeRows p n R).1).map Prod.fst = vertexInputList (StagePresentation p (n+1)) := by
  simp [materializeRows,mapQuery_value,List.map_map,Function.comp_def]

theorem materializeRows_cost_le {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    (materializeRows p n R).2 ≤
      65536*(R.length+1)*Fintype.card (Vertex (StagePresentation p (n+1))) := by
  have hquery (v : Vertex (StagePresentation p (n+1))) :
      ((successorCode p n v).run R).2+1 ≤ 65535*(R.length+1) := by
    have hb := PointCode.run_cost_le R (successorCode p n v)
    have hc := successorCode_bounds p n v
    have hm := Nat.mul_le_mul_left (2*R.length) hc.1
    nlinarith
  have h := mapQuery_cost_le
    (fun v => let q := (successorCode p n v).run R; ((v,q.1),q.2+1))
    (vertexInputList (StagePresentation p (n+1))) (65535*(R.length+1)) (fun v _ => hquery v)
  rw [vertexInputList_length] at h
  change (materializeRows p n R).2 ≤ _
  calc
    _ ≤ Fintype.card (Vertex (StagePresentation p (n+1)))*(65535*(R.length+1)+1) := h
    _ ≤ Fintype.card (Vertex (StagePresentation p (n+1)))*(65536*(R.length+1)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

/-- Static label-only execution cost; equality with the actual program is proved below. -/
def materializationLabelCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  (mapQuery (fun v => ((v,(0 : Space)),
    (successorCode p n v).costOnLabels (vertexInputList (StagePresentation p n))+1))
      (vertexInputList (StagePresentation p (n+1)))).2

theorem mapQuery_cost_congr {A B C : Type*} (q : A → B × ℕ) (r : A → C × ℕ)
    (h : ∀ a, (q a).2 = (r a).2) (L : List A) : (mapQuery q L).2 = (mapQuery r L).2 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [mapQuery,h a,ih]

theorem materializeRows_cost_labels {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (materializeRows p n (emittedRows p n J T)).2 = materializationLabelCost p n := by
  unfold materializeRows materializationLabelCost
  apply mapQuery_cost_congr
  intro v
  simp only [PointCode.run_cost_labels,emittedRows_labels]

def materializationCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : ℕ := (materializeRows p n (emittedRows p n w.1 w.2)).2

theorem materializationCost_static {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : materializationCost p n w = materializationLabelCost p n :=
  materializeRows_cost_labels p n w.1 w.2

theorem materializationCost_le {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : materializationCost p n w ≤
      65536*(Fintype.card (Vertex (StagePresentation p n))+1)*
        Fintype.card (Vertex (StagePresentation p (n+1))) := by
  have h := materializeRows_cost_le p n (emittedRows p n w.1 w.2)
  rw [emittedRows_length] at h
  exact h

theorem measurable_materializationCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (materializationCost p n) := by
  have h : materializationCost p n = fun _ => materializationLabelCost p n :=
    funext (materializationCost_static p n)
  rw [h]
  exact measurable_const

/-- The old execution is shared once; the new phase consumes its retained emitted rows. -/
def paidSuccessorQuery {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    List (Vertex (StagePresentation p (n+1)) × Space) × ℝ≥0∞ :=
  let events := eventUniverseQuery (StagePresentation p n) J
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
  let prior := actualPrefixQuery (StagePresentation p n) J (anchorRadius p.m) p.lambda
    ((6*p.m+2)*p.lambda) events.1 T
    (haltTime (eventSupport (StagePresentation p n) J (anchorRadius p.m))
      (eventBad (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)
  let scan := actualScanQuery (StagePresentation p n) J (anchorRadius p.m) p.lambda
    ((6*p.m+2)*p.lambda) events.1 prior.1
  let oldRows := outputStateRowsQuery (StagePresentation p n) J p.lambda prior.1
  let newRows := materializeRows p n oldRows.1
  (newRows.1, if Halts (eventSupport (StagePresentation p n) J (anchorRadius p.m))
      (eventBad (StagePresentation p n) J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
    then ((events.2+prior.2+scan.2+oldRows.2+newRows.2 : ℕ) : ℝ≥0∞) else ∞)

theorem paidSuccessorQuery_rows {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (paidSuccessorQuery p n J T).1 =
      (vertexInputList (StagePresentation p (n+1))).map (fun v => (v,physicalSuccessorOutput p n J T v)) :=
  materializeRows_value p n J T

theorem paidSuccessorQuery_cost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (paidSuccessorQuery p n J T).2 = jointStageCost p n (J,T) + (materializationCost p n (J,T) : ℕ) := by
  unfold paidSuccessorQuery jointStageCost actualExecutionCost materializationCost emittedRows
  split_ifs <;> simp only [Nat.cast_add,top_add]

def stageMaterializationCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℕ := materializationCost p i.val (stagePair p N i z)

def totalMaterializationCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : ℕ := ∑ i : Fin N, stageMaterializationCost p N i z

def extendedStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℝ≥0∞ :=
  (paidSuccessorQuery p i.val (stageInput p N i z) (tableAt p N i z)).2

def extendedTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : ℝ≥0∞ := ∑ i : Fin N, extendedStageCost p N i z

theorem extendedStageCost_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) :
    extendedStageCost p N i z = stageCost p N i z + (stageMaterializationCost p N i z : ℕ) :=
  paidSuccessorQuery_cost p i.val (stageInput p N i z) (tableAt p N i z)

theorem extendedTotalCost_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) :
    extendedTotalCost p N z = totalStageCost p N z + (totalMaterializationCost p N z : ℕ) := by
  simp only [extendedTotalCost,extendedStageCost_eq,Finset.sum_add_distrib,
    totalStageCost,totalMaterializationCost,Nat.cast_sum]

theorem stageMaterializationCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (z : Experiment p N) :
    stageMaterializationCost p M i (experimentPrefix p M N h z) =
      stageMaterializationCost p N (i.castLE h) z :=
  congrArg (materializationCost p i.val) (stagePair_prefix p h i z)

@[simp] theorem totalMaterializationCost_zero {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 0) : totalMaterializationCost p 0 z = 0 := by
  simp only [totalMaterializationCost,Fin.sum_univ_zero]

theorem stageMaterializationCost_static {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) :
    stageMaterializationCost p N i z = materializationLabelCost p i.val :=
  materializationCost_static p i.val (stagePair p N i z)

theorem totalMaterializationCost_static {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) :
    totalMaterializationCost p N z = ∑ i : Fin N, materializationLabelCost p i.val := by
  simp only [totalMaterializationCost,stageMaterializationCost_static]

theorem totalMaterializationCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) :
    totalMaterializationCost p (N+1) z = totalMaterializationCost p N z.1 +
      materializationCost p N (evaluate p N z.1,z.2) := by
  rw [totalMaterializationCost_static,totalMaterializationCost_static,materializationCost_static]
  simp only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]

theorem measurable_extendedTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    Measurable (extendedTotalCost p N) := by
  have heq : extendedTotalCost p N = fun z => totalStageCost p N z +
      ((∑ i : Fin N, materializationLabelCost p i.val : ℕ) : ℝ≥0∞) := by
    funext z
    rw [extendedTotalCost_eq,totalMaterializationCost_static]
  rw [heq]
  exact (measurable_totalStageCost p N).add measurable_const

theorem stageVertices_le_qubits {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Fintype.card (Vertex (StagePresentation p n)) ≤ 65*stageQubits p n := by
  have h := operation_input_size_le_qubits (StagePresentation p n)
    (state (perturbationOddScale p) n).admissible.toTannerSquareAdmissible
    (state_boundedValence (perturbationOddScale p) n)
  change _ ≤ 65*Fintype.card (StagePresentation p n).Q
  omega

/-- The formerly uncharged deterministic phase is bounded by the actual final qubit size. -/
theorem stageMaterializationCost_le_final {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) :
    stageMaterializationCost p N i z ≤ 65536*65^2*(stageQubits p N+1)^2 := by
  have hb := materializationCost_le p i.val (stagePair p N i z)
  have hv0 := stageVertices_le_qubits p i.val
  have hv1 := stageVertices_le_qubits p (i.val+1)
  have hq0 := stageQubits_mono p (Nat.le_of_lt i.isLt)
  have hq1 : stageQubits p (i.val+1) ≤ stageQubits p N :=
    stageQubits_mono p (by omega : i.val+1 ≤ N)
  have h0 : Fintype.card (Vertex (StagePresentation p i.val)) ≤ 65*stageQubits p N :=
    hv0.trans (Nat.mul_le_mul_left 65 hq0)
  have h1 : Fintype.card (Vertex (StagePresentation p (i.val+1))) ≤ 65*stageQubits p N :=
    hv1.trans (Nat.mul_le_mul_left 65 hq1)
  change materializationCost p i.val (stagePair p N i z) ≤ _
  calc
    _ ≤ 65536*(Fintype.card (Vertex (StagePresentation p i.val))+1)*
        Fintype.card (Vertex (StagePresentation p (i.val+1))) := hb
    _ ≤ 65536*(65*stageQubits p N+1)*(65*stageQubits p N) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right h0 1)) h1
    _ ≤ _ := by nlinarith

theorem totalMaterializationCost_le {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) :
    totalMaterializationCost p N z ≤ 65536*65^2*(stageQubits p N+1)^3 := by
  have hN := stage_count_le_qubits p N
  calc
    _ ≤ ∑ _i : Fin N, 65536*65^2*(stageQubits p N+1)^2 :=
      Finset.sum_le_sum (fun i _ => stageMaterializationCost_le_final p N i z)
    _ = N*(65536*65^2*(stageQubits p N+1)^2) := by simp
    _ ≤ (stageQubits p N+1)*(65536*65^2*(stageQubits p N+1)^2) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

/-- Ordinary integral addition is elaborated with opaque functions, before applying it
 to the large stopped program. The actual pointwise premise is proved below. -/
private theorem lintegral_le_add_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ≥0∞)
    (hf : Measurable f) (b : ℝ≥0∞) (h : ∀ z, g z ≤ f z+b) :
    (∫⁻ z, g z ∂μ) ≤ (∫⁻ z, f z ∂μ)+b := by
  calc
    _ ≤ ∫⁻ z, f z+b ∂μ := lintegral_mono h
    _ = _ := by rw [lintegral_add_left hf]; simp

/-- This arithmetic is independent of the elaboration of the physical experiment. -/
private theorem materialization_degree_bound (C q : ℕ) :
    C*(65^10*(q+1)^11)+65536*65^2*(q+1)^3 ≤
      (C*65^10+65536*65^2)*(q+1)^11 := by
  have hp : (q+1)^3 ≤ (q+1)^11 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ C*(65^10*(q+1)^11)+65536*65^2*(q+1)^11 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hp) _
    _ = _ := by ring

/-- The actual extra cost is bounded pointwise; no law of that cost is assumed. -/
private theorem extendedTotalCost_integral_le_add {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z, extendedTotalCost p N z ∂experimentLaw p N) ≤
      (∫⁻ z, totalStageCost p N z ∂experimentLaw p N)+
        ((65536*65^2*(stageQubits p N+1)^3 : ℕ) : ℝ≥0∞) := by
  apply lintegral_le_add_constant (experimentLaw p N) (totalStageCost p N)
    (extendedTotalCost p N) (measurable_totalStageCost p N)
  intro z
  rw [extendedTotalCost_eq]
  exact add_le_add (le_refl (totalStageCost p N z))
    ((Nat.cast_le (α := ℝ≥0∞)).mpr (totalMaterializationCost_le p N z))

/-- Order and scalar arithmetic are combined before substituting the two large
integrals. Both endpoint bounds are constructed for the actual program below. -/
private theorem combine_materialization_cost_bounds (a b : ℝ≥0∞) (C q : ℕ)
    (hpaid : a ≤ b+((65536*65^2*(q+1)^3 : ℕ) : ℝ≥0∞))
    (hold : b ≤ ((C*(65^10*(q+1)^11) : ℕ) : ℝ≥0∞)) :
    a ≤ (((C*65^10+65536*65^2)*(q+1)^11 : ℕ) : ℝ≥0∞) := by
  calc
    _ ≤ b+((65536*65^2*(q+1)^3 : ℕ) : ℝ≥0∞) := hpaid
    _ ≤ ((C*(65^10*(q+1)^11) : ℕ) : ℝ≥0∞)+
        ((65536*65^2*(q+1)^3 : ℕ) : ℝ≥0∞) :=
      add_le_add hold (le_refl _)
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact (Nat.cast_le (α := ℝ≥0∞)).mpr (materialization_degree_bound C q)

theorem extendedTotalCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ z, extendedTotalCost p N z ∂experimentLaw p N) ≤
      (((operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2)*
        (stageQubits p N+1)^11 : ℕ) : ℝ≥0∞) := by
  exact combine_materialization_cost_bounds
    (∫⁻ z, extendedTotalCost p N z ∂experimentLaw p N)
    (∫⁻ z, totalStageCost p N z ∂experimentLaw p N)
    (operationConstant ((6*p.m+2)*p.lambda)) (stageQubits p N)
    (extendedTotalCost_integral_le_add p N) (totalStageCost_integral_le p N)

theorem extendedStageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬ stageHalts p N i z) :
    extendedStageCost p N i z = ∞ := by
  rw [extendedStageCost_eq,stageCost_nonhalting p N i z h,top_add]

theorem extendedTotalCost_finite_on_success {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) (h : z ∈ finiteSuccess p N) : extendedTotalCost p N z < ∞ := by
  rw [extendedTotalCost_eq]
  exact ENNReal.add_lt_top.mpr ⟨totalStageCost_finite_on_success p N z h, by simp⟩

/-- The paid rows represent the same physical successor used in the original history. -/
theorem paid_stage_rows_history {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) :
    (paidSuccessorQuery p i.val (stageInput p N i z) (tableAt p N i z)).1 =
      (vertexInputList (StagePresentation p (i.val+1))).map
        (fun v => (v,history p N z ⟨i.val+1,by omega⟩ v)) := by
  rw [paidSuccessorQuery_rows]
  have hh := history_stage p N i z
  rw [hh]
  rfl

theorem finiteSuccess_paid_rows {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) (h : z ∈ finiteSuccess p N) (i : Fin N) :
    PhysicalSuccessorFacts p i.val (stageInput p N i z) (tableAt p N i z) ∧
      extendedTotalCost p N z < ∞ :=
  ⟨finiteSuccess_stageFacts p N h i,extendedTotalCost_finite_on_success p N z h⟩

theorem common_paid_materialization {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, extendedTotalCost p N (BDL26CountableEmbeddingExperiment.truncate p N omega) < ∞) ∧
    ∀ n, PhysicalGeometry (perturbationOddScale p) n
      (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t :=
  ⟨fun N => extendedTotalCost_finite_on_success p N _ (h N),
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_geometry p h⟩

/-- Fixed parameters precede every prefix; rank/setup and incoming-oracle costs remain excluded. -/
theorem fixed_parameters_paid_materialization (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N,
      Measurable (extendedTotalCost p N) ∧
      (∫⁻ z, extendedTotalCost p N z ∂experimentLaw p N) ≤
        (((operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2)*
          (stageQubits p N+1)^11 : ℕ) : ℝ≥0∞) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ extendedTotalCost p N z < ∞ := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p,fun N => ⟨measurable_extendedTotalCost p N,extendedTotalCost_integral_le p N,?_⟩⟩
  filter_upwards [finiteSuccess_ae p N] with z h
  exact ⟨h,extendedTotalCost_finite_on_success p N z h⟩

theorem paidSuccessorQuery_lookup {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) (v : Vertex (StagePresentation p (n+1))) :
    (pointRowQuery v (paidSuccessorQuery p n J T).1).1 = physicalSuccessorOutput p n J T v := by
  rw [paidSuccessorQuery_rows]
  exact pointRowQuery_map _ v _ (vertexInputList_complete _ v)

theorem extendedStageCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (z : Experiment p N) :
    extendedStageCost p M i (experimentPrefix p M N h z) = extendedStageCost p N (i.castLE h) z := by
  rw [extendedStageCost_eq,extendedStageCost_eq,stageCost_prefix,stageMaterializationCost_prefix]

@[simp] theorem extendedTotalCost_zero {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 0) : extendedTotalCost p 0 z = 0 := by
  simp only [extendedTotalCost,Fin.sum_univ_zero]

theorem extendedTotalCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) : extendedTotalCost p (N+1) z = extendedTotalCost p N z.1 +
      (paidSuccessorQuery p N (evaluate p N z.1) z.2).2 := by
  rw [extendedTotalCost_eq,totalStageCost_succ,totalMaterializationCost_succ,
    paidSuccessorQuery_cost,extendedTotalCost_eq]
  simp only [Nat.cast_add]
  ac_rfl

theorem paid_common_rows {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) (n : ℕ) :
    (paidSuccessorQuery p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)).1 =
      (vertexInputList (StagePresentation p (n+1))).map
        (fun v => (v,BDL26CountableEmbeddingExperiment.levelMap p omega (n+1) v)) := by
  rw [paidSuccessorQuery_rows,BDL26CountableEmbeddingExperiment.levelMap_succ]

theorem materializeRows_labels_nodup {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    (((materializeRows p n R).1).map Prod.fst).Nodup := by
  rw [materializeRows_labels]
  exact List.nodup_ofFn_ofInjective (Fintype.equivFin (Vertex (StagePresentation p (n+1)))).symm.injective

theorem materializeRows_length {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    (materializeRows p n R).1.length = Fintype.card (Vertex (StagePresentation p (n+1))) := by
  have h := congrArg List.length (materializeRows_labels p n R)
  simpa only [List.length_map,vertexInputList_length] using h

end QEC.Coding.BDL26ReplacementMaterialization
