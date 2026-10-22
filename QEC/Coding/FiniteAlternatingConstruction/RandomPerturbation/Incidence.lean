import QEC.Coding.FiniteAlternatingConstruction.BoundedValence
import QEC.Coding.FiniteAlternatingConstruction.ReplacementEmbeddingCoordinates

/-!
# Labeled auxiliary triangles for random perturbation

[BDL26, Section 3, random perturbation] uses independent samples at domain
vertices. These labels and incidence bounds retain both auxiliary triangles
of every face, even when their geometric images coincide.
-/

namespace QEC.Coding.BDL26RandomPerturbation

open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding

abbrev Triangle (P : TannerSquarePresentation) := P.Face × Two

/-- The three independent domain coordinates of an auxiliary triangle. -/
def triangleVertex (P : TannerSquarePresentation) (t : Triangle P) : Fin 3 → Vertex P :=
  ![Vertex.x (P.faceX t.1), Vertex.q (P.faceQ t.1 t.2), Vertex.z (P.faceZ t.1)]

theorem triangleVertex_injective (P : TannerSquarePresentation) (t : Triangle P) :
    Function.Injective (triangleVertex P t) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangleVertex]

/-- The actual three-coordinate convex hull, including degenerate maps. -/
theorem oldTriangleImage_eq (P : TannerSquarePresentation) (t : Triangle P)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (J : Vertex P → E) :
    oldTriangleImage P J t = convexHull ℝ (Set.range fun i => J (triangleVertex P t i)) := by
  rw [oldTriangleImage]
  congr 1
  ext x
  simp [triangleVertex, Fin.exists_fin_succ, eq_comm]

/-- Variable support uses labels rather than points in the image. -/
noncomputable def triangleSupport (P : TannerSquarePresentation) (t : Triangle P) :
    Finset (Vertex P) := by
  classical
  exact Finset.univ.image (triangleVertex P t)

theorem triangleSupport_card (P : TannerSquarePresentation) (t : Triangle P) :
    (triangleSupport P t).card = 3 := by
  classical
  rw [triangleSupport, Finset.card_image_of_injective _ (triangleVertex_injective P t)]
  simp

abbrev XTriangles (P : TannerSquarePresentation) (x : P.X) :=
  {t : Triangle P // P.faceX t.1 = x}
abbrev QTriangles (P : TannerSquarePresentation) (q : P.Q) :=
  {t : Triangle P // P.faceQ t.1 t.2 = q}
abbrev ZTriangles (P : TannerSquarePresentation) (z : P.Z) :=
  {t : Triangle P // P.faceZ t.1 = z}

private theorem sigma_card_le {A : Type*} [Fintype A] (B : A → Type*)
    [∀ a, Fintype (B a)] (k : ℕ) (h : ∀ a, Fintype.card (B a) ≤ k) :
    Fintype.card (Sigma B) ≤ Fintype.card A * k := by
  rw [Fintype.card_sigma]
  calc
    ∑ a, Fintype.card (B a) ≤ ∑ _ : A, k := Finset.sum_le_sum fun a _ => h a
    _ = Fintype.card A * k := by simp

/-- Route an X-incident label through its face's first X-Q edge, retaining its side. -/
private def xTriangleRoute (P : TannerSquarePresentation) (x : P.X) (t : XTriangles P x) :
    Σ q : {q : P.Q // P.xq x q = true}, XQIncidentFace P ⟨(x, q.1), q.2⟩ × Two := by
  let q : {q : P.Q // P.xq x q = true} :=
    ⟨P.faceQ t.1.1 0, by simpa [← t.2] using P.data.faceQ_xq t.1.1 0⟩
  exact ⟨q, ⟨t.1.1, t.2, 0, rfl⟩, t.1.2⟩

private theorem xTriangleRoute_injective (P : TannerSquarePresentation) (x : P.X) :
    Function.Injective (xTriangleRoute P x) := by
  intro a b h
  have hf := congrArg (fun s => s.2.1.1) h
  have hs := congrArg (fun s => s.2.2) h
  apply Subtype.ext
  exact Prod.ext hf hs

/-- At most 56 auxiliary labels touch an X vertex, independently of map density. -/
theorem xTriangles_card_le (P : TannerSquarePresentation) (h : BoundedValence P) (x : P.X) :
    Fintype.card (XTriangles P x) ≤ 56 := by
  classical
  calc
    _ ≤ Fintype.card (Σ q : {q : P.Q // P.xq x q = true},
        XQIncidentFace P ⟨(x, q.1), q.2⟩ × Two) :=
      Fintype.card_le_of_injective _ (xTriangleRoute_injective P x)
    _ ≤ xDegree P x * 8 := sigma_card_le _ 8 (by
      intro q
      have he := xqIncidentFace_card_le_four P h ⟨(x, q.1), q.2⟩
      simp only [Fintype.card_prod, Two, Fintype.card_fin]
      omega)
    _ ≤ 56 := by have hx := h.1 x; omega

private def zTriangleRoute (P : TannerSquarePresentation) (z : P.Z) (t : ZTriangles P z) :
    Σ q : {q : P.Q // P.qz q z = true}, QZIncidentFace P ⟨(q.1, z), q.2⟩ × Two := by
  let q : {q : P.Q // P.qz q z = true} :=
    ⟨P.faceQ t.1.1 0, by simpa [← t.2] using P.data.faceQ_qz t.1.1 0⟩
  exact ⟨q, ⟨t.1.1, t.2, 0, rfl⟩, t.1.2⟩

private theorem zTriangleRoute_injective (P : TannerSquarePresentation) (z : P.Z) :
    Function.Injective (zTriangleRoute P z) := by
  intro a b h
  have hf := congrArg (fun s => s.2.1.1) h
  have hs := congrArg (fun s => s.2.2) h
  apply Subtype.ext
  exact Prod.ext hf hs

theorem zTriangles_card_le (P : TannerSquarePresentation) (h : BoundedValence P) (z : P.Z) :
    Fintype.card (ZTriangles P z) ≤ 56 := by
  classical
  calc
    _ ≤ Fintype.card (Σ q : {q : P.Q // P.qz q z = true},
        QZIncidentFace P ⟨(q.1, z), q.2⟩ × Two) :=
      Fintype.card_le_of_injective _ (zTriangleRoute_injective P z)
    _ ≤ zDegree P z * 8 := sigma_card_le _ 8 (by
      intro q
      have he := qzIncidentFace_card_le_four P h ⟨(q.1, z), q.2⟩
      simp only [Fintype.card_prod, Two, Fintype.card_fin]
      omega)
    _ ≤ 56 := by have hz := h.2.1 z; omega

private def qTriangleRoute (P : TannerSquarePresentation) (q : P.Q) (t : QTriangles P q) :
    Σ x : {x : P.X // P.xq x q = true}, XQIncidentFace P ⟨(x.1, q), x.2⟩ × Two := by
  let x : {x : P.X // P.xq x q = true} :=
    ⟨P.faceX t.1.1, by simpa [← t.2] using P.data.faceQ_xq t.1.1 t.1.2⟩
  exact ⟨x, ⟨t.1.1, rfl, t.1.2, t.2⟩, t.1.2⟩

private theorem qTriangleRoute_injective (P : TannerSquarePresentation) (q : P.Q) :
    Function.Injective (qTriangleRoute P q) := by
  intro a b h
  have hf := congrArg (fun s => s.2.1.1) h
  have hs := congrArg (fun s => s.2.2) h
  apply Subtype.ext
  exact Prod.ext hf hs

theorem qTriangles_card_le (P : TannerSquarePresentation) (h : BoundedValence P) (q : P.Q) :
    Fintype.card (QTriangles P q) ≤ 56 := by
  classical
  calc
    _ ≤ Fintype.card (Σ x : {x : P.X // P.xq x q = true},
        XQIncidentFace P ⟨(x.1, q), x.2⟩ × Two) :=
      Fintype.card_le_of_injective _ (qTriangleRoute_injective P q)
    _ ≤ qXDegree P q * 8 := sigma_card_le _ 8 (by
      intro x
      have he := xqIncidentFace_card_le_four P h ⟨(x.1, q), x.2⟩
      simp only [Fintype.card_prod, Two, Fintype.card_fin]
      omega)
    _ ≤ 56 := by have hq := (h.2.2 q).1; omega

end QEC.Coding.BDL26RandomPerturbation
