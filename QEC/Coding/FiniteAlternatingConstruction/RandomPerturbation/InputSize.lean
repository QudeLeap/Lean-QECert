import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Incidence

/-!
# Actual input cardinality versus qubit count

Admissibility, not an upper degree bound alone, rules out isolated X/Z vertices.
A boundary root exhibits an incident face. Perfect pairing bounds face fibers.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26TannerLocalRegularity

/-- An actual X-star boundary root supplies a face, even without a chosen edge. -/
theorem faceX_surjective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Surjective P.faceX := by
  intro x
  obtain ⟨v,hv⟩ := A.xBoundaryRoot x
  cases v with
  | x y => simp [xStarBoundaryVertexMember] at hv
  | q q =>
    simp [xStarBoundaryVertexMember, xStarFaceMember] at hv
    obtain ⟨f,hf,_⟩ := hv
    exact ⟨f,hf⟩
  | z z =>
    simp [xStarBoundaryVertexMember, xStarFaceMember] at hv
    obtain ⟨f,hf,_⟩ := hv
    exact ⟨f,hf⟩

theorem faceZ_surjective (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) :
    Function.Surjective P.faceZ := by
  intro z
  obtain ⟨v,hv⟩ := A.zBoundaryRoot z
  cases v with
  | x x =>
    simp [zStarBoundaryVertexMember, zStarFaceMember] at hv
    obtain ⟨f,hf,_⟩ := hv
    exact ⟨f,hf⟩
  | q q =>
    simp [zStarBoundaryVertexMember, zStarFaceMember] at hv
    obtain ⟨f,hf,_⟩ := hv
    exact ⟨f,hf⟩
  | z y => simp [zStarBoundaryVertexMember] at hv

private def faceRoute (P : TannerSquarePresentation) (f : P.Face) :
    Σ q : P.Q, Σ x : {x : P.X // P.xq x q = true}, XQIncidentFace P ⟨(x.1,q),x.2⟩ :=
  ⟨P.faceQ f 0, ⟨P.faceX f,P.data.faceQ_xq f 0⟩, ⟨f,rfl,0,rfl⟩⟩

private theorem faceRoute_injective (P : TannerSquarePresentation) :
    Function.Injective (faceRoute P) := by
  intro a b h
  exact congrArg (fun s => s.2.2.1) h

/-- Conservative linear face count directly from the two Q-side degree bounds. -/
theorem face_card_le_qubits (P : TannerSquarePresentation) (h : BoundedValence P) :
    Fintype.card P.Face ≤ 16 * Fintype.card P.Q := by
  classical
  calc
    _ ≤ Fintype.card (Σ q : P.Q, Σ x : {x : P.X // P.xq x q = true},
        XQIncidentFace P ⟨(x.1,q),x.2⟩) := Fintype.card_le_of_injective _ (faceRoute_injective P)
    _ = ∑ q : P.Q, ∑ x : {x : P.X // P.xq x q = true},
        Fintype.card (XQIncidentFace P ⟨(x.1,q),x.2⟩) := by simp only [Fintype.card_sigma]
    _ ≤ ∑ _ : P.Q, 16 := by
      apply Finset.sum_le_sum
      intro q _
      calc
        _ ≤ ∑ _ : {x : P.X // P.xq x q = true}, 4 :=
          Finset.sum_le_sum fun x _ => xqIncidentFace_card_le_four P h _
        _ = qXDegree P q * 4 := by simp [qXDegree]
        _ ≤ 16 := by have hq := (h.2.2 q).1; omega
    _ = 16 * Fintype.card P.Q := by simp [mul_comm]

/-- All labels used by the event algorithm are controlled by actual qubit count. -/
theorem input_labels_le_qubits (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (h : BoundedValence P) :
    Fintype.card P.X + Fintype.card P.Q + Fintype.card P.Z +
      Fintype.card (Triangle P) ≤ 65 * Fintype.card P.Q := by
  have hx := Fintype.card_le_of_surjective P.faceX (faceX_surjective P A)
  have hz := Fintype.card_le_of_surjective P.faceZ (faceZ_surjective P A)
  have hf := face_card_le_qubits P h
  change Fintype.card P.X ≤ Fintype.card P.Face at hx
  change Fintype.card P.Z ≤ Fintype.card P.Face at hz
  simp only [Triangle,Fintype.card_prod,Two,Fintype.card_fin]
  omega

end QEC.Coding.BDL26RandomPerturbation
