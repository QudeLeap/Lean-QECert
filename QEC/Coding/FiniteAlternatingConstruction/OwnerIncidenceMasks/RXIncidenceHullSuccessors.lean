import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.RXIncidenceHullGrowth

noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth

/-- Both endpoints of each actual Q-cylinder edge have its actual successor
Z incidence, exhibited by the original X-Q glue face. -/
theorem rx_q_endpoint_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge P q S) (endpoint : BDL26FiniteTannerSquare.Two) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q, BDL26RXLocalReplacement.edgeEndpoint
        (qDoubleCylinderEdgeStart P q S) (qDoubleCylinderEdgeEnd P q S) edge endpoint⟩)
      (Sum.inl (Sum.inr ⟨q,edge⟩)) = true := by
  let a : XQEdge P := ⟨((A.xqRoot q).1,q),(A.xqRoot q).2⟩
  let face : RXFace P S := Sum.inr (Sum.inl ⟨a,edge,endpoint⟩)
  apply (rxQZIncidence_eq_true_iff P S _ _).mpr
  refine ⟨face,1,?_,rfl⟩
  simp [face,rxFaceQ,twoSelect,glueFaceQ1,a]

theorem rx_q_start_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge P q S) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q,qDoubleCylinderEdgeStart P q S edge⟩)
      (Sum.inl (Sum.inr ⟨q,edge⟩)) = true := by
  simpa only [BDL26RXLocalReplacement.edgeEndpoint, BDL26RXLocalReplacement.twoSelect_zero]
    using rx_q_endpoint_incidence P A S q edge 0

theorem rx_q_end_incidence (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (edge : QDoubleCylinderEdge P q S) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q,qDoubleCylinderEdgeEnd P q S edge⟩)
      (Sum.inl (Sum.inr ⟨q,edge⟩)) = true := by
  simpa only [BDL26RXLocalReplacement.edgeEndpoint, BDL26RXLocalReplacement.twoSelect_one]
    using rx_q_endpoint_incidence P A S q edge 1

/-- The constructive local cylinder path induces a path of actual successor
Q coordinates sharing actual successor Z checks. -/
theorem rx_q_path_map (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    {u v : QDoubleCylinderVertex P q S}
    (path : UndirectedPath (qDoubleCylinderEdgeStart P q S)
      (qDoubleCylinderEdgeEnd P q S) u v) :
    SharedZPath (rxReplacementPresentation P S) (Sum.inr ⟨q,u⟩) (Sum.inr ⟨q,v⟩) := by
  induction path with
  | nil => exact .refl _
  | @step u v path edge connects ih =>
      rcases connects with ⟨hs,he⟩ | ⟨hs,he⟩
      · exact .snoc ih (Sum.inl (Sum.inr ⟨q,edge⟩))
          (hs ▸ rx_q_start_incidence P A S q edge)
          (he ▸ rx_q_end_incidence P A S q edge)
      · exact .snoc ih (Sum.inl (Sum.inr ⟨q,edge⟩))
          (he ▸ rx_q_end_incidence P A S q edge)
          (hs ▸ rx_q_start_incidence P A S q edge)

/-- Every vertex in the actual Q-local cylinder lies in its root component,
including both copies and all interior and endpoint coordinates. -/
theorem rx_q_cylinder_connected (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (u v : QDoubleCylinderVertex P q S) :
    SharedZPath (rxReplacementPresentation P S) (Sum.inr ⟨q,u⟩) (Sum.inr ⟨q,v⟩) :=
  (rx_q_path_map P A S q (qDoubleCylinderPath P A q S u)).symm.trans
    (rx_q_path_map P A S q (qDoubleCylinderPath P A q S v))

/-- Every old Q--Z incidence has a materialized old-face corner. -/
theorem old_qz_face (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    ∃ f : P.Face, ∃ corner : BDL26FiniteTannerSquare.Two, P.faceQ f corner = q ∧ P.faceZ f = z := by
  let x := A.xqRoot q
  let shared : SharedQ P.data x.1 z := ⟨q,by simp [x.2,hqz]⟩
  obtain ⟨⟨f,corner⟩,he⟩ := (P.perfectPairing x.1 z).2 shared
  exact ⟨f.1,corner,congrArg Subtype.val he,f.2.2⟩

/-- Old Z copy zero joins every incident old Q-cylinder endpoint. -/
theorem rx_old_z_incidence (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    (rxReplacementPresentation P S).qz
      (Sum.inr ⟨q,(0,Sum.inl (Sum.inr (⟨z,hqz⟩ : QStarEdge P q)))⟩)
      (Sum.inr (z,0)) = true := by
  obtain ⟨f,corner,hq,hz⟩ := old_qz_face P A q z hqz
  subst q
  subst z
  let face : RXFace P S := Sum.inr (Sum.inr (f,0))
  apply (rxQZIncidence_eq_true_iff P S _ _).mpr
  refine ⟨face,corner,?_,?_⟩
  · rfl
  · rfl

/-- A retained centre in either copy of an old Q cylinder. -/
def rxRoot (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) :
    (rxReplacementPresentation P S).Q := Sum.inr ⟨q,(copy,Sum.inl (Sum.inl ()))⟩

/-- A shared old Z gives a genuine path between any two retained root copies. -/
theorem rx_shared_z_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q r : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (hrz : P.qz r z = true) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rxReplacementPresentation P S) (rxRoot P S q a) (rxRoot P S r b) := by
  let u : QDoubleCylinderVertex P q S := (0,Sum.inl (Sum.inr ⟨z,hqz⟩))
  let v : QDoubleCylinderVertex P r S := (0,Sum.inl (Sum.inr ⟨z,hrz⟩))
  have first := rx_q_cylinder_connected P A S q (a,Sum.inl (Sum.inl ())) u
  have middle : SharedZPath (rxReplacementPresentation P S)
      (Sum.inr ⟨q,u⟩) (Sum.inr ⟨r,v⟩) :=
    .snoc (.refl _) (Sum.inr (z,0)) (rx_old_z_incidence P A S q z hqz)
      (rx_old_z_incidence P A S r z hrz)
  exact first.trans (middle.trans
    (rx_q_cylinder_connected P A S r v (b,Sum.inl (Sum.inl ()))))

/-- Every original component path lifts while each old Q supplies BOTH
retained copies, without assuming connectivity of the entire successor. -/
theorem rx_path_roots (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) {q r : P.Q} (path : SharedZPath P q r) (a b : BDL26FiniteTannerSquare.Two) :
    SharedZPath (rxReplacementPresentation P S) (rxRoot P S q a) (rxRoot P S r b) := by
  induction path generalizing a b with
  | refl => exact rx_q_cylinder_connected P A S _ _ _
  | @snoc r t path z left right ih =>
      exact (ih a 0).trans (rx_shared_z_roots P A S r t z left right 0 b)

end QEC.Coding.BDL26RXIncidenceHullSuccessors
end
