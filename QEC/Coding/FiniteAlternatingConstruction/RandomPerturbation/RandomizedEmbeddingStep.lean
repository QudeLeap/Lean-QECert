import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.ExpectedOperationCost

/-! # The complete internal randomized perturbation step for approved source841 statement P

Numerical parameters are chosen before the presentation, level or input size.
This step retains every P.Face × Two label. The full recursive public theorem
and deterministic replacement application remain separate downstream tasks.
-/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

/-- The actual canonical least odd source scale; its threshold is derived from p. -/
noncomputable def perturbationOddScale {L : ℝ} (p : GeometricParameters L) : OddScale :=
  BDL26QuantitativeBounds.leastOddScaleAbove ((2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ)) (by have h := p.rounding; linarith)

theorem perturbationOddScale_bounds {L : ℝ} (p : GeometricParameters L) :
    (2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ) < (perturbationOddScale p).ell ∧
      ((perturbationOddScale p).ell : ℝ) ≤ (2*(6*(p.m : ℝ))+1)*(p.lambda : ℝ)+2 :=
  by simpa only [perturbationOddScale] using canonical_replacement_scale_bounds p.rounding

/-- The measured positive-probability event has actual geometry and labeled density. -/
theorem supported_avoidance_geometry_density (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (w : Vertex P → Space) (hw : w ∈ geometricSupport P p ∩ geometricAvoidance P J p) :
    IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨geometricSupport_incoming_geometry P J p hJ (perturbationOddScale p)
    (perturbationOddScale_bounds p).1.le w hw.1,?_⟩
  intro z
  exact avoidance_triangle_density P J w p hJ hv (fun v => (hw.1 v).1.le)
    (fun e => hw.2 e (Finset.mem_univ e)) z

theorem geometric_output_geometry_density_ae (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      Halts (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      IncomingFaceGeometry P (perturbationOddScale p)
        (perturbedMap P J p.lambda (geometricOutput P J p T))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (geometricOutput P J p T)))
          (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  filter_upwards [geometric_execution_good_ae P J p hJ hv] with T hT
  have hg := supported_avoidance_geometry_density P J p hJ hv (geometricOutput P J p T)
    ⟨hT.2.1,hT.2.2⟩
  exact ⟨hT.1,hg⟩

/-- The actual emitted embedding consists of the counted perturbed coordinates. -/
noncomputable def perturbationEmbeddingOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) : Vertex P → Space :=
  perturbedMap P J p.lambda (geometricOutput P J p T)

theorem measurable_perturbationEmbeddingOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Measurable (perturbationEmbeddingOutput P J p) := by
  apply measurable_pi_lambda
  intro v
  exact measurable_const.add ((measurable_pi_apply v).comp (measurable_geometricOutput P J p))

/-- The counted output loop emits exactly the measurable geometric execution map. -/
theorem actual_emitted_embedding_rows (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (T : Table (X := fun _ : Vertex P => Space)) :
    (outputStateRowsQuery P J p.lambda
      (actualPrefixQuery P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
        (eventUniverseQuery P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1 T
        (haltTime (eventSupport P J (anchorRadius p.m))
          (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T)).1).1 =
      (vertexInputList P).map (fun v => (v,perturbationEmbeddingOutput P J p T v)) := by
  simp only [perturbationEmbeddingOutput,perturbedMap,geometricOutput,output]
  exact outputStateRowsQuery_value P J p.lambda T _ _
    (actualPrefixQuery_rep P J (by positivity) p.lambda ((6*p.m+2)*p.lambda) T _)

/-- Joint size/depth-independent constants with finite-law and actual algorithm guarantees. -/
theorem randomized_embedding_step (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower,
      (0 : ℝ) < triangleDensityBound ∧ (triangleDensityBound : ℝ) < p.t ∧
      ∀ (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (J : Vertex P → Space),
        IsBoundedDensityLocalMap P J p.t → BoundedValence P →
        letI (v : Vertex P) := vertexLaw_probability P
          ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
        0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) ∧
        Measurable (perturbationEmbeddingOutput P J p) ∧
        (∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
          Halts (eventSupport P J (anchorRadius p.m))
            (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
          IncomingFaceGeometry P (perturbationOddScale p)
            (perturbedMap P J p.lambda (geometricOutput P J p T))
            (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
          ∀ z, ((familyHits (oldTriangleImage P
            (perturbedMap P J p.lambda (geometricOutput P J p T)))
              (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound) ∧
        (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
          p.lambda ((6*p.m+2)*p.lambda) T
          ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
            (operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 : ℕ) := by
  obtain ⟨p⟩ := geometricParameters_nonempty densityLower
  refine ⟨p,by norm_num [triangleDensityBound],p.triangle_density,?_⟩
  intro P A J hJ hv
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  exact ⟨supported_avoidance_positive P J p hJ hv,measurable_perturbationEmbeddingOutput P J p,
    geometric_output_geometry_density_ae P J p hJ hv,
    geometric_expected_operations_le_qubits P J A p hJ hv⟩

end QEC.Coding.BDL26RandomPerturbation
