import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.NetCatch

/-! # Actual event avoidance gives the labeled triangulated density bound -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem avoidance_triangle_density (P : TannerSquarePresentation) (J w : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (hw : ∀ v, ‖w v‖ ≤ (6*p.m : ℕ)*(p.lambda : ℝ))
    (havoid : ∀ e : Event P J (anchorRadius p.m),
      w ∉ localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e)
    (z : Space) :
    ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  classical
  let hits := familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
    (Metric.closedBall z 1)
  have hfiber : ∀ c : Fin 3 → Fin 56,
      (hits.filter (fun a => boundedTriangleColor P hv a = c)).card ≤ 3 := by
    intro c
    by_contra h
    have hfour : 4 ≤ (hits.filter (fun a => boundedTriangleColor P hv a = c)).card := by omega
    obtain ⟨s,hsub,hcard⟩ := Finset.exists_subset_card_eq hfour
    have hsHit : ∀ a ∈ s,
        (oldTriangleImage P (perturbedMap P J p.lambda w) a ∩ Metric.closedBall z 1).Nonempty := by
      intro a ha
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hsub ha)).1).2
    have hsColor : ∀ a ∈ s, ∀ b ∈ s, triangleColor P a = triangleColor P b := by
      intro a ha b hb
      have he := (Finset.mem_filter.mp (hsub ha)).2.trans
        (Finset.mem_filter.mp (hsub hb)).2.symm
      funext i
      exact congrArg Fin.val (congrFun he i)
    have hsClose : ∀ a ∈ s, ∀ b ∈ s,
        dist (oldAnchor P J a) (oldAnchor P J b) ≤ (anchorRadius p.m : ℝ) := by
      intro a ha b hb
      have hl : (1 : ℝ) ≤ p.lambda := by exact_mod_cast p.lambda_one
      have hd := common_hits_anchor_distance P J w p.t (6*p.m : ℕ) p.lambda
        hJ hl hw a b z (hsHit a ha) (hsHit b hb)
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hd
      simp only [anchorRadius,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      linarith
    let e : Event P J (anchorRadius p.m) := ⟨s,hcard,hsColor,hsClose⟩
    exact havoid e (four_hits_mem_event P J w p.t (anchorRadius p.m) (6*p.m) p.lambda
      hJ p.lambda_one hw e z hsHit)
  have hc := Finset.card_le_mul_card_image hits 3 (fun c _ => hfiber c)
  have himage : (hits.image (boundedTriangleColor P hv)).card ≤ 56^3 := by
    calc
      _ ≤ Fintype.card (Fin 3 → Fin 56) := Finset.card_le_univ _
      _ = _ := boundedTriangleColor_card
  have hn : hits.card ≤ triangleDensityBound := by
    have hbound := hc.trans (Nat.mul_le_mul_left 3 himage)
    norm_num [triangleDensityBound] at hbound ⊢
    omega
  exact_mod_cast hn

end QEC.Coding.BDL26RandomPerturbation
