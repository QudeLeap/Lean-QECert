import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.TriangleMinimum

/-! # Singular triangles lie on one of their three closed edges -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace

theorem collinear_weights_on_edge (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) (k : ℝ)
    (hk : a 2-a 0 = k • (a 1-a 0)) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by
  have hs := w.property.2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  change w.val 0+(w.val 1+w.val 2) = 1 at hs
  have h0 := w.property.1 0
  have h1 := w.property.1 1
  have h2 := w.property.1 2
  let s : ℝ := w.val 1+w.val 2*k
  have hy : barycenterMap a w = a 0+s • (a 1-a 0) := by
    rw [barycenter_affine_coordinates,hk]
    dsimp [s]
    module
  by_cases hk0 : k ≤ 0
  · have hd : 0 < 1-k := by linarith
    have hsk : k ≤ s := by
      dsimp [s]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hk0 h0,
        mul_nonpos_of_nonpos_of_nonneg hk0 h1]
    have hs1 : s ≤ 1 := by
      dsimp [s]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hk0]
    refine ⟨1,2,by decide,(1-s)/(1-k),div_nonneg (by linarith) hd.le,?_,?_⟩
    · apply (div_le_one hd).mpr
      linarith
    · have hc : ((1-s)/(1-k))*(k-1) = s-1 := by
        field_simp [hd.ne']
        <;> ring
      have ha2 : a 2 = a 0+k • (a 1-a 0) := by
        calc
          a 2 = k • (a 1-a 0)+a 0 := sub_eq_iff_eq_add.mp hk
          _ = _ := by abel
      rw [hy,ha2]
      have he : a 0+s • (a 1-a 0) =
          a 1+(((1-s)/(1-k))*(k-1)) • (a 1-a 0) := by
        rw [hc]
        module
      calc
        a 0+s • (a 1-a 0) = _ := he
        _ = _ := by module
  · have hk0' : 0 ≤ k := le_of_lt (lt_of_not_ge hk0)
    by_cases hk1 : k ≤ 1
    · have hs0 : 0 ≤ s := add_nonneg h1 (mul_nonneg h2 hk0')
      have hs1 : s ≤ 1 := by
        dsimp [s]
        nlinarith [mul_nonneg h2 (sub_nonneg.mpr hk1)]
      exact ⟨0,1,by decide,s,hs0,hs1,hy⟩
    · have hkpos : 0 < k := by linarith
      have hs0 : 0 ≤ s := add_nonneg h1 (mul_nonneg h2 hk0')
      have hsk : s ≤ k := by
        dsimp [s]
        nlinarith [mul_nonneg h0 hk0',mul_nonneg h1 (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hk1)))]
      refine ⟨0,2,by decide,s/k,div_nonneg hs0 hkpos.le,
        (div_le_one hkpos).mpr hsk,?_⟩
      rw [hy,hk,smul_smul,div_mul_cancel₀ _ hkpos.ne']

/-- The singular Gram case includes repeated vertices and collinear triples. -/
theorem singular_weights_on_edge (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) (hdet : gramDet (a 1-a 0) (a 2-a 0) = 0) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by
  by_cases hb : a 1-a 0 = 0
  · have hs := w.property.2
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
    change w.val 0+(w.val 1+w.val 2) = 1 at hs
    refine ⟨0,2,by decide,w.val 2,w.property.1 2,?_,?_⟩
    · linarith [w.property.1 0,w.property.1 1]
    · rw [barycenter_affine_coordinates,hb]
      simp
  · exact collinear_weights_on_edge a w _ (gramDet_zero_collinear _ _ hb hdet)

end QEC.Coding.BDL26RandomPerturbation
