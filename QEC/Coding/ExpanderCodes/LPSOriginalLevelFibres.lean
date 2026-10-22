import QEC.Coding.ExpanderCodes.LPSOriginalLevelMapGeometry
import QEC.Coding.ExpanderCodes.LPSHeckeCosetCover
/-!
# Genuine original modular level fibres

The actual nonnormal integral Gamma0 left cosets biject with the entire original
interior fibre. The proof uses the actual central ±I stabilizers; it assumes
neither freeness nor normality. The filled map has no cusp preimages of interior
points. For prime p coprime to N and 4 dividing N, the SAME original filled
level-Np map has p+1 preimages of every genuine lower interior point.

This is internal mathematics for the original LPS/Hecke route behind pinned
PK22 main.tex ex:Xpq:484–486 and th:qLDPC:231–238, not a direct source assertion
of these separate modular-curve lemmas. Global ramified covering theory, second
Hecke degeneracy, arithmetic normalization and good reduction, Frobenius/Weil,
the LPS spectrum and the exact arbitrary-field quantum family remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

lemma lpsOriginalLevelInterior_representative_eq_iff
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N) (τ : ℍ)
    (γ₁ γ₂ : CongruenceSubgroup.Gamma0 N) :
    (⟦Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ))⁻¹ • τ⟧ :
      MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ) =
      ⟦Matrix.SpecialLinearGroup.mapGL ℝ (γ₂ : SL(2,ℤ))⁻¹ • τ⟧ ↔
      (γ₁ : SL(2,ℤ))⁻¹ * (γ₂ : SL(2,ℤ)) ∈ CongruenceSubgroup.Gamma0 M := by
  constructor
  · intro he
    have hr := Quotient.exact he.symm
    change MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ₂ : SL(2,ℤ))⁻¹ • τ)
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ))⁻¹ • τ) at hr
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
    obtain ⟨δ,hδ⟩ := hr
    obtain ⟨d,hd,hmap⟩ := δ.property
    change δ.val • (Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ))⁻¹ • τ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (γ₂ : SL(2,ℤ))⁻¹ • τ at hδ
    rw [← hmap] at hδ
    let k : SL(2,ℤ) := (γ₂ : SL(2,ℤ)) * d * (γ₁ : SL(2,ℤ))⁻¹
    have hk : k ∈ CongruenceSubgroup.Gamma0 N :=
      (CongruenceSubgroup.Gamma0 N).mul_mem
        ((CongruenceSubgroup.Gamma0 N).mul_mem γ₂.property
          ((lpsGamma0_level_le N M hNM) hd))
        ((CongruenceSubgroup.Gamma0 N).inv_mem γ₁.property)
    have hfix : Matrix.SpecialLinearGroup.mapGL ℝ k • τ = τ := by
      change Matrix.SpecialLinearGroup.mapGL ℝ
        ((γ₂ : SL(2,ℤ)) * d * (γ₁ : SL(2,ℤ))⁻¹) • τ = τ
      rw [map_mul,map_mul,mul_smul,mul_smul,hδ,←mul_smul,←map_mul]
      simp only [mul_inv_cancel,map_one,one_smul]
    have hc := lpsGamma0_fixed_mapGL N hN k hk τ hfix
    apply (Subgroup.mem_map_iff_mem (Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (S := ℝ))).mp
    have hi : Matrix.SpecialLinearGroup.mapGL ℝ
        ((γ₁ : SL(2,ℤ))⁻¹*(γ₂ : SL(2,ℤ))) =
        (Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ)))⁻¹ *
        Matrix.SpecialLinearGroup.mapGL ℝ k *
        Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ)) *
        (Matrix.SpecialLinearGroup.mapGL ℝ d)⁻¹ := by
      simp only [k,map_mul,map_inv,mul_assoc,mul_inv_cancel,
        mul_one,inv_mul_cancel]
    rw [hi]
    have hdR : Matrix.SpecialLinearGroup.mapGL ℝ d ∈
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) :=
      ⟨d,hd,rfl⟩
    rcases hc with hp | hm
    · rw [hp]
      simpa only [mul_one,inv_mul_cancel,one_mul] using
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).inv_mem hdR
    · rw [hm]
      have hz : (Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ)))⁻¹ *
          (-1 : GL (Fin 2) ℝ) * Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ)) =
          -1 := by
        simp only [mul_neg,mul_one,neg_mul,inv_mul_cancel]
      rw [hz]
      exact (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).mul_mem
        (lpsGamma0_neg_one_mem M)
        ((CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).inv_mem hdR)
  · intro h
    apply Quotient.sound
    change MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ₁ : SL(2,ℤ))⁻¹ • τ)
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ₂ : SL(2,ℤ))⁻¹ • τ)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ
      ((γ₁ : SL(2,ℤ))⁻¹*(γ₂ : SL(2,ℤ))),⟨_,h,rfl⟩⟩,?_⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ
      ((γ₁ : SL(2,ℤ))⁻¹*(γ₂ : SL(2,ℤ))) •
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ₂ : SL(2,ℤ))⁻¹ • τ) = _
    rw [←mul_smul,←map_mul]
    simp only [mul_assoc,mul_inv_cancel,mul_one]

/-- The actual representative map from original left cosets into the genuine interior fibre. -/
def lpsOriginalLevelInteriorCosetToFibre
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N) (τ : ℍ) :
    CongruenceSubgroup.Gamma0 N ⧸
      (CongruenceSubgroup.Gamma0 M).subgroupOf (CongruenceSubgroup.Gamma0 N) →
    {y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ |
      lpsOriginalInteriorForgetLevel N M hNM y = ⟦τ⟧} :=
  Quotient.lift (fun γ : CongruenceSubgroup.Gamma0 N =>
    ⟨⟦Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2,ℤ))⁻¹ • τ⟧, by
      change lpsOriginalInteriorForgetLevel N M hNM
        ⟦Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2,ℤ))⁻¹ • τ⟧ = ⟦τ⟧
      rw [lpsOriginalInteriorForgetLevel_projection]
      apply Quotient.sound
      change MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ _ _
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2,ℤ))⁻¹,
        ⟨_, (CongruenceSubgroup.Gamma0 N).inv_mem γ.property, rfl⟩⟩, rfl⟩⟩)
    (by
      intro γ₁ γ₂ h
      apply Subtype.ext
      apply (lpsOriginalLevelInterior_representative_eq_iff N M hNM hN τ γ₁ γ₂).mpr
      have he : (QuotientGroup.mk γ₁ : CongruenceSubgroup.Gamma0 N ⧸
          (CongruenceSubgroup.Gamma0 M).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
          QuotientGroup.mk γ₂ := Quotient.sound h
      exact (Subgroup.mem_subgroupOf).mp (QuotientGroup.eq.mp he))

/-- Evaluation uses the inverse of the original integral actor. -/
lemma lpsOriginalLevelInteriorCosetToFibre_mk
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N) (τ : ℍ)
    (γ : CongruenceSubgroup.Gamma0 N) :
    (lpsOriginalLevelInteriorCosetToFibre N M hNM hN τ
      (QuotientGroup.mk γ)).val =
      ⟦Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2,ℤ))⁻¹ • τ⟧ := rfl

/-- The true original representative map is bijective, using the proved central stabilizers. -/
lemma lpsOriginalLevelInteriorCosetToFibre_bijective
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N) (τ : ℍ) :
    Function.Bijective (lpsOriginalLevelInteriorCosetToFibre N M hNM hN τ) := by
  constructor
  · intro a b he
    induction a using QuotientGroup.induction_on with
    | H γ₁ =>
      induction b using QuotientGroup.induction_on with
      | H γ₂ =>
        apply QuotientGroup.eq.mpr
        change (γ₁ : SL(2,ℤ))⁻¹ * (γ₂ : SL(2,ℤ)) ∈ CongruenceSubgroup.Gamma0 M
        apply (lpsOriginalLevelInterior_representative_eq_iff N M hNM hN τ γ₁ γ₂).mp
        exact congrArg Subtype.val he
  · intro y
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep y.val
    have he : (⟦σ⟧ : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) = ⟦τ⟧ := by
      rw [←lpsOriginalInteriorForgetLevel_projection N M hNM σ, hσ]
      exact y.property
    have hr := Quotient.exact he
    change MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ σ τ at hr
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
    obtain ⟨δ,hδ⟩ := hr
    obtain ⟨d,hd,hmap⟩ := δ.property
    let γ : CongruenceSubgroup.Gamma0 N := ⟨d,hd⟩
    refine ⟨QuotientGroup.mk γ⁻¹,?_⟩
    apply Subtype.ext
    rw [lpsOriginalLevelInteriorCosetToFibre_mk]
    change (⟦Matrix.SpecialLinearGroup.mapGL ℝ (d⁻¹)⁻¹ • τ⟧ :
      MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ) = y.val
    rw [inv_inv,hmap]
    change (⟦δ.val • τ⟧ : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ) = y.val
    change δ.val • τ = σ at hδ
    rw [hδ,hσ]

/-- The actual nonnormal original left cosets are equivalent to the entire interior fibre. -/
def lpsOriginalLevelInteriorCosetFibreEquiv
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N) (τ : ℍ) :
    CongruenceSubgroup.Gamma0 N ⧸
      (CongruenceSubgroup.Gamma0 M).subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
    {y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ |
      lpsOriginalInteriorForgetLevel N M hNM y = ⟦τ⟧} :=
  Equiv.ofBijective (lpsOriginalLevelInteriorCosetToFibre N M hNM hN τ)
    (lpsOriginalLevelInteriorCosetToFibre_bijective N M hNM hN τ)

/-- Every actual interior fibre has cardinality the genuine relative subgroup index. -/
lemma lpsOriginalInteriorForgetLevel_fibre_card
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    Nat.card {x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ |
      lpsOriginalInteriorForgetLevel N M hNM x = y} =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
  exact (Nat.card_congr (lpsOriginalLevelInteriorCosetFibreEquiv N M hNM hN τ)).symm

/-- An actual filled fibre over an interior point contains exactly its interior fibre. -/
def lpsOriginalFilledInteriorFibreEquiv
    (N M : ℕ) (hNM : N ∣ M)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    {x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ |
      lpsOriginalInteriorForgetLevel N M hNM x = y} ≃
    {x : LPSOriginalFilledCurve M |
      lpsOriginalFilledForgetLevel N M hNM x = Sum.inl y} :=
  Equiv.ofBijective
    (fun x => ⟨Sum.inl x.val, congrArg Sum.inl x.property⟩)
    (by
      constructor
      · intro a b he
        apply Subtype.ext
        exact Sum.inl.inj (congrArg Subtype.val he)
      · intro x
        rcases x with ⟨x,hx⟩
        cases x with
        | inl z =>
          refine ⟨⟨z,Sum.inl.inj hx⟩,?_⟩
          rfl
        | inr c => cases hx)

/-- The SAME original filled level-Np map has a full actual p+1 fibre equivalence. -/
def lpsOriginalPrimeLevelFilledFibreEquiv
    (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N) (τ : ℍ) :
    {x : LPSOriginalFilledCurve (N*p) |
      lpsOriginalFilledForgetLevel N (N*p) (dvd_mul_right N p) x = Sum.inl ⟦τ⟧} ≃
      Option (Fin p) :=
  (lpsOriginalFilledInteriorFibreEquiv N (N*p) (dvd_mul_right N p) ⟦τ⟧).symm.trans
    ((lpsOriginalLevelInteriorCosetFibreEquiv N (N*p) (dvd_mul_right N p) hN τ).symm.trans
      (lpsHeckeIntersectionCosetEquiv N p hNp))

/-- Every genuine interior point has p+1 preimages under the actual original filled map. -/
lemma lpsOriginalFilledForgetLevel_prime_fibre_card
    (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    Nat.card {x : LPSOriginalFilledCurve (N*p) |
      lpsOriginalFilledForgetLevel N (N*p) (dvd_mul_right N p) x = Sum.inl y} = p+1 := by
  obtain ⟨τ,rfl⟩ := Quotient.exists_rep y
  rw [Nat.card_congr (lpsOriginalPrimeLevelFilledFibreEquiv N p hNp hN τ),
    Nat.card_eq_fintype_card]
  simp

end
end QEC.Coding.TannerLiftedProduct
