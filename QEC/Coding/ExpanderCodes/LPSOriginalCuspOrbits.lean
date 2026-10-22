import QEC.Coding.ExpanderCodes.LPSOriginalCuspNeighborhoods

/-!
# LPSOriginalCuspOrbits

Actual original cusp orbits, genuine height-preserving changes and disjoint original neighborhoods.
This internal topological geometry supplies no complex analytic filled atlas, arithmetic
modular model, good reduction, Hecke/Frobenius/Jacobian/Rosati magnitude or PK22 theorem.
The original group, source and public theorem scope remain unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

/-- The true original cusp-orbit label represented by the integral matrix acting on infinity. -/
def lpsOriginalCuspOrbit (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  cosetToCuspOrbit (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ⟦ρ⁻¹⟧

/-- Every genuine original cusp orbit has an actual integral representative. -/
lemma lpsOriginalCuspOrbit_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (lpsOriginalCuspOrbit N) := by
  intro c
  obtain ⟨x,hx⟩ := surjective_cosetToCuspOrbit
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) c
  obtain ⟨γ,rfl⟩ := Quotient.exists_rep x
  refine ⟨γ⁻¹,?_⟩
  simpa [lpsOriginalCuspOrbit] using hx

/-- A genuine original-group cusp action identifies actual cusp-orbit labels. -/
lemma lpsOriginalCuspOrbit_eq_of_original_cusp_action (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (he : g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ' • (OnePoint.infty : OnePoint ℝ))=
      Matrix.SpecialLinearGroup.mapGL ℝ ρ • (OnePoint.infty : OnePoint ℝ)) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' := by
  unfold lpsOriginalCuspOrbit
  rw [cosetToCuspOrbit_apply_mk,cosetToCuspOrbit_apply_mk]
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨⟨g,hg⟩,?_⟩
  apply Subtype.ext
  simpa only [SubMulAction.val_smul,MulAction.subgroup_smul_def,inv_inv] using he

/-- True cusp-orbit equality is exactly an actual original-group cusp action. -/
lemma lpsOriginalCuspOrbit_eq_iff_original_action (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' ↔
      ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
        g • (Matrix.SpecialLinearGroup.mapGL ℝ ρ' • (OnePoint.infty : OnePoint ℝ))=
          Matrix.SpecialLinearGroup.mapGL ℝ ρ • (OnePoint.infty : OnePoint ℝ) := by
  constructor
  · intro he
    unfold lpsOriginalCuspOrbit at he
    rw [cosetToCuspOrbit_apply_mk,cosetToCuspOrbit_apply_mk] at he
    have ho := Quotient.eq.mp he
    rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
    obtain ⟨g,hg⟩ := ho
    refine ⟨g.val,g.property,?_⟩
    have hv := congrArg Subtype.val hg
    simpa only [SubMulAction.val_smul,MulAction.subgroup_smul_def,inv_inv] using hv
  · rintro ⟨g,hg,he⟩
    exact lpsOriginalCuspOrbit_eq_of_original_cusp_action N ρ ρ' g hg he

/-- A genuine change within one original cusp orbit is a signed integral-range translation. -/
lemma lpsOriginalCuspChange_translation (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      ∃ x : ℝ,
        (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹*g*Matrix.SpecialLinearGroup.mapGL ℝ ρ'=
          Matrix.GeneralLinearGroup.upperRightHom x ∨
        (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹*g*Matrix.SpecialLinearGroup.mapGL ℝ ρ'=
          -Matrix.GeneralLinearGroup.upperRightHom x := by
  obtain ⟨g,hg,he⟩ := (lpsOriginalCuspOrbit_eq_iff_original_action N ρ ρ').mp h
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹*g*e
  have hd : d∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
    obtain ⟨γ,hγ,hγg⟩ := hg
    refine ⟨ρ⁻¹*γ*ρ',?_⟩
    simp only [map_mul,map_inv]
    rw [hγg]
  have hf : d • (OnePoint.infty : OnePoint ℝ)=OnePoint.infty := by
    simp only [d,mul_smul]
    rw [he]
    exact inv_smul_smul r OnePoint.infty
  obtain ⟨x,hx⟩ := lpsIntegralFixInfinity_translation d hd
    (OnePoint.smul_infty_eq_self_iff.mp hf)
  exact ⟨g,hg,x,hx⟩

/-- A genuine signed real translation preserves imaginary height. -/
lemma lpsSignedTranslation_im (g : GL (Fin 2) ℝ) (x : ℝ)
    (hg : g=Matrix.GeneralLinearGroup.upperRightHom x ∨
      g= -Matrix.GeneralLinearGroup.upperRightHom x) (τ : ℍ) :
    (g • τ).im=τ.im := by
  rcases hg with rfl|rfl
  · have he := congrArg Complex.im (lpsUpperRight_smul_coe x τ)
    simpa only [Complex.add_im,Complex.ofReal_im,add_zero,UpperHalfPlane.coe_im] using he
  · rw [UpperHalfPlane.neg_smul]
    have he := congrArg Complex.im (lpsUpperRight_smul_coe x τ)
    simpa only [Complex.add_im,Complex.ofReal_im,add_zero,UpperHalfPlane.coe_im] using he

/-- Changing representatives of the same true cusp preserves the original projected point and height. -/
lemma lpsOriginalCuspNeighborhood_change_point (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ')
    (σ : {τ : ℍ // 1<τ.im}) :
    ∃ τ : {τ : ℍ // 1<τ.im}, τ.val.im=σ.val.im ∧
      lpsOriginalCuspProjection N ρ τ=lpsOriginalCuspProjection N ρ' σ := by
  obtain ⟨g,hg,x,hx⟩ := lpsOriginalCuspChange_translation N ρ ρ' h
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹*g*e
  have him : 1<(d • σ.val).im := by
    rw [lpsSignedTranslation_im d x hx]
    exact σ.property
  refine ⟨⟨d • σ.val,him⟩,lpsSignedTranslation_im d x hx σ.val,?_⟩
  apply Quotient.eq.mpr
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
  refine ⟨⟨g,hg⟩,?_⟩
  change g • (e • σ.val)=r • (d • σ.val)
  simp only [d,mul_smul,smul_inv_smul]

/-- The true cusp-representative change transports the whole original neighborhood. -/
lemma lpsOriginalCuspNeighborhood_range_subset (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    Set.range (lpsOriginalCuspProjection N ρ')⊆Set.range (lpsOriginalCuspProjection N ρ) := by
  rintro y ⟨σ,rfl⟩
  obtain ⟨τ,ht,he⟩ := lpsOriginalCuspNeighborhood_change_point N ρ ρ' h σ
  exact ⟨τ,he⟩

/-- Representatives of the same actual cusp give the same original neighborhood. -/
lemma lpsOriginalCuspNeighborhood_range_eq (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    Set.range (lpsOriginalCuspProjection N ρ)=Set.range (lpsOriginalCuspProjection N ρ') :=
  Set.Subset.antisymm (lpsOriginalCuspNeighborhood_range_subset N ρ' ρ h.symm)
    (lpsOriginalCuspNeighborhood_range_subset N ρ ρ' h)

/-- Choose an actual integral representative of each true original cusp orbit. -/
def lpsOriginalCuspRepresentative (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) : SL(2,ℤ) :=
  Classical.choose (lpsOriginalCuspOrbit_surjective N c)

/-- The selected integral representative realizes its true original cusp label. -/
lemma lpsOriginalCuspRepresentative_orbit (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    lpsOriginalCuspOrbit N (lpsOriginalCuspRepresentative N c)=c :=
  Classical.choose_spec (lpsOriginalCuspOrbit_surjective N c)

/-- The selected representative preserves the actual original cusp neighborhood. -/
lemma lpsOriginalCuspRepresentative_range (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Set.range (lpsOriginalCuspProjection N
      (lpsOriginalCuspRepresentative N (lpsOriginalCuspOrbit N ρ)))=
        Set.range (lpsOriginalCuspProjection N ρ) :=
  lpsOriginalCuspNeighborhood_range_eq N _ ρ (lpsOriginalCuspRepresentative_orbit N _)

/-- An overlap of true high neighborhoods forces equality of actual cusp orbits. -/
lemma lpsOriginalCuspNeighborhood_overlap_cuspOrbit (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (τ σ : {τ : ℍ // 1<τ.im})
    (he : lpsOriginalCuspProjection N ρ τ=lpsOriginalCuspProjection N ρ' σ) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' := by
  have ho := Quotient.eq.mp he
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
  obtain ⟨g,hg⟩ := ho
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹*g.val*e
  have hd : d∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
    obtain ⟨γ,hγ,hγg⟩ := g.property
    refine ⟨ρ⁻¹*γ*ρ',?_⟩
    simp only [map_mul,map_inv]
    rw [hγg]
  have hs : d • σ.val=τ.val := by
    change (r⁻¹*g.val*e) • σ.val=τ.val
    simp only [mul_smul]
    change r⁻¹ • (g • (e • σ.val))=τ.val
    rw [hg]
    exact inv_smul_smul r τ.val
  have hz := lpsIntegralHoroball_lowerLeft_zero d hd σ.val σ.property (hs ▸ τ.property)
  have hf : d • (OnePoint.infty : OnePoint ℝ)=OnePoint.infty := OnePoint.smul_infty_eq_self_iff.mpr hz
  apply lpsOriginalCuspOrbit_eq_of_original_cusp_action N ρ ρ' g.val g.property
  have ht := congrArg (fun c : OnePoint ℝ => r • c) hf
  simpa only [d,mul_smul,smul_inv_smul] using ht

/-- Different genuine cusps have disjoint original high neighborhoods. -/
lemma lpsOriginalCuspNeighborhood_disjoint (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ≠lpsOriginalCuspOrbit N ρ') :
    Disjoint (Set.range (lpsOriginalCuspProjection N ρ))
      (Set.range (lpsOriginalCuspProjection N ρ')) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨τ,rfl⟩ ⟨σ,he⟩
  exact h (lpsOriginalCuspNeighborhood_overlap_cuspOrbit N ρ ρ' τ σ he.symm)

end
end QEC.Coding.TannerLiftedProduct
