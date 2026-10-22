import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.IndexSelection
import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.ResidueRepresentation

/-!
# The determinant-class quotient of PGL

This file identifies the quotient of `PGL_d(K)` by the image of `SL_d(K)`
with determinant classes modulo `d`th powers.  It supplies the group-theoretic
bridge used by the LSV `whatisr` and `Chooseorder` steps.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped MatrixGroups

namespace ProjectiveIndex

variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]

abbrev DetPowerClass :=
  Kˣ ⧸ (powMonoidHom (Fintype.card n) : Kˣ →* Kˣ).range

/-- Determinant modulo `d`th powers descends from `GL_d` to `PGL_d`. -/
noncomputable def projectiveDetClass :
    PGL(n, K) →* DetPowerClass n K :=
  Matrix.ProjGenLinGroup.lift
    ((QuotientGroup.mk'
      (powMonoidHom (Fintype.card n) : Kˣ →* Kˣ).range).comp
        Matrix.GeneralLinearGroup.det) <| by
    ext u
    change QuotientGroup.mk' _
      (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar n u)) = 1
    rw [Matrix.GeneralLinearGroup.det_scalar]
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨u, rfl⟩

omit [Nonempty n] in
theorem projectiveDetClass_mk
    (g : Matrix.GeneralLinearGroup n K) :
    projectiveDetClass n K (Matrix.ProjGenLinGroup.mk g) =
      QuotientGroup.mk' _ (Matrix.GeneralLinearGroup.det g) :=
  rfl

omit [Fintype K] in
/-- Determinant on `GL_d(K)` is onto when the index type is nonempty. -/
theorem generalLinear_det_surjective :
    Function.Surjective
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup n K →* Kˣ) := by
  intro u
  let i0 : n := Classical.choice (inferInstance : Nonempty n)
  let f : n → K := fun i => if i = i0 then (u : K) else 1
  let fInv : n → K := fun i => if i = i0 then (u⁻¹ : Kˣ) else 1
  let fu : (n → K)ˣ :=
    { val := f
      inv := fInv
      val_inv := by
        funext i
        by_cases hi : i = i0 <;> simp [f, fInv, hi]
      inv_val := by
        funext i
        by_cases hi : i = i0 <;> simp [f, fInv, hi] }
  let A : Matrix.GeneralLinearGroup n K :=
    Units.map (Matrix.diagonalRingHom n K).toMonoidHom fu
  refine ⟨A, ?_⟩
  apply Units.ext
  change Matrix.det (Matrix.diagonal f) = (u : K)
  rw [Matrix.det_diagonal]
  classical
  simp [f, i0]

/-- The projective determinant-class map is onto. -/
theorem projectiveDetClass_surjective :
    Function.Surjective (projectiveDetClass n K) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro u
  obtain ⟨A, hA⟩ := generalLinear_det_surjective n K u
  refine ⟨Matrix.ProjGenLinGroup.mk A, ?_⟩
  rw [projectiveDetClass_mk, hA]
  rfl

/-- Image of `SL_d(K)` in `PGL_d(K)`. -/
noncomputable def projectiveSpecialLinear :
    Subgroup PGL(n, K) :=
  (Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL).range

/-- The kernel of determinant class is exactly `PSL_d(K)`. -/
theorem ker_projectiveDetClass_eq_projectiveSpecialLinear :
    (projectiveDetClass n K).ker = projectiveSpecialLinear n K := by
  ext g
  constructor
  · intro hg
    refine Matrix.ProjGenLinGroup.induction_on g ?_ hg
    intro A hA
    change
      ((Matrix.GeneralLinearGroup.det A : Kˣ) : DetPowerClass n K) = 1 at hA
    have hmem : Matrix.GeneralLinearGroup.det A ∈
        (powMonoidHom (Fintype.card n) : Kˣ →* Kˣ).range :=
      (QuotientGroup.eq_one_iff _).1 hA
    obtain ⟨u, hu⟩ := hmem
    let B : Matrix.GeneralLinearGroup n K :=
      Matrix.GeneralLinearGroup.scalar n u⁻¹ * A
    have hdetB : Matrix.det (B : Matrix n n K) = 1 := by
      have huval := congrArg Units.val hu
      dsimp [B]
      rw [Matrix.det_mul, Matrix.det_diagonal]
      simp only [Finset.prod_const, Finset.card_univ]
      simp only [Units.val_inv_eq_inv_val]
      change (u : K) ^ Fintype.card n =
        Matrix.det (A : Matrix n n K) at huval
      change (u : K)⁻¹ ^ Fintype.card n *
        Matrix.det (A : Matrix n n K) = 1
      rw [← huval]
      simp
    let s : Matrix.SpecialLinearGroup n K := ⟨(B : Matrix n n K), hdetB⟩
    refine ⟨s, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) =
      Matrix.ProjGenLinGroup.mk A
    have hsB : Matrix.SpecialLinearGroup.toGL s = B := by
      apply Units.ext
      rfl
    rw [hsB]
    dsimp [B]
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  · rintro ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    change projectiveDetClass n K
      (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s)) = 1
    rw [projectiveDetClass_mk]
    apply (QuotientGroup.eq_one_iff _).2
    refine ⟨1, ?_⟩
    ext
    simp

/-- Consequently, the index of `PSL_d(K)` in `PGL_d(K)` is the cardinality
of the determinant power-class group. -/
theorem index_projectiveSpecialLinear :
    (projectiveSpecialLinear n K).index = Nat.card (DetPowerClass n K) := by
  rw [← ker_projectiveDetClass_eq_projectiveSpecialLinear n K,
    Subgroup.index_ker]
  rw [MonoidHom.range_eq_top.mpr (projectiveDetClass_surjective n K)]
  simp

end ProjectiveIndex

instance rankMatrixIndexNonempty (r : Rank) : Nonempty (Fin r.matrixRank) :=
  ⟨⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩⟩

/-- Determinant power class on the selected projective residue group. -/
noncomputable def residueProjectiveDetClass
    (P : BasePrime) (r : Rank) (level : Nat) :
    PGL P r level →* ResiduePowerClass P r level :=
  by
    simpa only [PGL, ResiduePowerClass, IndexSelection.PowerClass,
      IndexSelection.dthPowerUnits, ProjectiveIndex.DetPowerClass,
      Fintype.card_fin] using
      (ProjectiveIndex.projectiveDetClass
        (Fin r.matrixRank) (ResidueField P r level))

theorem ker_residueProjectiveDetClass_eq_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    (residueProjectiveDetClass P r level).ker = PSL P r level := by
  simpa [residueProjectiveDetClass, PSL, specialToProjective,
    ProjectiveIndex.projectiveSpecialLinear, ResiduePowerClass,
    IndexSelection.PowerClass, IndexSelection.dthPowerUnits,
    ProjectiveIndex.DetPowerClass,
    Fintype.card_fin] using
    (ProjectiveIndex.ker_projectiveDetClass_eq_projectiveSpecialLinear
      (Fin r.matrixRank) (ResidueField P r level))

theorem residueProjectiveDetClass_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (residueProjectiveDetClass P r level) := by
  simpa [residueProjectiveDetClass, ResiduePowerClass,
    IndexSelection.PowerClass, IndexSelection.dthPowerUnits,
    ProjectiveIndex.DetPowerClass,
    Fintype.card_fin] using
    (ProjectiveIndex.projectiveDetClass_surjective
      (Fin r.matrixRank) (ResidueField P r level))

/-- Exact projective index for every selected hierarchy level. -/
theorem PSL_index
    (P : BasePrime) (r : Rank) (level : Nat) :
    (PSL P r level).index =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank := by
  calc
    (PSL P r level).index =
        Nat.card (ResiduePowerClass P r level) := by
      simpa [PSL, specialToProjective,
        ProjectiveIndex.projectiveSpecialLinear, ResiduePowerClass,
        IndexSelection.PowerClass, IndexSelection.dthPowerUnits,
        ProjectiveIndex.DetPowerClass,
        Fintype.card_fin] using
        (ProjectiveIndex.index_projectiveSpecialLinear
          (Fin r.matrixRank) (ResidueField P r level))
    _ = (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank :=
      by
        simpa only [ResiduePowerClass, Fintype.card_fin] using
          (IndexSelection.natCard_powerClass
            (ResidueField P r level) (Fintype.card (Fin r.matrixRank)))

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
