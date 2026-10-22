import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Congruence.Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence

/-!
# The projective special-linear endpoint in ranks three and four

This file develops the group-theoretic input needed to prove that the finite
Cartwright--Steger image contains the full projective special-linear group.
The first step is a construction-level perfectness proof: elementary
transvections are explicit commutators once a third coordinate is available.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open Matrix
open scoped commutatorElement
open scoped Pointwise

/-- A transvection bundled in the special linear group. -/
noncomputable def specialTransvection
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup n K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

@[simp] theorem specialTransvection_coe
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (hij : i ≠ j) (c : K) :
    (specialTransvection i j hij c : Matrix n n K) =
      Matrix.transvection i j c := rfl

/-- The Steinberg commutator relation, in the exact bundled form needed for
the commutator subgroup of `SL`. -/
theorem specialTransvection_commutator
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j k : n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (c : K) :
    ⁅specialTransvection i k hik c,
        specialTransvection k j hkj 1⁆ =
      specialTransvection i j hij c := by
  let A := specialTransvection i k hik c
  let B := specialTransvection k j hkj (1 : K)
  have hAinv : A⁻¹ = specialTransvection i k hik (-c) := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    rw [show (specialTransvection i k hik (-c) * A :
        Matrix.SpecialLinearGroup n K) =
      specialTransvection i k hik ((-c) + c) by
        apply Subtype.ext
        exact Matrix.transvection_mul_transvection_same
          (i := i) (j := k) hik (-c) c]
    simp [specialTransvection]
  have hBinv : B⁻¹ = specialTransvection k j hkj (-1 : K) := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    rw [show (specialTransvection k j hkj (-1 : K) * B :
        Matrix.SpecialLinearGroup n K) =
      specialTransvection k j hkj ((-1 : K) + 1) by
        apply Subtype.ext
        exact Matrix.transvection_mul_transvection_same
          (i := k) (j := j) hkj (-1) 1]
    simp [specialTransvection]
  change A * B * A⁻¹ * B⁻¹ = specialTransvection i j hij c
  rw [hAinv, hBinv]
  apply Subtype.ext
  let X : Matrix n n K := Matrix.single i k c
  let Y : Matrix n n K := Matrix.single k j 1
  have hXX : X * X = 0 := by
    dsimp [X]
    exact Matrix.single_mul_single_of_ne
      (c := c) i k i hik.symm c
  have hYY : Y * Y = 0 := by
    dsimp [Y]
    exact Matrix.single_mul_single_of_ne
      (c := (1 : K)) k j k hkj.symm 1
  have hYX : Y * X = 0 := by
    dsimp [X, Y]
    exact Matrix.single_mul_single_of_ne
      (c := (1 : K)) k j i hij.symm c
  have hXY : X * Y = Matrix.single i j c := by
    dsimp [X, Y]
    simpa using Matrix.single_mul_single_same
      (c := c) i k j (1 : K)
  have hnegX : Matrix.single i k (-c) = -X := by
    ext a b
    by_cases h : i = a ∧ k = b <;> simp [X, Matrix.single, h]
  have hnegY : Matrix.single k j (-1 : K) = -Y := by
    ext a b
    by_cases h : k = a ∧ j = b <;> simp [Y, Matrix.single, h]
  change (1 + Matrix.single i k c) * (1 + Matrix.single k j (1 : K)) *
    (1 + Matrix.single i k (-c)) * (1 + Matrix.single k j (-1 : K)) =
      1 + Matrix.single i j c
  rw [hnegX, hnegY]
  rw [show Matrix.single i k c = X by rfl,
    show Matrix.single k j (1 : K) = Y by rfl]
  rw [← hXY]
  noncomm_ring [hXX, hYY, hYX]

/-- Every elementary transvection in matrix rank at least three belongs to
the commutator subgroup of the special linear group. -/
theorem specialTransvection_mem_commutator
    {K : Type*} [Field K] (r : Rank)
    (i j : Fin r.matrixRank) (hij : i ≠ j) (c : K) :
    specialTransvection i j hij c ∈
      commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by
    cases r <;> decide)
  have hik : i ≠ k := Ne.symm hki
  rw [← specialTransvection_commutator i j k hij hik hkj c]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- In matrix ranks three and four the special linear group is perfect.  The
proof uses Gaussian transvection induction, the explicit diagonal
factorizations from congruence lifting, and the Steinberg commutator relation
above. -/
theorem specialLinearGroup_commutator_eq_top
    {K : Type*} [Field K] (r : Rank) :
    commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K) = ⊤ := by
  apply top_unique
  intro g hg
  let Q : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K → Prop :=
    fun M ↦ ∃ hdet : Matrix.det M = 1,
      (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin r.matrixRank) K) ∈
        commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K)
  have htrans : ∀ t : Matrix.TransvectionStruct
      (Fin r.matrixRank) K, Q t.toMatrix := by
    intro t
    refine ⟨Matrix.det_transvection_of_ne t.i t.j t.hij t.c, ?_⟩
    change specialTransvection t.i t.j t.hij t.c ∈
      commutator (Matrix.SpecialLinearGroup (Fin r.matrixRank) K)
    exact specialTransvection_mem_commutator r t.i t.j t.hij t.c
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨hA, hAmem⟩ ⟨hB, hBmem⟩
    have hdet : Matrix.det (A * B) = 1 := by
      rw [Matrix.det_mul, hA, hB, one_mul]
    refine ⟨hdet, ?_⟩
    have hprod :=
      (commutator (Matrix.SpecialLinearGroup
        (Fin r.matrixRank) K)).mul_mem hAmem hBmem
    exact hprod
  have hQ : Q (g : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      have hdet : Matrix.det (Matrix.diagonal D) = 1 := hD.trans g.prop
      cases r with
      | three =>
          exact CongruenceLifting.property_fin3_diagonal
            Q htrans hmul D hdet
      | four =>
          exact CongruenceLifting.property_fin4_diagonal
            Q htrans hmul D hdet
    · exact htrans
    · exact hmul
  obtain ⟨hdet, hmem⟩ := hQ
  have heq :
      (⟨(g : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K), hdet⟩ :
        Matrix.SpecialLinearGroup (Fin r.matrixRank) K) = g := by
    rfl
  rw [← heq]
  exact hmem

/-- Projectivization with codomain restricted to the construction-owned
`PSL` subgroup. -/
noncomputable def specialLinearToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) →*
      PSL P r level where
  toFun s := ⟨specialToProjective P r level s, ⟨s, rfl⟩⟩
  map_one' := Subtype.ext (map_one (specialToProjective P r level))
  map_mul' s t :=
    Subtype.ext (map_mul (specialToProjective P r level) s t)

theorem specialLinearToPSL_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (specialLinearToPSL P r level) := by
  intro g
  obtain ⟨s, hs⟩ := g.property
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hs

/-- The finite projective special-linear group selected by the construction
is perfect, proved as the surjective projective image of the explicit
rank-three/rank-four perfect `SL`. -/
theorem PSL_commutator_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    commutator (PSL P r level) = ⊤ := by
  letI : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level)) :=
    ⟨specialLinearGroup_commutator_eq_top r⟩
  letI : Group.IsPerfect (PSL P r level) :=
    Group.IsPerfect.ofSurjective
      (specialLinearToPSL_surjective P r level)
  exact Group.IsPerfect.commutator_eq_top

section ProjectiveRoots

open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An arbitrary linear transvection, bundled with its determinant-one
certificate.  Keeping the functional and centre vector visible is important:
the root subgroup at a projective point consists of exactly these elements
with centre on that point. -/
noncomputable def linearSpecialTransvection
    (f : Module.Dual K V) (v : V) (hfv : f v = 0) :
    SpecialLinearGroup K V :=
  ⟨LinearEquiv.transvection hfv, LinearEquiv.transvection.det_eq_one hfv⟩

@[simp] theorem linearSpecialTransvection_apply
    (f : Module.Dual K V) (v : V) (hfv : f v = 0) (w : V) :
    linearSpecialTransvection f v hfv w = w + f w • v :=
  rfl

/-- Generators of the projective root subgroup centred at `x`. -/
def projectiveRootGenerators (x : ℙ K V) : Set (SpecialLinearGroup K V) :=
  {g | ∃ (f : Module.Dual K V) (v : V) (hv : v ≠ 0) (hfv : f v = 0),
    Projectivization.mk K v hv = x ∧ g = linearSpecialTransvection f v hfv}

/-- The root subgroup at a projective point, constructed rather than
postulated as part of an Iwasawa structure. -/
def projectiveRootSubgroup (x : ℙ K V) : Subgroup (SpecialLinearGroup K V) :=
  Subgroup.closure (projectiveRootGenerators x)

theorem projectiveRootGenerators_commute (x : ℙ K V)
    (a : SpecialLinearGroup K V) (ha : a ∈ projectiveRootGenerators x)
    (b : SpecialLinearGroup K V) (hb : b ∈ projectiveRootGenerators x) :
    a * b = b * a := by
  obtain ⟨f, v, hv, hfv, hxv, rfl⟩ := ha
  obtain ⟨g, w, hw, hgw, hxw, rfl⟩ := hb
  obtain ⟨u, hu⟩ :=
    (Projectivization.mk_eq_mk_iff K v w hv hw).mp (hxv.trans hxw.symm)
  have hu' : (u : K) • w = v := by
    simpa [Units.smul_def] using hu
  apply SpecialLinearGroup.ext
  intro z
  have hfw : f w = 0 := by
    have hzero : (u : K) * f w = 0 := by
      have := congrArg f hu'
      simpa [map_smul, hfv, smul_eq_mul] using this
    exact (mul_eq_zero.mp hzero).resolve_left (Units.ne_zero u)
  have hgv : g v = 0 := by
    rw [← hu', map_smul, hgw, smul_zero]
  simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply,
    linearSpecialTransvection_apply, map_add, map_smul]
  simp [hfv, hgw, hfw, hgv, add_assoc, add_left_comm, add_comm]

theorem projectiveRootSubgroup_isMulCommutative (x : ℙ K V) :
    IsMulCommutative (projectiveRootSubgroup x) :=
  Subgroup.isMulCommutative_closure
    (projectiveRootGenerators_commute x)

theorem linearSpecialTransvection_conj
    (a : SpecialLinearGroup K V)
    (f : Module.Dual K V) (v : V) (hfv : f v = 0) :
    a * linearSpecialTransvection f v hfv * a⁻¹ =
      linearSpecialTransvection
        (f.comp (a⁻¹ : V ≃ₗ[K] V).toLinearMap) (a v) (by simp [hfv]) := by
  apply SpecialLinearGroup.ext
  intro z
  simp [linearSpecialTransvection_apply, map_add, map_smul]

theorem projectiveRootGenerators_conj
    (a : SpecialLinearGroup K V) (x : ℙ K V) :
    MulAut.conj a '' projectiveRootGenerators x =
      projectiveRootGenerators (a • x) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, v, hv, hfv, hx, rfl⟩ := hg
    let f' : Module.Dual K V :=
      f.comp (a⁻¹ : V ≃ₗ[K] V).toLinearMap
    have hf' : f' (a v) = 0 := by simp [f', hfv]
    refine ⟨f', a v, ?_, hf', ?_, ?_⟩
    · exact (a : V ≃ₗ[K] V).map_ne_zero_iff.mpr hv
    · calc
        Projectivization.mk K (a v) _ =
            a • Projectivization.mk K v hv := by
              rw [Projectivization.smul_mk]
              rfl
        _ = a • x := congrArg (a • ·) hx
    · exact linearSpecialTransvection_conj a f v hfv
  · rintro g ⟨f, v, hv, hfv, hx, rfl⟩
    let w : V := a⁻¹ v
    let f' : Module.Dual K V := f.comp (a : V ≃ₗ[K] V).toLinearMap
    have hw : w ≠ 0 := by
      exact (a⁻¹ : V ≃ₗ[K] V).map_ne_zero_iff.mpr hv
    have hf' : f' w = 0 := by simp [f', w, hfv]
    let t := linearSpecialTransvection f' w hf'
    refine ⟨t, ?_, ?_⟩
    · refine ⟨f', w, hw, hf', ?_, rfl⟩
      calc
        Projectivization.mk K w hw =
            a⁻¹ • Projectivization.mk K v hv := by
              rw [Projectivization.smul_mk]
              rfl
        _ = a⁻¹ • (a • x) := congrArg (a⁻¹ • ·) hx
        _ = x := inv_smul_smul a x
    · rw [MulAut.conj_apply, linearSpecialTransvection_conj]
      apply SpecialLinearGroup.ext
      intro z
      simp [f', w, linearSpecialTransvection_apply]

theorem projectiveRootSubgroup_conj
    (a : SpecialLinearGroup K V) (x : ℙ K V) :
    projectiveRootSubgroup (a • x) =
      MulAut.conj a • projectiveRootSubgroup x := by
  rw [Subgroup.pointwise_smul_def, projectiveRootSubgroup, projectiveRootSubgroup]
  change Subgroup.closure (projectiveRootGenerators (a • x)) =
    Subgroup.map (MulAut.conj a).toMonoidHom (Subgroup.closure (projectiveRootGenerators x))
  rw [MonoidHom.map_closure]
  change Subgroup.closure (projectiveRootGenerators (a • x)) =
    Subgroup.closure (MulAut.conj a '' projectiveRootGenerators x)
  rw [projectiveRootGenerators_conj]

section CoordinateRoots

variable {n : Type*} [Fintype n] [DecidableEq n]

private def coordinateFunctional (j : n) (c : K) : Module.Dual K (n → K) :=
  c • LinearMap.proj j

private def coordinateVector (i : n) : n → K :=
  Pi.single i 1

private theorem coordinateVector_ne_zero (i : n) :
    coordinateVector (K := K) i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [coordinateVector] at this

private theorem coordinateFunctional_vector_eq_zero
    (i j : n) (hij : i ≠ j) (c : K) :
    coordinateFunctional j c (coordinateVector i) = 0 := by
  simp [coordinateFunctional, coordinateVector, LinearMap.proj_apply,
    Pi.single_apply, hij.symm]

theorem toLinEquiv_specialTransvection
    (i j : n) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.toLin'_equiv
        (specialTransvection i j hij c) =
      linearSpecialTransvection
        (coordinateFunctional j c) (coordinateVector i)
        (coordinateFunctional_vector_eq_zero i j hij c) := by
  apply SpecialLinearGroup.ext
  intro z
  funext k
  change (Matrix.toLin' (Matrix.transvection i j c) z) k = _
  simp [Matrix.toLin'_apply',
    Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, Function.update_apply,
    linearSpecialTransvection_apply,
    coordinateFunctional, coordinateVector, LinearMap.proj_apply,
    Pi.single_apply]

theorem toLinEquiv_specialTransvection_mem_projectiveRoots
    (i j : n) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.toLin'_equiv
        (specialTransvection i j hij c) ∈
      iSup (projectiveRootSubgroup :
        ℙ K (n → K) → Subgroup (SpecialLinearGroup K (n → K))) := by
  let v := coordinateVector (K := K) i
  have hv : v ≠ 0 := coordinateVector_ne_zero i
  let x := Projectivization.mk K v hv
  apply (le_iSup projectiveRootSubgroup x)
  apply Subgroup.subset_closure
  refine ⟨coordinateFunctional j c, v, hv,
    coordinateFunctional_vector_eq_zero i j hij c, rfl, ?_⟩
  exact toLinEquiv_specialTransvection i j hij c

theorem projectiveRootSubgroups_generate_specialLinear
    (r : Rank) {K : Type*} [Field K] :
    iSup (projectiveRootSubgroup :
      ℙ K (Fin r.matrixRank → K) →
        Subgroup (SpecialLinearGroup K (Fin r.matrixRank → K))) = ⊤ := by
  apply top_unique
  intro g hg
  let S : Subgroup (SpecialLinearGroup K (Fin r.matrixRank → K)) :=
    iSup (projectiveRootSubgroup :
      ℙ K (Fin r.matrixRank → K) →
        Subgroup (SpecialLinearGroup K (Fin r.matrixRank → K)))
  let gm : Matrix.SpecialLinearGroup (Fin r.matrixRank) K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm g
  let Q : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K → Prop :=
    fun M ↦ ∃ hdet : Matrix.det M = 1,
      Matrix.SpecialLinearGroup.toLin'_equiv
        (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin r.matrixRank) K) ∈ S
  have htrans : ∀ t : Matrix.TransvectionStruct
      (Fin r.matrixRank) K, Q t.toMatrix := by
    intro t
    have hdet := Matrix.det_transvection_of_ne t.i t.j t.hij t.c
    refine ⟨hdet, ?_⟩
    have heq :
        (⟨t.toMatrix, hdet⟩ :
          Matrix.SpecialLinearGroup (Fin r.matrixRank) K) =
          specialTransvection t.i t.j t.hij t.c := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact toLinEquiv_specialTransvection_mem_projectiveRoots
      t.i t.j t.hij t.c
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨hdetA, hAmem⟩ ⟨hdetB, hBmem⟩
    have hdet : Matrix.det (A * B) = 1 := by
      rw [Matrix.det_mul, hdetA, hdetB, one_mul]
    refine ⟨hdet, ?_⟩
    let aSL : Matrix.SpecialLinearGroup (Fin r.matrixRank) K := ⟨A, hdetA⟩
    let bSL : Matrix.SpecialLinearGroup (Fin r.matrixRank) K := ⟨B, hdetB⟩
    have hab :
        (⟨A * B, hdet⟩ : Matrix.SpecialLinearGroup
          (Fin r.matrixRank) K) = aSL * bSL := by
      apply Subtype.ext
      rfl
    rw [hab, map_mul]
    exact S.mul_mem hAmem hBmem
  have hQ : Q (gm : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      have hdet : Matrix.det (Matrix.diagonal D) = 1 := hD.trans gm.prop
      cases r with
      | three =>
          exact CongruenceLifting.property_fin3_diagonal
            Q htrans hmul D hdet
      | four =>
          exact CongruenceLifting.property_fin4_diagonal
            Q htrans hmul D hdet
    · exact htrans
    · exact hmul
  obtain ⟨hdet, hgm⟩ := hQ
  change g ∈ S
  change Matrix.SpecialLinearGroup.toLin'_equiv gm ∈ S at hgm
  rw [show Matrix.SpecialLinearGroup.toLin'_equiv gm = g from
    Matrix.SpecialLinearGroup.toLin'_equiv.apply_symm_apply g] at hgm
  exact hgm

end CoordinateRoots

/-- The explicit root subgroups satisfy all three structural clauses of the
Iwasawa criterion. -/
noncomputable def specialLinearIwasawaStructure
    (r : Rank) {K : Type*} [Field K] :
    MulAction.IwasawaStructure
      (SpecialLinearGroup K (Fin r.matrixRank → K))
      (ℙ K (Fin r.matrixRank → K)) where
  T := projectiveRootSubgroup
  is_comm := projectiveRootSubgroup_isMulCommutative
  is_conj := projectiveRootSubgroup_conj
  is_generator := projectiveRootSubgroups_generate_specialLinear r

/-- A special-linear map fixing every projective point is a homothety.  This
is the kernel calculation needed below; it is proved from collinearity of
every vector with its image, not assumed as faithfulness of projective
action. -/
theorem specialLinear_fixed_projective_is_homothety
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Free K V]
    (a : SpecialLinearGroup K V)
    (hfix : ∀ x : ℙ K V, a • x = x) :
    ∃ c : K, (a : V ≃ₗ[K] V).toLinearMap = c • 1 := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v
  by_cases hv : v = 0
  · subst v
    intro hli
    exact (hli.ne_zero 0) rfl
  have hav : a v ≠ 0 :=
    (a : V ≃ₗ[K] V).map_ne_zero_iff.mpr hv
  intro hli
  have hind : Projectivization.Independent
      ![Projectivization.mk K v hv, Projectivization.mk K (a v) hav] :=
    (Projectivization.independent_mk_iff_LinearIndependent hv hav).2 hli
  have hne := (Projectivization.independent_pair_iff_ne _ _).1 hind
  apply hne
  have hs := hfix (Projectivization.mk K v hv)
  rw [Projectivization.specialLinearGroup_smul_def,
    Projectivization.smul_mk] at hs
  exact hs.symm

theorem specialToProjective_eq_one_of_fixed_projective
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (hfix : ∀ x : ℙ (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level), s • x = x) :
    specialToProjective P r level s = 1 := by
  let a : SpecialLinearGroup (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level) :=
    Matrix.SpecialLinearGroup.toLin'_equiv s
  have hfixa : ∀ x : ℙ (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level), a • x = x := by
    intro x
    exact hfix x
  obtain ⟨c, hc⟩ := specialLinear_fixed_projective_is_homothety a hfixa
  rw [specialToProjective]
  change Matrix.ProjGenLinGroup.mk
    (Matrix.SpecialLinearGroup.toGL s) = 1
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  calc
    Matrix.toLin' (Matrix.scalar (Fin r.matrixRank) c) = c • 1 := by
      ext v i
      by_cases h : v = i <;>
        simp [Matrix.scalar, Matrix.toLin'_apply', Pi.single_apply, h]
    _ = a.val.toLinearMap := hc.symm
    _ = Matrix.toLin' (Matrix.SpecialLinearGroup.toGL s :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
      exact Matrix.SpecialLinearGroup.toLin'_to_linearMap s

/-- The projective quotient map, expressed on the module version of the
special linear group used by the Iwasawa action. -/
noncomputable def abstractSpecialLinearToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    SpecialLinearGroup (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level) →*
      PSL P r level :=
  (specialLinearToPSL P r level).comp
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom

theorem abstractSpecialLinearToPSL_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (abstractSpecialLinearToPSL P r level) := by
  intro g
  obtain ⟨s, rfl⟩ := specialLinearToPSL_surjective P r level g
  exact ⟨Matrix.SpecialLinearGroup.toLin'_equiv s, by
    simp [abstractSpecialLinearToPSL]⟩

/-- The finite `PSL` endpoint is simple in the construction's ranks.  The
proof is an explicit Iwasawa argument: root subgroups are constructed above,
perfectness comes from elementary commutators, and the projective-action
kernel is proved to consist of scalar matrices. -/
theorem PSL_isSimpleGroup
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsSimpleGroup (PSL P r level) := by
  letI : Nontrivial (PSL P r level) :=
    (CongruenceLifting.residueTransvectionPSL_injective
      P r level).nontrivial
  refine ⟨?_⟩
  intro H hH
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  let φ := abstractSpecialLinearToPSL P r level
  let N := H.comap φ
  letI : H.Normal := hH
  letI : N.Normal := inferInstance
  have hfixed : MulAction.fixedPoints N
      (ℙ (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level)) ≠ Set.univ := by
    intro hall
    apply hbot
    apply bot_unique
    intro g hg
    obtain ⟨a, rfl⟩ := abstractSpecialLinearToPSL_surjective P r level g
    have haN : a ∈ N := hg
    have hafix : ∀ x : ℙ (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level), a • x = x := by
      intro x
      exact (MulAction.mem_fixedPoints.mp
        (Set.eq_univ_iff_forall.mp hall x)) ⟨a, haN⟩
    let s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) :=
      Matrix.SpecialLinearGroup.toLin'_equiv.symm a
    have hsfix : ∀ x : ℙ (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level), s • x = x := by
      intro x
      rw [Projectivization.matrixSpecialLinearGroup_smul_def]
      simpa [s] using hafix x
    have hsone := specialToProjective_eq_one_of_fixed_projective
      P r level s hsfix
    apply Subtype.ext
    simpa [φ, abstractSpecialLinearToPSL, specialLinearToPSL, s] using hsone
  have hcomm : commutator
      (SpecialLinearGroup (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level)) = ⊤ := by
    letI : Group.IsPerfect
        (Matrix.SpecialLinearGroup (Fin r.matrixRank)
          (ResidueField P r level)) :=
      ⟨specialLinearGroup_commutator_eq_top r⟩
    let e : Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) ≃*
        SpecialLinearGroup (ResidueField P r level)
          (Fin r.matrixRank → ResidueField P r level) :=
      Matrix.SpecialLinearGroup.toLin'_equiv
    letI : Group.IsPerfect
        (SpecialLinearGroup (ResidueField P r level)
          (Fin r.matrixRank → ResidueField P r level)) :=
      Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hcomm_le := (specialLinearIwasawaStructure r).commutator_le N hfixed
  rw [hcomm] at hcomm_le
  have hNtop : N = ⊤ := top_unique hcomm_le
  apply top_unique
  intro g hg
  obtain ⟨a, rfl⟩ := abstractSpecialLinearToPSL_surjective P r level g
  have ha : a ∈ N := by
    rw [hNtop]
    exact Subgroup.mem_top a
  exact ha

end ProjectiveRoots

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
