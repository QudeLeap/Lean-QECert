import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Building.BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The compact cyclic stabilizer in the Cartwright--Steger building model

This module begins the global-arithmetic half of LSV05b Proposition 4.8.
It constructs the actual constant/cyclic subgroup at the building place and
records its semidirect-product relations.  These are the local images of the
normal forms in LSV05b Proposition 3.5; no stabilizer classification is
assumed as input.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

/-- Frobenius acting on the units of the constant extension. -/
noncomputable def constantFrobeniusUnitEquiv
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ ≃* (ConstantExtension P r)ˣ :=
  Units.mapEquiv (constantFrobenius P r).toMulEquiv

@[simp]
theorem constantFrobeniusUnitEquiv_coe
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    (constantFrobeniusUnitEquiv P r u : ConstantExtension P r) =
      constantFrobenius P r u :=
  rfl

/-- The constant-field representation as a genuine group homomorphism at
the building place. -/
noncomputable def buildingConstantGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  (Matrix.GeneralLinearGroup.map
      (algebraMap (BaseField P) (BuildingLocalField P))).comp
    (Units.map (constantRegularMatrix P r).toMonoidHom)

@[simp]
theorem buildingConstantGLHom_apply
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantGLHom P r u = buildingConstantGL P r u :=
  rfl

/-- Projectivized constant-field representation at the building place. -/
noncomputable def buildingConstantPGLHom
    (P : BasePrime) (r : Rank) :
    (ConstantExtension P r)ˣ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk.comp (buildingConstantGLHom P r)

/-- The projective local cyclic element. -/
noncomputable def buildingCyclicGeneratorPGL
    (P : BasePrime) (r : Rank) :
    Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  Matrix.ProjGenLinGroup.mk (buildingCyclicGeneratorGL P r)

/-- Conjugation by the local cyclic element realizes arithmetic Frobenius
on represented constant units. -/
theorem buildingCyclicGeneratorGL_conj_constant
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorGL P r * buildingConstantGL P r u *
        (buildingCyclicGeneratorGL P r)⁻¹ =
      buildingConstantGL P r (constantFrobeniusUnitEquiv P r u) := by
  apply mul_right_cancel (b := buildingCyclicGeneratorGL P r)
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply Units.ext
  simp only [Units.val_mul]
  rw [buildingCyclicGeneratorGL_coe, buildingConstantGL_coe,
    buildingConstantGL_coe, constantFrobeniusUnitEquiv_coe]
  exact buildingCyclicGeneratorMatrix_mul_buildingConstantMatrix P r u

/-- Projective form of the Frobenius conjugation relation. -/
theorem buildingCyclicGeneratorPGL_conj_constant
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorPGL P r * buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r)⁻¹ =
      buildingConstantPGLHom P r (constantFrobeniusUnitEquiv P r u) := by
  exact congrArg (Matrix.ProjGenLinGroup.mk :
      Matrix.GeneralLinearGroup (Fin r.matrixRank) (BuildingLocalField P) →*
        Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (buildingCyclicGeneratorGL_conj_constant P r u)

/-- Conjugation by an arbitrary integral power of the cyclic element is the
corresponding power of Frobenius on the represented constants. -/
theorem buildingCyclicGeneratorPGL_zpow_conj_constant
    (P : BasePrime) (r : Rank) (n : ℤ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorPGL P r ^ n *
        buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ n)⁻¹ =
      buildingConstantPGLHom P r
        ((constantFrobeniusUnitEquiv P r ^ n) u) := by
  induction n using Int.induction_on generalizing u with
  | zero => simp
  | succ n ih =>
      calc
        buildingCyclicGeneratorPGL P r ^ ((n : ℤ) + 1) *
              buildingConstantPGLHom P r u *
              (buildingCyclicGeneratorPGL P r ^ ((n : ℤ) + 1))⁻¹ =
            buildingCyclicGeneratorPGL P r ^ (n : ℤ) *
              (buildingCyclicGeneratorPGL P r *
                buildingConstantPGLHom P r u *
                (buildingCyclicGeneratorPGL P r)⁻¹) *
              (buildingCyclicGeneratorPGL P r ^ (n : ℤ))⁻¹ := by
                rw [zpow_add_one]
                group
        _ = buildingCyclicGeneratorPGL P r ^ (n : ℤ) *
              buildingConstantPGLHom P r
                (constantFrobeniusUnitEquiv P r u) *
              (buildingCyclicGeneratorPGL P r ^ (n : ℤ))⁻¹ := by
                rw [buildingCyclicGeneratorPGL_conj_constant]
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ (n : ℤ))
                (constantFrobeniusUnitEquiv P r u)) :=
              ih (constantFrobeniusUnitEquiv P r u)
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ ((n : ℤ) + 1)) u) := by
                rw [zpow_add_one, MulAut.mul_apply]
  | pred n ih =>
      have hinverse (v : (ConstantExtension P r)ˣ) :
          (buildingCyclicGeneratorPGL P r)⁻¹ *
              buildingConstantPGLHom P r v *
              buildingCyclicGeneratorPGL P r =
            buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by
        have hforward := buildingCyclicGeneratorPGL_conj_constant P r
          ((constantFrobeniusUnitEquiv P r)⁻¹ v)
        have hforward' :
            buildingCyclicGeneratorPGL P r *
                buildingConstantPGLHom P r
                  ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                (buildingCyclicGeneratorPGL P r)⁻¹ =
              buildingConstantPGLHom P r v := by
          simpa using hforward
        calc
          (buildingCyclicGeneratorPGL P r)⁻¹ *
                buildingConstantPGLHom P r v *
                buildingCyclicGeneratorPGL P r =
              (buildingCyclicGeneratorPGL P r)⁻¹ *
                (buildingCyclicGeneratorPGL P r *
                  buildingConstantPGLHom P r
                    ((constantFrobeniusUnitEquiv P r)⁻¹ v) *
                  (buildingCyclicGeneratorPGL P r)⁻¹) *
                buildingCyclicGeneratorPGL P r := by rw [hforward']
          _ = buildingConstantPGLHom P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ v) := by group
      change buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1) *
            buildingConstantPGLHom P r u *
            (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1))⁻¹ =
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u)
      calc
        buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1) *
              buildingConstantPGLHom P r u *
              (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ) - 1))⁻¹ =
            buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)) *
              ((buildingCyclicGeneratorPGL P r)⁻¹ *
                buildingConstantPGLHom P r u *
                buildingCyclicGeneratorPGL P r) *
              (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [zpow_sub_one]
                group
        _ = buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)) *
              buildingConstantPGLHom P r
                ((constantFrobeniusUnitEquiv P r)⁻¹ u) *
              (buildingCyclicGeneratorPGL P r ^ (-(n : ℤ)))⁻¹ := by
                rw [hinverse]
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ)))
                ((constantFrobeniusUnitEquiv P r)⁻¹ u)) :=
              ih ((constantFrobeniusUnitEquiv P r)⁻¹ u)
        _ = buildingConstantPGLHom P r
              ((constantFrobeniusUnitEquiv P r ^ (-(n : ℤ) - 1)) u) := by
                rw [zpow_sub_one, MulAut.mul_apply]

/-- Natural-power specialization of cyclic conjugation, used for the
canonical exponents `0 ≤ j < d`. -/
theorem buildingCyclicGeneratorPGL_pow_conj_constant
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    buildingCyclicGeneratorPGL P r ^ j *
        buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r
        ((constantFrobeniusUnitEquiv P r ^ j) u) := by
  simpa using
    (buildingCyclicGeneratorPGL_zpow_conj_constant P r (j : ℤ) u)

/-- The integer cyclic group acts on constant units by powers of
Frobenius. -/
noncomputable def constantFrobeniusZAction
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →* MulAut ((ConstantExtension P r)ˣ) :=
  zpowersHom _ (constantFrobeniusUnitEquiv P r)

/-- Integer powers of the projective cyclic element. -/
noncomputable def buildingCyclicZHom
    (P : BasePrime) (r : Rank) :
    Multiplicative ℤ →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  zpowersHom _ (buildingCyclicGeneratorPGL P r)

theorem buildingConstant_cyclic_compatibility
    (P : BasePrime) (r : Rank) (n : Multiplicative ℤ) :
    (buildingConstantPGLHom P r).comp
        ((constantFrobeniusZAction P r n).toMonoidHom) =
      (MulAut.conj (buildingCyclicZHom P r n)).toMonoidHom.comp
        (buildingConstantPGLHom P r) := by
  ext u
  change buildingConstantPGLHom P r
      ((constantFrobeniusUnitEquiv P r ^ n.toAdd) u) =
    buildingCyclicGeneratorPGL P r ^ n.toAdd *
      buildingConstantPGLHom P r u *
      (buildingCyclicGeneratorPGL P r ^ n.toAdd)⁻¹
  exact (buildingCyclicGeneratorPGL_zpow_conj_constant
    P r n.toAdd u).symm

/-- The source semidirect product for the compact cyclic stabilizer. -/
abbrev BuildingCompactCyclicSemidirect
    (P : BasePrime) (r : Rank) :=
  (ConstantExtension P r)ˣ ⋊[constantFrobeniusZAction P r] Multiplicative ℤ

/-- The source normal form `u z^n` mapped to the actual projective building
representation. -/
noncomputable def buildingCompactCyclicSemidirectHom
    (P : BasePrime) (r : Rank) :
    BuildingCompactCyclicSemidirect P r →*
      Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P) :=
  SemidirectProduct.lift
    (buildingConstantPGLHom P r)
    (buildingCyclicZHom P r)
    (buildingConstant_cyclic_compatibility P r)

@[simp]
theorem buildingCompactCyclicSemidirectHom_apply
    (P : BasePrime) (r : Rank)
    (x : BuildingCompactCyclicSemidirect P r) :
    buildingCompactCyclicSemidirectHom P r x =
      buildingConstantPGLHom P r x.left *
        buildingCyclicGeneratorPGL P r ^ x.right.toAdd :=
  rfl

/-- The local cyclic element has projective order dividing the matrix rank,
because its rank-th power is the central scalar `1 + y`. -/
theorem buildingCyclicGeneratorPGL_pow_matrixRank
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorPGL P r ^ r.matrixRank = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (buildingCyclicGeneratorGL P r ^ r.matrixRank) = 1
  let a : (BuildingLocalField P)ˣ :=
    Units.mk0 (1 + buildingLocalY P) (one_add_buildingLocalY_ne_zero P)
  have hgl : buildingCyclicGeneratorGL P r ^ r.matrixRank =
      Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
        a := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val]
    rw [buildingCyclicGeneratorGL_coe]
    rw [buildingCyclicGeneratorMatrix_pow_matrixRank]
    change (1 + buildingLocalY P) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (BuildingLocalField P)) =
      Matrix.scalar (Fin r.matrixRank) (1 + buildingLocalY P)
    rw [Matrix.scalar_apply]
    exact Matrix.smul_one_eq_diagonal _
  rw [hgl]
  exact Matrix.ProjGenLinGroup.mk_scalar _

/-- Conjugation by a compact normal form `u z^n` only remembers the
cyclic exponent on the represented constant field.  The leading constant
factor disappears because the constant extension is commutative. -/
theorem buildingConstant_mul_cyclic_zpow_conj_constant
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ) (n : ℤ) :
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ n) *
        buildingConstantPGLHom P r v *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ n)⁻¹ =
      buildingConstantPGLHom P r
        ((constantFrobeniusUnitEquiv P r ^ n) v) := by
  calc
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ n) *
        buildingConstantPGLHom P r v *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ n)⁻¹ =
      buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ n *
          buildingConstantPGLHom P r v *
          (buildingCyclicGeneratorPGL P r ^ n)⁻¹) *
        (buildingConstantPGLHom P r u)⁻¹ := by group
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ n) v) *
        (buildingConstantPGLHom P r u)⁻¹ := by
          rw [buildingCyclicGeneratorPGL_zpow_conj_constant]
    _ = buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ n) v) := by
          rw [← map_inv, ← map_mul, ← map_mul]
          simp [mul_comm]

/-- A Frobenius power in the canonical exponent range can be the identity
only at exponent zero. -/
theorem eq_zero_of_constantFrobenius_pow_eq_one
    (P : BasePrime) (r : Rank) (j : ℕ) (hj : j < r.matrixRank)
    (hpow : constantFrobenius P r ^ j = 1) :
    j = 0 := by
  have hdvd : r.matrixRank ∣ j := by
    simpa [constantFrobenius_order P r] using
      (orderOf_dvd_of_pow_eq_one hpow)
  exact Nat.eq_zero_of_dvd_of_lt hdvd hj

/-- A unit fixed by arithmetic Frobenius is not merely a fixed field
element: it is the image of an actual base-field unit. -/
theorem exists_baseUnit_of_constantFrobeniusUnitEquiv_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (hu : constantFrobeniusUnitEquiv P r u = u) :
    ∃ a : (BaseField P)ˣ,
      Units.map (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a = u := by
  have huCoe : constantFrobenius P r (u : ConstantExtension P r) = u := by
    simpa only [constantFrobeniusUnitEquiv_coe] using congrArg Units.val hu
  obtain ⟨a, ha⟩ :=
    exists_eq_algebraMap_of_constantFrobenius_eq P r (u : ConstantExtension P r) huCoe
  have ha0 : a ≠ 0 := by
    intro haZero
    apply u.ne_zero
    rw [← ha]
    simp [haZero]
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  exact ha

/-- Base-field units act as scalar matrices and hence disappear after
projectivization. -/
theorem buildingConstantPGLHom_map_baseUnit_eq_one
    (P : BasePrime) (r : Rank) (a : (BaseField P)ˣ) :
    buildingConstantPGLHom P r
        (Units.map
          (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a) = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (buildingConstantGL P r
        (Units.map
          (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a)) = 1
  let aLocal : (BuildingLocalField P)ˣ :=
    Units.map (algebraMap (BaseField P) (BuildingLocalField P)).toMonoidHom a
  have hgl :
      buildingConstantGL P r
          (Units.map
            (algebraMap (BaseField P) (ConstantExtension P r)).toMonoidHom a) =
        Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank) aLocal := by
    apply Units.ext
    change
      (constantRegularMatrix P r
          (algebraMap (BaseField P) (ConstantExtension P r) (a : BaseField P))).map
          (algebraMap (BaseField P) (BuildingLocalField P)) =
        Matrix.scalar (Fin r.matrixRank)
          (algebraMap (BaseField P) (BuildingLocalField P) (a : BaseField P))
    rw [(constantRegularMatrix P r).commutes]
    rw [Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_map (map_zero
        (algebraMap (BaseField P) (BuildingLocalField P)))]
    rfl
  rw [hgl]
  exact Matrix.ProjGenLinGroup.mk_scalar _

/-- Consequently every Frobenius-fixed represented constant unit is the
projective identity. -/
theorem buildingConstantPGLHom_eq_one_of_constantFrobeniusUnitEquiv_eq
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (hu : constantFrobeniusUnitEquiv P r u = u) :
    buildingConstantPGLHom P r u = 1 := by
  obtain ⟨a, rfl⟩ :=
    exists_baseUnit_of_constantFrobeniusUnitEquiv_eq P r u hu
  exact buildingConstantPGLHom_map_baseUnit_eq_one P r a

/-- The unit coefficient of the conjugate of the cyclic monomial `v z^k`
by the compact normal form `u z^j`. -/
noncomputable def compactConjugationDiagonalUnit
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (ConstantExtension P r)ˣ :=
  u * ((constantFrobeniusUnitEquiv P r ^ j) v) *
    ((constantFrobeniusUnitEquiv P r ^ k) u)⁻¹

/-- The computed block formula agrees with actual projective inner
conjugation on every nonzero cyclic monomial. -/
theorem buildingCompactNormalForm_conj_constantCyclicMonomial
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j) *
        (buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r
          (compactConjugationDiagonalUnit P r u v j k) *
        buildingCyclicGeneratorPGL P r ^ k := by
  have hv := buildingCyclicGeneratorPGL_pow_conj_constant P r j v
  have huInv := buildingCyclicGeneratorPGL_pow_conj_constant P r k u⁻¹
  calc
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j) *
        (buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ j *
          buildingConstantPGLHom P r v *
          (buildingCyclicGeneratorPGL P r ^ j)⁻¹) *
        buildingCyclicGeneratorPGL P r ^ k *
        (buildingConstantPGLHom P r u)⁻¹ := by group
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ j) v) *
        buildingCyclicGeneratorPGL P r ^ k *
        (buildingConstantPGLHom P r u)⁻¹ := by rw [hv]
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ j) v) *
        (buildingCyclicGeneratorPGL P r ^ k *
          (buildingConstantPGLHom P r u)⁻¹ *
          (buildingCyclicGeneratorPGL P r ^ k)⁻¹) *
        buildingCyclicGeneratorPGL P r ^ k := by group
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ j) v) *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ k) u⁻¹) *
        buildingCyclicGeneratorPGL P r ^ k := by
          rw [← map_inv, huInv]
    _ = buildingConstantPGLHom P r
          (compactConjugationDiagonalUnit P r u v j k) *
        buildingCyclicGeneratorPGL P r ^ k := by
          rw [compactConjugationDiagonalUnit, map_mul, map_mul, map_inv]

/-- Coercing a Frobenius power on units agrees with the corresponding
power of the constant-field automorphism. -/
theorem constantFrobeniusUnitEquiv_pow_coe
    (P : BasePrime) (r : Rank) (j : ℕ)
    (u : (ConstantExtension P r)ˣ) :
    (((constantFrobeniusUnitEquiv P r ^ j) u :
        (ConstantExtension P r)ˣ) : ConstantExtension P r) =
      (constantFrobenius P r ^ j) (u : ConstantExtension P r) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, MulAut.mul_apply, pow_succ, AlgEquiv.mul_apply]
      rw [ih, constantFrobeniusUnitEquiv_coe]

/-- The diagonal multiplier on the `k`-th constant-field block of inner
conjugation by the compact normal form `u z^j`. -/
noncomputable def compactConjugationDiagonalMultiplier
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (k : ℕ) :
    ConstantExtension P r :=
  (u : ConstantExtension P r) *
    ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹

/-- The exact `k`-th diagonal block of inner conjugation by `u z^j` on
the cyclic-algebra decomposition `⊕ₖ F_(q^d) z^k`.

This is the algebraic block inspected modulo `1/y` in LSV05b Definition
4.7 and Proposition 4.8. -/
noncomputable def compactConjugationDiagonalBlock
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    ConstantExtension P r →ₗ[BaseField P] ConstantExtension P r :=
  (Algebra.lmul (BaseField P) (ConstantExtension P r)
      (compactConjugationDiagonalMultiplier P r u k)).comp
    (constantFrobenius P r ^ j).toLinearEquiv.toLinearMap

/-- The unit coefficient used in the monomial conjugation theorem is
exactly evaluation of the linear diagonal block. -/
theorem compactConjugationDiagonalUnit_coe
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (compactConjugationDiagonalUnit P r u v j k : ConstantExtension P r) =
      compactConjugationDiagonalBlock P r u j k
        (v : ConstantExtension P r) := by
  simp only [compactConjugationDiagonalUnit, Units.val_mul, Units.val_inv_eq_inv_val,
    constantFrobeniusUnitEquiv_pow_coe]
  change
    (u : ConstantExtension P r) *
        (constantFrobenius P r ^ j) (v : ConstantExtension P r) *
        ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹ =
      ((u : ConstantExtension P r) *
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹) *
        (constantFrobenius P r ^ j) (v : ConstantExtension P r)
  ring

/-- On the zeroth cyclic block, compact inner conjugation is exactly the
Frobenius power contributed by `z^j`. -/
theorem compactConjugationDiagonalBlock_zero
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ) :
    compactConjugationDiagonalBlock P r u j 0 =
      (constantFrobenius P r ^ j :
        ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r).toLinearEquiv.toLinearMap := by
  ext c
  change
    ((u : ConstantExtension P r) *
        ((constantFrobenius P r ^ (0 : ℕ))
          (u : ConstantExtension P r))⁻¹) *
        (constantFrobenius P r ^ j) c =
      (constantFrobenius P r ^ j) c
  rw [pow_zero]
  simp only [AlgEquiv.one_apply]
  rw [mul_inv_cancel₀ u.ne_zero, one_mul]

/-- The identity-diagonal-block condition imposed at infinity on a
compact normal form.  This definition contains no conclusion data: every
block is computed from `u` and `j`. -/
def CompactNormalFormHasIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ) :
    Prop :=
  ∀ k : Fin r.matrixRank,
    compactConjugationDiagonalBlock P r u j k = LinearMap.id

/-- The zeroth identity block forces the cyclic exponent to act by the
identity Frobenius power. -/
theorem constantFrobenius_pow_eq_one_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    constantFrobenius P r ^ j = 1 := by
  let k0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  have h0 := hdiag k0
  have hblock := compactConjugationDiagonalBlock_zero P r u j
  rw [show (k0 : ℕ) = 0 by rfl, hblock] at h0
  apply AlgEquiv.ext
  intro c
  have hc := LinearMap.congr_fun h0 c
  simpa using hc

/-- In the canonical exponent range, the infinity identity blocks force
the compact cyclic exponent itself to vanish. -/
theorem eq_zero_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j < r.matrixRank)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    j = 0 :=
  eq_zero_of_constantFrobenius_pow_eq_one P r j hj
    (constantFrobenius_pow_eq_one_of_compactIdentityDiagonal P r u j hdiag)

/-- After the cyclic exponent vanishes, the first identity block forces
the leading constant unit to be Frobenius-fixed. -/
theorem constantFrobeniusUnitEquiv_eq_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j = 0)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    constantFrobeniusUnitEquiv P r u = u := by
  let k1 : Fin r.matrixRank :=
    ⟨1, Rank.two_le_matrixRank r⟩
  have h1 := LinearMap.congr_fun (hdiag k1) (1 : ConstantExtension P r)
  have hmul :
      (u : ConstantExtension P r) *
          (constantFrobenius P r (u : ConstantExtension P r))⁻¹ = 1 := by
    simpa [compactConjugationDiagonalBlock,
      compactConjugationDiagonalMultiplier, hj, k1] using h1
  apply Units.ext
  change constantFrobenius P r (u : ConstantExtension P r) = u
  have hFrobNe :
      constantFrobenius P r (u : ConstantExtension P r) ≠ 0 := by
    simp
  exact (mul_inv_eq_one₀ hFrobNe).mp hmul |>.symm

/-- The complete compact obstruction: a normal form in the canonical
exponent range whose infinity conjugation has identity diagonal blocks is
the projective identity. -/
theorem buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j < r.matrixRank)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ j = 1 := by
  have hj0 := eq_zero_of_compactIdentityDiagonal P r u j hj hdiag
  have hu := constantFrobeniusUnitEquiv_eq_of_compactIdentityDiagonal
    P r u j hj0 hdiag
  subst j
  simpa using
    buildingConstantPGLHom_eq_one_of_constantFrobeniusUnitEquiv_eq P r u hu

/-- Representation-independent formulation of the infinity diagonal
condition for a projective building element: every canonical compact
normal form representing it has the computed identity diagonal blocks. -/
def BuildingElementHasIdentityConjugationDiagonal
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) :
    Prop :=
  ∀ (u : (ConstantExtension P r)ˣ) (j : ℕ),
    j < r.matrixRank →
    g = buildingConstantPGLHom P r u *
      buildingCyclicGeneratorPGL P r ^ j →
    CompactNormalFormHasIdentityDiagonal P r u j

/-- The construction-owned compact cyclic subgroup generated by all
represented constants and the cyclic element. -/
noncomputable def BuildingCompactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    Subgroup
      (Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) :=
  Subgroup.closure
    (Set.range (buildingConstantPGLHom P r) ∪
      {buildingCyclicGeneratorPGL P r})

theorem buildingConstantPGL_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) :
    buildingConstantPGLHom P r u ∈ BuildingCompactCyclicSubgroup P r :=
  Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self u))

theorem buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank) :
    buildingCyclicGeneratorPGL P r ∈ BuildingCompactCyclicSubgroup P r :=
  Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))

/-- The compact cyclic subgroup is exactly the image of the Frobenius
semidirect product, not merely a closure with unspecified elements. -/
theorem range_buildingCompactCyclicSemidirectHom
    (P : BasePrime) (r : Rank) :
    (buildingCompactCyclicSemidirectHom P r).range =
      BuildingCompactCyclicSubgroup P r := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    rw [buildingCompactCyclicSemidirectHom_apply]
    exact (BuildingCompactCyclicSubgroup P r).mul_mem
      (buildingConstantPGL_mem_compactCyclicSubgroup P r x.left)
      ((BuildingCompactCyclicSubgroup P r).zpow_mem
        (buildingCyclicGeneratorPGL_mem_compactCyclicSubgroup P r)
        x.right.toAdd)
  · rw [BuildingCompactCyclicSubgroup]
    apply (Subgroup.closure_le _).mpr
    rintro g (hg | hg)
    · obtain ⟨u, rfl⟩ := hg
      refine ⟨SemidirectProduct.inl u, ?_⟩
      simp [buildingCompactCyclicSemidirectHom]
    · rw [Set.mem_singleton_iff] at hg
      subst g
      refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)), ?_⟩
      simp [buildingCompactCyclicSemidirectHom, buildingCyclicZHom]

/-- Every element of the explicit compact cyclic subgroup has a genuine
`u z^n` normal form. -/
theorem exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r) :
    ∃ u : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      g = buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ n := by
  have hgRange : g ∈ (buildingCompactCyclicSemidirectHom P r).range := by
    rw [range_buildingCompactCyclicSemidirectHom P r]
    exact hg
  obtain ⟨x, hx⟩ := hgRange
  exact ⟨x.left, x.right.toAdd,
    hx.symm.trans (buildingCompactCyclicSemidirectHom_apply P r x)⟩

/-- Projective scalar reduction makes the cyclic exponent unique up to the
matrix rank, so every compact normal form can be chosen in
`0 ≤ j < matrixRank`. -/
theorem exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r) :
    ∃ u : (ConstantExtension P r)ˣ, ∃ j : ℕ, j < r.matrixRank ∧
      g = buildingConstantPGLHom P r u *
        buildingCyclicGeneratorPGL P r ^ j := by
  obtain ⟨u, n, hn⟩ :=
    exists_constant_mul_cyclic_zpow_of_mem_compactCyclicSubgroup P r g hg
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by norm_num) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  let m : ℤ := n % (r.matrixRank : ℤ)
  have hmNonneg : 0 ≤ m := Int.emod_nonneg n (ne_of_gt hd)
  have hmLt : m < (r.matrixRank : ℤ) := Int.emod_lt_of_pos n hd
  let j : ℕ := m.toNat
  have hj : j < r.matrixRank := by
    exact (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2 hmLt
  refine ⟨u, j, hj, ?_⟩
  rw [hn]
  have hreduce : buildingCyclicGeneratorPGL P r ^ n =
      buildingCyclicGeneratorPGL P r ^ m := by
    exact zpow_eq_zpow_emod' n
      (buildingCyclicGeneratorPGL_pow_matrixRank P r)
  rw [hreduce]
  congr 1
  rw [← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg hmNonneg).symm

/-- LSV05b Proposition 4.8's compact obstruction, separated cleanly from
the forthcoming global arithmetic inclusion: an element of the explicit
compact cyclic subgroup satisfying the construction-owned infinity
diagonal condition is necessarily trivial. -/
theorem eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r)
    (hdiag : BuildingElementHasIdentityConjugationDiagonal P r g) :
    g = 1 := by
  obtain ⟨u, j, hj, hgForm⟩ :=
    exists_constant_mul_cyclic_pow_of_mem_compactCyclicSubgroup P r g hg
  have hnormalDiag := hdiag u j hj hgForm
  rw [hgForm]
  exact buildingConstant_mul_cyclic_pow_eq_one_of_compactIdentityDiagonal
    P r u j hj hnormalDiag

/-- The explicit constant/cyclic subgroup really is compact: every one of
its generators lies in the maximal compact subgroup. -/
theorem BuildingCompactCyclicSubgroup_le_maximalCompact
    (P : BasePrime) (r : Rank) :
    BuildingCompactCyclicSubgroup P r ≤
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by
  rw [BuildingCompactCyclicSubgroup]
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | hg)
  · obtain ⟨u, rfl⟩ := hg
    exact buildingConstant_mem_maximalCompact P r u
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact buildingCyclicGenerator_mem_maximalCompact P r

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
