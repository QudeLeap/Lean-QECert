import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWFibreDivisors
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PolarDegree

/-!
# The principal divisor of the source F256(w) generator

The relation `w ^ 15 = z` transfers the already-constructed pole-degree
formula for the rational base coordinate to the literal intermediate
generator.  The known zero and infinity fibres attain that full degree, so
coefficientwise inclusion and positivity identify both parts of the
principal divisor.

No ramification value, different, genus, or canonical differential is
asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

open IntermediateField
open scoped Polynomial RatFunc

noncomputable section

private abbrev E (m : ℕ) := SourceGaloisClosureField m

private abbrev ClosurePlace (m : ℕ) :=
  @GlobalPlace F256 (E m) _ _ _ (sourceGaloisClosureConstantAlgebra m)

private noncomputable local instance closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (E m) :=
  ((algebraMap (RatFunc F256) (E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra

private noncomputable local instance closurePolynomialRatFuncScalarTower
    (m : ℕ) : IsScalarTower (Polynomial F256) (RatFunc F256) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (E m) :=
  IsGalois.to_isSeparable

private abbrev DirectClosurePlace (m : ℕ) :=
  @GlobalPlace F256 (E m) _ _ _
    (@AffinePlace.constantAlgebra F256 (E m) _ _
      (closurePolynomialAlgebra m))

private abbrev directClosureOrder (m : ℕ)
    (P : DirectClosurePlace m) (x : E m) : ℤ :=
  @GlobalPlace.order F256 (E m) _ _ _
    (@AffinePlace.constantAlgebra F256 (E m) _ _
      (closurePolynomialAlgebra m)) P x

private abbrev closureOrder (m : ℕ)
    (P : ClosurePlace m) (x : E m) : ℤ :=
  @GlobalPlace.order F256 (E m) _ _ _ (sourceGaloisClosureConstantAlgebra m) P x

private noncomputable abbrev directClosureResidueDegree (m : ℕ) :
    DirectClosurePlace m → ℕ :=
  fun P => GlobalPlace.residueDegree
    (π := closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (σ := closureRatFuncIsSeparable m)
    (κ := @AffinePlace.constantAlgebra F256 (E m) _ _
      (closurePolynomialAlgebra m)) P

private noncomputable abbrev closureResidueDegree (m : ℕ) :
    ClosurePlace m → ℕ :=
  fun P => GlobalPlace.residueDegree
    (π := closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (σ := closureRatFuncIsSeparable m)
    (κ := sourceGaloisClosureConstantAlgebra m) P

private noncomputable def closurePlaceEquiv (m : ℕ) :
    DirectClosurePlace m ≃ ClosurePlace m :=
  GlobalPlace.repackageEquiv
    (@AffinePlace.constantAlgebra F256 (E m) _ _
      (closurePolynomialAlgebra m))
    (sourceGaloisClosureConstantAlgebra m)

/- `GlobalPlace.polarDivisor` is compiled on the direct-chart constant
algebra.  This definition has the same coefficient formula on the canonical
normal-closure carrier used by the fibre divisors. -/
private noncomputable def polarDivisorOnClosure (m : ℕ) (x : E m) :
    Divisor (ClosurePlace m) := by
  classical
  exact if hx : x = 0 then 0
    else (-GlobalPlace.principalDivisor (k := F256) (F := E m)
      (Units.mk0 x hx)) ⊔ 0

private noncomputable def polarDivisorOnDirectClosure (m : ℕ) (x : E m) :
    Divisor (DirectClosurePlace m) :=
  GlobalPlace.polarDivisor
    (π := closurePolynomialAlgebra m)
    (ρ := sourceGaloisClosureRatFuncAlgebra m)
    (τ := closurePolynomialRatFuncScalarTower m)
    (φ := sourceGaloisClosureFunctionField m)
    (s := closureRatFuncIsSeparable m)
    (k := F256) (F := E m) x

private theorem closurePlaceEquiv_symm_order (m : ℕ)
    (P : ClosurePlace m) (x : E m) :
    directClosureOrder m ((closurePlaceEquiv m).symm P) x =
      closureOrder m P x := by
  change -WithZero.log
      (@GlobalPlace.valuation F256 (E m) _ _ _
        (@AffinePlace.constantAlgebra F256 (E m) _ _
          (closurePolynomialAlgebra m))
        ((closurePlaceEquiv m).symm P) x) =
    -WithZero.log
      (@GlobalPlace.valuation F256 (E m) _ _ _
        (sourceGaloisClosureConstantAlgebra m) P x)
  rfl

private theorem polarDivisorOnClosure_apply_of_ne (m : ℕ) (x : E m)
    (P : ClosurePlace m) (hx : x ≠ 0) :
    polarDivisorOnClosure m x P = max (-closureOrder m P x) 0 := by
  unfold polarDivisorOnClosure
  simp only [dif_neg hx, Finsupp.sup_apply, Finsupp.neg_apply,
    Finsupp.zero_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0]

private theorem polarDivisorOnDirectClosure_apply_of_ne (m : ℕ) (x : E m)
    (P : DirectClosurePlace m) (hx : x ≠ 0) :
    polarDivisorOnDirectClosure m x P =
      max (-directClosureOrder m P x) 0 := by
  unfold polarDivisorOnDirectClosure GlobalPlace.polarDivisor
  simp only [dif_neg hx, Finsupp.sup_apply, Finsupp.neg_apply,
    Finsupp.zero_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0]

private theorem polarDivisorOnClosure_nonnegative (m : ℕ) (x : E m) :
    Divisor.Nonnegative (polarDivisorOnClosure m x) := by
  intro P
  unfold polarDivisorOnClosure
  split_ifs
  · simp
  · exact le_sup_right

private noncomputable def transportedDirectPolarDivisor (m : ℕ) (x : E m) :
    Divisor (ClosurePlace m) :=
  Finsupp.equivMapDomain (closurePlaceEquiv m)
    (polarDivisorOnDirectClosure m x)

private theorem transportedDirectPolarDivisor_eq (m : ℕ) (x : E m) :
    transportedDirectPolarDivisor m x =
      polarDivisorOnClosure m x := by
  classical
  ext P
  by_cases hx : x = 0
  · subst x
    simp [transportedDirectPolarDivisor, polarDivisorOnDirectClosure,
      GlobalPlace.polarDivisor, polarDivisorOnClosure]
  · rw [transportedDirectPolarDivisor, Finsupp.equivMapDomain_apply,
      polarDivisorOnDirectClosure_apply_of_ne m x _ hx,
      polarDivisorOnClosure_apply_of_ne m x P hx,
      closurePlaceEquiv_symm_order m P x]

private theorem divisor_degree_equivMapDomain
    {α β : Type*} (e : α ≃ β) (weight : β → ℕ) (D : Divisor α) :
    Divisor.degree weight (Finsupp.equivMapDomain e D) =
      Divisor.degree (fun a => weight (e a)) D := by
  change (Finsupp.equivMapDomain e D).sum
      (fun b coefficient => coefficient * (weight b : ℤ)) =
    D.sum (fun a coefficient => coefficient * (weight (e a) : ℤ))
  rw [Finsupp.sum_equivMapDomain]

private theorem sourceGaloisClosure_chartVariable_polarDivisor_degree (m : ℕ) :
    Divisor.degree (closureResidueDegree m)
        (polarDivisorOnClosure m
          (GlobalPlace.chartVariable (k := F256) (F := E m))) =
      (Module.finrank (RatFunc F256) (E m) : ℤ) := by
  let e := closurePlaceEquiv m
  let D := polarDivisorOnDirectClosure m
    (GlobalPlace.chartVariable (k := F256) (F := E m))
  rw [← transportedDirectPolarDivisor_eq m]
  change Divisor.degree (closureResidueDegree m)
    (Finsupp.equivMapDomain e D) = _
  calc
    Divisor.degree (closureResidueDegree m)
        (Finsupp.equivMapDomain e D) =
        Divisor.degree (fun P => closureResidueDegree m (e P)) D :=
      divisor_degree_equivMapDomain e (closureResidueDegree m) D
    _ = Divisor.degree (directClosureResidueDegree m) D := by
      congr 1
      funext P
      exact GlobalPlace.residueDegree_repackage
        (@AffinePlace.constantAlgebra F256 (E m) _ _
          (closurePolynomialAlgebra m))
        (sourceGaloisClosureConstantAlgebra m) P
    _ = (Module.finrank (RatFunc F256) (E m) : ℤ) := by
      dsimp only [D, polarDivisorOnDirectClosure,
        directClosureResidueDegree]
      exact GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank
        (π := closurePolynomialAlgebra m)
        (ρ := sourceGaloisClosureRatFuncAlgebra m)
        (τ := closurePolynomialRatFuncScalarTower m)
        (φ := sourceGaloisClosureFunctionField m)
        (s := closureRatFuncIsSeparable m)
        (k := F256) (F := E m)

/-- The embedded intermediate generator is nonzero in every source-normal-closure
level. -/
theorem sourceGaloisWClosureGenerator_ne_zero (m : ℕ) :
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ≠ 0 := by
  let P : SourceGaloisWInfinityPrime m :=
    Classical.choice (sourceGaloisWInfinityPrime_nonempty m)
  have horder := sourceGaloisWInfinityPlaceOfPrime_order_generator m P
  intro hzero
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder
  have hpositive := sourceGaloisWInfinityRamificationIndex_pos m
  omega

/-- The pole divisor of the embedded generator, on the canonical
normal-closure place carrier. -/
noncomputable def sourceGaloisWClosureGeneratorPoleDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (E m)) :=
  polarDivisorOnClosure m
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)

/-- The coefficient of the generator's pole divisor is the negative part of
its normalized order at the actual global place. -/
@[simp]
theorem sourceGaloisWClosureGeneratorPoleDivisor_apply (m : ℕ)
    (P : GlobalPlace F256 (E m)) :
    sourceGaloisWClosureGeneratorPoleDivisor m P =
      max (-P.order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)) 0 := by
  exact polarDivisorOnClosure_apply_of_ne m _ P
    (sourceGaloisWClosureGenerator_ne_zero m)

private theorem order_pow (m n : ℕ)
    (P : GlobalPlace F256 (E m)) (x : E m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [(P.valuation).map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

private theorem sourceGaloisWClosureGenerator_pow_fifteen_eq_chartVariable
    (m : ℕ) :
    ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ^ 15 =
      GlobalPlace.chartVariable (k := F256) (F := E m) := by
  rw [sourceGaloisWClosureGenerator_pow_fifteen]
  change algebraMap GaloisBaseField (E m)
      (AdjoinSimple.gen F256 galoisBaseZ) =
    sourceGaloisClosureRatFuncEmbedding m RatFunc.X
  change algebraMap GaloisBaseField (E m)
      (AdjoinSimple.gen F256 galoisBaseZ) =
    algebraMap GaloisBaseField (E m)
      (galoisBaseFieldEquivRatFunc RatFunc.X)
  have hX : galoisBaseFieldEquivRatFunc RatFunc.X =
      AdjoinSimple.gen F256 galoisBaseZ := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X
      galoisBaseZ galoisBaseZ_transcendental
  rw [hX]

private theorem sourceGaloisWClosureGenerator_polarDivisor_pow_fifteen
    (m : ℕ) :
    polarDivisorOnClosure m
        (((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ^ 15) =
      15 • polarDivisorOnClosure m
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) := by
  let w : E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  have hw : w ≠ 0 := sourceGaloisWClosureGenerator_ne_zero m
  have hw_pow : w ^ 15 ≠ 0 := pow_ne_zero 15 hw
  ext P
  change polarDivisorOnClosure m (w ^ 15) P =
    (15 • polarDivisorOnClosure m w) P
  simp only [polarDivisorOnClosure, dif_neg hw_pow, dif_neg hw,
    Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply,
    GlobalPlace.principalDivisor_apply, Units.val_mk0,
    Finsupp.smul_apply, nsmul_eq_mul]
  rw [order_pow m 15 P w]
  by_cases horder : 0 ≤ -P.order w
  · rw [max_eq_left horder, max_eq_left]
    · ring
    · omega
  · rw [max_eq_right (le_of_not_ge horder), max_eq_right]
    · simp
    · omega

private theorem sourceGaloisWClosureGenerator_polarDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWClosureGeneratorPoleDivisor m) =
      (sourceGaloisWRelativeDegree m : ℤ) := by
  let D := sourceGaloisWClosureGeneratorPoleDivisor m
  have hscaled :
      (15 : ℤ) * Divisor.degree GlobalPlace.residueDegree D =
        (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) := by
    calc
      (15 : ℤ) * Divisor.degree GlobalPlace.residueDegree D =
          Divisor.degree GlobalPlace.residueDegree (15 • D) := by
        symm
        have h := (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul 15 D
        simp only [nsmul_eq_mul] at h
        exact h
      _ = Divisor.degree GlobalPlace.residueDegree
          (polarDivisorOnClosure m
            (((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ^
              15)) :=
        congrArg (Divisor.degree GlobalPlace.residueDegree)
          (sourceGaloisWClosureGenerator_polarDivisor_pow_fifteen m).symm
      _ = Divisor.degree GlobalPlace.residueDegree
          (polarDivisorOnClosure m
            (GlobalPlace.chartVariable (k := F256) (F := E m))) := by
        rw [sourceGaloisWClosureGenerator_pow_fifteen_eq_chartVariable]
      _ = (Module.finrank (RatFunc F256) (E m) : ℤ) :=
        sourceGaloisClosure_chartVariable_polarDivisor_degree m
      _ = (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) := by
        rw [sourceGaloisClosureField_ratFunc_finrank]
        norm_cast
        simpa only [sourceGaloisClosureSelectedLength] using
          (sourceGaloisWRelativeDegree_mul_fifteen m).symm
  dsimp only [D, sourceGaloisWClosureGeneratorPoleDivisor] at hscaled ⊢
  omega

private theorem residueDegree_pos (m : ℕ) (P : GlobalPlace F256 (E m)) :
    0 < GlobalPlace.residueDegree (k := F256) (F := E m) P := by
  letI : Algebra F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueAlgebra P
  letI : FiniteDimensional F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  rw [GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos

private theorem divisorDegree_mono (m : ℕ)
    {D R : Divisor (GlobalPlace F256 (E m))} (hDR : D ≤ R) :
    Divisor.degree GlobalPlace.residueDegree D ≤
      Divisor.degree GlobalPlace.residueDegree R := by
  have hnonnegative : Divisor.Nonnegative (R - D) := by
    intro P
    exact sub_nonneg.mpr (hDR P)
  have hdegree_nonnegative :
      0 ≤ Divisor.degree GlobalPlace.residueDegree (R - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have heq : D + (R - D) = R := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [← heq, Divisor.degree_add]
  exact le_add_of_nonneg_right hdegree_nonnegative

private theorem divisorDegree_single (m : ℕ)
    (P : GlobalPlace F256 (E m)) (coefficient : ℤ) :
    Divisor.degree GlobalPlace.residueDegree
        (Finsupp.single P coefficient) =
      coefficient * (GlobalPlace.residueDegree P : ℤ) := by
  simp [Divisor.degree, Divisor.degreeHom]

private theorem divisor_eq_of_le_of_degree_eq (m : ℕ)
    {D R : Divisor (GlobalPlace F256 (E m))} (hDR : D ≤ R)
    (hdegree : Divisor.degree GlobalPlace.residueDegree D =
      Divisor.degree GlobalPlace.residueDegree R) :
    R = D := by
  classical
  apply Finsupp.ext
  intro P
  have hnonnegative : 0 ≤ R P - D P := sub_nonneg.mpr (hDR P)
  have hdegree_sub :
      Divisor.degree GlobalPlace.residueDegree (R - D) = 0 := by
    rw [Divisor.degree_sub, hdegree, sub_self]
  have hsingle_le : Finsupp.single P (R P - D P) ≤ R - D := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQP)]
      exact sub_nonneg.mpr (hDR Q)
  have hsingle_degree_le := divisorDegree_mono m hsingle_le
  rw [divisorDegree_single, hdegree_sub] at hsingle_degree_le
  have hresidue : 0 < (GlobalPlace.residueDegree P : ℤ) := by
    exact_mod_cast residueDegree_pos m P
  have hcoefficient : R P - D P = 0 := by
    by_contra hne
    have hpositive : 0 < R P - D P := lt_of_le_of_ne hnonnegative
      (Ne.symm hne)
    exact (not_lt_of_ge hsingle_degree_le)
      (mul_pos hpositive hresidue)
  omega

private theorem infinityFibre_smul_le_polarDivisor (m : ℕ) :
    sourceGaloisWInfinityRamificationIndex m • sourceGaloisWInfinityFibreDivisor m ≤
      sourceGaloisWClosureGeneratorPoleDivisor m := by
  classical
  intro Q
  letI : Decidable (Q ∈ Set.range (sourceGaloisWInfinityPlaceOfPrime m)) :=
    Classical.propDecidable _
  by_cases hQ : Q ∈ Set.range (sourceGaloisWInfinityPlaceOfPrime m)
  · rcases hQ with ⟨P, rfl⟩
    have hw := sourceGaloisWClosureGenerator_ne_zero m
    simp only [Finsupp.smul_apply, nsmul_eq_mul,
      sourceGaloisWInfinityFibreDivisor_apply, mul_one,
      sourceGaloisWClosureGeneratorPoleDivisor, polarDivisorOnClosure,
      dif_neg hw, Finsupp.sup_apply,
      Finsupp.neg_apply, Finsupp.zero_apply,
      GlobalPlace.principalDivisor_apply, Units.val_mk0]
    rw [sourceGaloisWInfinityPlaceOfPrime_order_generator]
    simpa only [neg_neg] using
      (le_max_left (sourceGaloisWInfinityRamificationIndex m : ℤ) 0)
  · have hzero : sourceGaloisWInfinityFibreDivisor m Q = 0 := by
      by_contra hne
      have hmem : Q ∈ ↑(sourceGaloisWInfinityFibreDivisor m).support :=
        Divisor.mem_support_iff.mpr hne
      have hmemSet : Q ∈
          (↑(sourceGaloisWInfinityFibreDivisor m).support : Set _) := by
        exact hmem
      rw [sourceGaloisWInfinityFibreDivisor_support] at hmemSet
      exact hQ hmemSet
    rw [Finsupp.smul_apply, hzero, nsmul_zero]
    exact polarDivisorOnClosure_nonnegative m _ Q

/-- The pole divisor of the embedded generator is exactly its actual
infinity fibre, weighted by the common ramification index. -/
theorem sourceGaloisWClosureGenerator_polarDivisor (m : ℕ) :
    sourceGaloisWClosureGeneratorPoleDivisor m =
      sourceGaloisWInfinityRamificationIndex m •
        sourceGaloisWInfinityFibreDivisor m := by
  apply divisor_eq_of_le_of_degree_eq m
    (infinityFibre_smul_le_polarDivisor m)
  calc
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWInfinityRamificationIndex m •
          sourceGaloisWInfinityFibreDivisor m) =
        (sourceGaloisWInfinityRamificationIndex m : ℤ) *
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisWInfinityFibreDivisor m) := by
      simpa only [Divisor.degree, nsmul_eq_mul] using
        (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul
          (sourceGaloisWInfinityRamificationIndex m)
          (sourceGaloisWInfinityFibreDivisor m)
    _ = (sourceGaloisWRelativeDegree m : ℤ) :=
      sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree m
    _ = Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWClosureGeneratorPoleDivisor m) :=
      (sourceGaloisWClosureGenerator_polarDivisor_degree m).symm

private theorem principalDivisor_add_polarDivisor_nonnegative (m : ℕ) :
    Divisor.Nonnegative
      (GlobalPlace.principalDivisor (k := F256) (F := E m)
          (Units.mk0
            ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
            (sourceGaloisWClosureGenerator_ne_zero m)) +
        sourceGaloisWClosureGeneratorPoleDivisor m) := by
  intro P
  have hw := sourceGaloisWClosureGenerator_ne_zero m
  simp only [Finsupp.add_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0, sourceGaloisWClosureGeneratorPoleDivisor,
    polarDivisorOnClosure, dif_neg hw,
    Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply]
  omega

private theorem zeroFibre_smul_le_principal_add_polar (m : ℕ) :
    sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m ≤
      GlobalPlace.principalDivisor (k := F256) (F := E m)
          (Units.mk0
            ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
            (sourceGaloisWClosureGenerator_ne_zero m)) +
        sourceGaloisWClosureGeneratorPoleDivisor m := by
  classical
  intro Q
  letI : Decidable (Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m)) :=
    Classical.propDecidable _
  by_cases hQ : Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m)
  · rcases hQ with ⟨P, rfl⟩
    have hw := sourceGaloisWClosureGenerator_ne_zero m
    simp only [Finsupp.smul_apply, nsmul_eq_mul,
      sourceGaloisWZeroFibreDivisor_apply, mul_one, Finsupp.add_apply,
      GlobalPlace.principalDivisor_apply, Units.val_mk0,
      sourceGaloisWClosureGeneratorPoleDivisor, polarDivisorOnClosure,
      dif_neg hw, Finsupp.sup_apply,
      Finsupp.neg_apply, Finsupp.zero_apply]
    rw [sourceGaloisWZeroPlaceOfPrime_order_generator]
    have hnonnegative :
        0 ≤ (sourceGaloisWZeroRamificationIndex m : ℤ) := by positivity
    rw [max_eq_right (by omega), add_zero]
  · have hzero : sourceGaloisWZeroFibreDivisor m Q = 0 := by
      by_contra hne
      have hmem : Q ∈ ↑(sourceGaloisWZeroFibreDivisor m).support :=
        Divisor.mem_support_iff.mpr hne
      have hmemSet : Q ∈
          (↑(sourceGaloisWZeroFibreDivisor m).support : Set _) := by
        exact hmem
      rw [sourceGaloisWZeroFibreDivisor_support] at hmemSet
      exact hQ hmemSet
    rw [Finsupp.smul_apply, hzero, nsmul_zero]
    exact principalDivisor_add_polarDivisor_nonnegative m Q

private theorem principalDivisor_add_polarDivisor_eq_zeroFibre (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := E m)
          (Units.mk0
            ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
            (sourceGaloisWClosureGenerator_ne_zero m)) +
        sourceGaloisWClosureGeneratorPoleDivisor m =
      sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m := by
  apply divisor_eq_of_le_of_degree_eq m
    (zeroFibre_smul_le_principal_add_polar m)
  calc
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m) =
        (sourceGaloisWZeroRamificationIndex m : ℤ) *
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisWZeroFibreDivisor m) := by
      simpa only [Divisor.degree, nsmul_eq_mul] using
        (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul
          (sourceGaloisWZeroRamificationIndex m) (sourceGaloisWZeroFibreDivisor m)
    _ = (sourceGaloisWRelativeDegree m : ℤ) :=
      sourceGaloisWZeroRamificationIndex_mul_fibreDivisor_degree m
    _ = Divisor.degree GlobalPlace.residueDegree
        (GlobalPlace.principalDivisor (k := F256) (F := E m)
            (Units.mk0
              ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
              (sourceGaloisWClosureGenerator_ne_zero m)) +
          sourceGaloisWClosureGeneratorPoleDivisor m) := by
      rw [Divisor.degree_add, GlobalPlace.principalDivisor_degree_zero,
        zero_add, sourceGaloisWClosureGenerator_polarDivisor_degree]

/-- The actual principal divisor of `w` is its ramification-weighted zero
fibre minus its ramification-weighted infinity fibre. -/
theorem sourceGaloisWClosureGenerator_principalDivisor (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := E m)
        (Units.mk0
          ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
          (sourceGaloisWClosureGenerator_ne_zero m)) =
      sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWInfinityRamificationIndex m •
          sourceGaloisWInfinityFibreDivisor m := by
  calc
    GlobalPlace.principalDivisor (k := F256) (F := E m)
        (Units.mk0
          ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
          (sourceGaloisWClosureGenerator_ne_zero m)) =
        (GlobalPlace.principalDivisor (k := F256) (F := E m)
            (Units.mk0
              ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
              (sourceGaloisWClosureGenerator_ne_zero m)) +
          sourceGaloisWClosureGeneratorPoleDivisor m) -
          sourceGaloisWClosureGeneratorPoleDivisor m := by
      abel
    _ = sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWClosureGeneratorPoleDivisor m := by
      rw [principalDivisor_add_polarDivisor_eq_zeroFibre]
    _ = sourceGaloisWZeroRamificationIndex m • sourceGaloisWZeroFibreDivisor m -
        sourceGaloisWInfinityRamificationIndex m •
          sourceGaloisWInfinityFibreDivisor m := by
      rw [sourceGaloisWClosureGenerator_polarDivisor]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
