import QEC.Coding.FiniteFieldMultiplication.SelfDualBasis

namespace QEC.Coding

/-- The three polynomial-coordinate factors underlying the length-512 MFE. -/
abbrev F256MFEIndex := Fin 8 × (Fin 8 × Fin 8)

/-- The concrete flattening of three eight-coordinate factors to `Fin 512`. -/
noncomputable def f256MFEIndexEquiv : F256MFEIndex ≃ Fin 512 :=
  ((Equiv.refl (Fin 8)).prodCongr (finProdFinEquiv (m := 8) (n := 8))).trans
    (finProdFinEquiv (m := 8) (n := 64))

/-- The coordinate with polynomial indices `(i,j,k)`. -/
noncomputable def f256MFEIndex (i j k : Fin 8) : Fin 512 :=
  f256MFEIndexEquiv (i, (j, k))

/-- The first cyclic coordinate permutation of the length-512 carrier. -/
noncomputable def f256MFEpi2 : Equiv.Perm (Fin 512) :=
  (f256MFEIndexEquiv.symm.trans
    ((Equiv.prodComm (Fin 8) (Fin 8 × Fin 8)).trans
      (Equiv.prodAssoc (Fin 8) (Fin 8) (Fin 8)))).trans f256MFEIndexEquiv

/-- The second cyclic coordinate permutation of the length-512 carrier. -/
noncomputable def f256MFEpi3 : Equiv.Perm (Fin 512) :=
  f256MFEpi2.trans f256MFEpi2

/-- Reindex a binary coordinate vector by an actual finite permutation. -/
noncomputable def f256MFEPermutationAction (pi : Equiv.Perm (Fin 512)) :
    (Fin 512 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) where
  toFun v := fun q => v (pi q)
  map_add' v w := by
    ext q
    rfl
  map_smul' c v := by
    ext q
    rfl

/-- The action of the first cyclic coordinate permutation. -/
noncomputable def f256MFEpi2Action : (Fin 512 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) :=
  f256MFEPermutationAction f256MFEpi2

/-- The action of the second cyclic coordinate permutation. -/
noncomputable def f256MFEpi3Action : (Fin 512 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) :=
  f256MFEPermutationAction f256MFEpi3

/-- Embed a field element by repeating its first polynomial-basis coordinate. -/
noncomputable def f256MFESigma : F256 →ₗ[ZMod 2] (Fin 512 → ZMod 2) where
  toFun x := fun q => f256PolynomialBasis.equivFun x (f256MFEIndexEquiv.symm q).1
  map_add' x y := by
    ext q
    simp only [map_add, Pi.add_apply]
  map_smul' c x := by
    ext q
    have hsmul := congr_fun (f256PolynomialBasis.equivFun.map_smul c x)
      (f256MFEIndexEquiv.symm q).1
    simpa only [Pi.smul_apply, RingHom.id_apply] using hsmul

/-- Contract the three polynomial-coordinate factors against multiplication in `F256`. -/
noncomputable def f256MFEPsi : (Fin 512 → ZMod 2) →ₗ[ZMod 2] F256 where
  toFun v :=
    ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
      v (f256MFEIndex i j k) •
        (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    change
      (∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        (c * v (f256MFEIndex i j k)) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k)) =
        c • ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
          v (f256MFEIndex i j k) •
            (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k)
    simp only [Finset.smul_sum, smul_smul]

/-- The first permutation sends `(i,j,k)` to `(j,k,i)`. -/
theorem f256MFEpi2_apply (i j k : Fin 8) :
    f256MFEpi2 (f256MFEIndex i j k) = f256MFEIndex j k i := by
  simp [f256MFEpi2, f256MFEIndex]

/-- The second permutation sends `(i,j,k)` to `(k,i,j)`. -/
theorem f256MFEpi3_apply (i j k : Fin 8) :
    f256MFEpi3 (f256MFEIndex i j k) = f256MFEIndex k i j := by
  rw [f256MFEpi3, Equiv.trans_apply, f256MFEpi2_apply, f256MFEpi2_apply]

/-- Evaluation of the concrete coordinate embedding. -/
theorem f256MFESigma_apply (x : F256) (i j k : Fin 8) :
    f256MFESigma x (f256MFEIndex i j k) = f256PolynomialBasis.equivFun x i := by
  simp [f256MFESigma, f256MFEIndex]

/-- Evaluation of the contraction map on a coordinate vector. -/
theorem f256MFEPsi_apply (v : Fin 512 → ZMod 2) :
    f256MFEPsi v =
      ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        v (f256MFEIndex i j k) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k) := rfl

/-- Evaluation of a reindexing action. -/
theorem f256MFEPermutationAction_apply (pi : Equiv.Perm (Fin 512))
    (v : Fin 512 → ZMod 2) (q : Fin 512) :
    f256MFEPermutationAction pi v q = v (pi q) := rfl

/-- The first action exposes the second polynomial coordinate. -/
theorem f256MFEpi2_sigma_apply (y : F256) (i j k : Fin 8) :
    f256MFEpi2Action (f256MFESigma y) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun y j := by
  rw [f256MFEpi2Action, f256MFEPermutationAction_apply, f256MFEpi2_apply,
    f256MFESigma_apply]

/-- The second action exposes the third polynomial coordinate. -/
theorem f256MFEpi3_sigma_apply (z : F256) (i j k : Fin 8) :
    f256MFEpi3Action (f256MFESigma z) (f256MFEIndex i j k) =
      f256PolynomialBasis.equivFun z k := by
  rw [f256MFEpi3Action, f256MFEPermutationAction_apply, f256MFEpi3_apply,
    f256MFESigma_apply]

/-- The concrete coordinate embedding is injective. -/
theorem f256MFESigma_injective : Function.Injective f256MFESigma := by
  intro x y hxy
  apply f256PolynomialBasis.equivFun.injective
  ext i
  have hcoordinate := congr_fun hxy (f256MFEIndex i 0 0)
  simpa only [f256MFESigma_apply] using hcoordinate

/-- Each actual coordinate permutation is bijective. -/
theorem f256MFEpi2_bijective : Function.Bijective f256MFEpi2 :=
  f256MFEpi2.bijective

/-- Each actual coordinate permutation is bijective. -/
theorem f256MFEpi3_bijective : Function.Bijective f256MFEpi3 :=
  f256MFEpi3.bijective

/-- The concrete maps satisfy the degree-three reverse-multiplication identity. -/
theorem f256MFE_ternary_reverse_mul (x y z : F256) :
    f256MFEPsi (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
      f256MFEpi3Action (f256MFESigma z)) = x * y * z := by
  calc
    f256MFEPsi (f256MFESigma x * f256MFEpi2Action (f256MFESigma y) *
        f256MFEpi3Action (f256MFESigma z)) =
        (∑ i : Fin 8, f256PolynomialBasis.equivFun x i • f256PolynomialBasis i) *
          (∑ j : Fin 8, f256PolynomialBasis.equivFun y j • f256PolynomialBasis j) *
          ∑ k : Fin 8, f256PolynomialBasis.equivFun z k • f256PolynomialBasis k := by
      rw [f256MFEPsi_apply]
      simp only [Pi.mul_apply, f256MFESigma_apply, f256MFEpi2_sigma_apply,
        f256MFEpi3_sigma_apply]
      rw [Fintype.sum_mul_sum]
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      simp only [Algebra.smul_def, map_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = x * y * z := by
      rw [f256PolynomialBasis.sum_equivFun x, f256PolynomialBasis.sum_equivFun y,
        f256PolynomialBasis.sum_equivFun z]

/-- The contraction map has a concrete preimage for every field element. -/
theorem f256MFEPsi_surjective : Function.Surjective f256MFEPsi := by
  intro x
  refine ⟨f256MFESigma x * f256MFEpi2Action (f256MFESigma 1) *
    f256MFEpi3Action (f256MFESigma 1), ?_⟩
  simpa using f256MFE_ternary_reverse_mul x 1 1

end QEC.Coding
