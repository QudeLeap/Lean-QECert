import QEC.Coding.AlgebraicGeometry.Differentials.ParameterDifferentialOrder

/-!
# Differential-order transfer through the source's local steps

The index-one case uses a lower uniformizer that is still a uniformizer
upstairs. In the quadratic simple-pole case, differentiating y²+y=a gives
dy=da in characteristic two, and both local parameter differentials have
order -2. No different or canonical-divisor identity is supplied as input.
-/

namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

noncomputable section

variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) K] [IsScalarTower k (RatFunc k) L]
    [IsScalarTower (RatFunc k) K L]
    [Algebra.IsSeparable (RatFunc k) K] [Algebra.IsSeparable (RatFunc k) L]
    [FiniteDimensional (RatFunc k) K] [FiniteDimensional (RatFunc k) L]

/-- Index-one order transport preserves the order of the actual common
rational differential generator. -/
theorem differentialGenerator_order_of_unramified_order_transport
    (P : GlobalPlace k K) (Q : GlobalPlace k L)
    (horder : ∀ x : K, x ≠ 0 → Q.order (algebraMap K L x) = P.order x) :
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := L))
        functionFieldDifferentialGenerator_ne_zero =
      differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero := by
  have ht : P.uniformizer ≠ 0 := by
    intro hz
    have h := P.order_uniformizer
    rw [hz] at h
    simp [GlobalPlace.order] at h
  have htL : algebraMap K L P.uniformizer ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne ht
  have hQt : Q.order (algebraMap K L P.uniformizer) = 1 := by
    rw [horder P.uniformizer ht, P.order_uniformizer]
  obtain ⟨hdt, hP⟩ := differentialGenerator_order_of_order_one_or_neg_one
    P P.uniformizer ht (Or.inl P.order_uniformizer)
  obtain ⟨_, hQ⟩ := differentialGenerator_order_of_order_one_or_neg_one
    Q (algebraMap K L P.uniformizer) htL (Or.inl hQt)
  rw [hQ, hP, hQt, P.order_uniformizer, functionFieldDerivation_algebraMap,
    horder _ hdt]

/-- The displayed characteristic-two simple-pole equation gives precisely
the source's weak-different correction for actual differential orders. -/
theorem differentialGenerator_order_of_quadratic_simplePole [CharP L 2]
    (P : GlobalPlace k K) (Q : GlobalPlace k L) (e : ℕ)
    (horder : ∀ x : K, x ≠ 0 → Q.order (algebraMap K L x) = (e : ℤ) * P.order x)
    (a : K) (y : L) (ha : P.order a = -1) (hyorder : Q.order y = -1)
    (hy : y ^ 2 + y = algebraMap K L a) :
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := L))
        functionFieldDifferentialGenerator_ne_zero =
      (e : ℤ) * differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
        functionFieldDifferentialGenerator_ne_zero + 2 * ((e : ℤ) - 1) := by
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz, GlobalPlace.order] at ha
  have hy0 : y ≠ 0 := by
    intro hz
    simp [hz, GlobalPlace.order] at hyorder
  obtain ⟨hda, hP⟩ := differentialGenerator_order_of_order_one_or_neg_one P a ha0 (Or.inr ha)
  obtain ⟨_, hQ⟩ := differentialGenerator_order_of_order_one_or_neg_one Q y hy0 (Or.inr hyorder)
  have hderiv : functionFieldDerivation (k := k) (F := L) y =
      algebraMap K L (functionFieldDerivation (k := k) (F := K) a) := by
    have h := congrArg (functionFieldDerivation (k := k) (F := L)) hy
    rw [map_add, Derivation.leibniz_pow] at h
    simpa only [Nat.cast_ofNat, nsmul_eq_mul, CharTwo.two_eq_zero, zero_mul,
      zero_smul, zero_add, functionFieldDerivation_algebraMap] using h
  rw [hQ, hP, hyorder, ha, hderiv, horder _ hda]
  ring

end

end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
