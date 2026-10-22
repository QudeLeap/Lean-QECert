import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Arithmetic.PrasadSpecialization

/-!
# Denominator correction for the Cartwright--Steger Prasad specialization

This module develops the placewise infrastructure used to remove the finite
denominator support of a global reduced-norm-one point.  Every declaration is
specialized to the Cartwright--Steger arithmetic ring and cyclic algebra; no
general adelic algebraic-group interface is introduced here.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open scoped TensorProduct

noncomputable local instance arithmeticFinitePlaceDecidableEq (P : BasePrime) :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  Classical.decEq _

/-! ## One-place scalar support at an arbitrary arithmetic finite place -/

/-- Insert one completed scalar at a specified arithmetic finite place and
zero at every other place. -/
noncomputable def arithmeticFiniteAdeleSupportedAtPlace
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    ArithmeticFiniteAdeleRing P := by
  classical
  refine ⟨Pi.single v x, ?_⟩
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton v)
  intro w hw
  simp only [Set.mem_singleton_iff]
  by_contra hwv
  apply hw
  rw [Pi.single_eq_of_ne hwv]
  exact (w.adicCompletionIntegers (FunctionField P)).zero_mem

@[simp] theorem arithmeticFiniteAdeleAt_supportedAtPlace
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleAt P v
        (arithmeticFiniteAdeleSupportedAtPlace P v x) = x := by
  classical
  change Pi.single v x v = x
  exact Pi.single_eq_same v x

theorem arithmeticFiniteAdeleAt_supportedAtPlace_of_ne
    (P : BasePrime)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hvw : w ≠ v)
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleAt P w
        (arithmeticFiniteAdeleSupportedAtPlace P v x) = 0 := by
  classical
  change Pi.single v x w = 0
  rw [Pi.single_eq_of_ne hvw]

/-- One-place scalar support is integral at all arithmetic finite places
exactly when its nonzero coordinate is integral. -/
theorem arithmeticFiniteAdeleSupportedAtPlace_mem_integral_iff
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : v.adicCompletion (FunctionField P)) :
    arithmeticFiniteAdeleSupportedAtPlace P v x ∈
        ArithmeticIntegralFiniteAdeles P ↔
      x ∈ v.adicCompletionIntegers (FunctionField P) := by
  classical
  constructor
  · intro hx
    have hv := hx v
    change Pi.single v x v ∈
      v.adicCompletionIntegers (FunctionField P) at hv
    rw [Pi.single_eq_same] at hv
    exact hv
  · intro hx w
    by_cases hwv : w = v
    · subst w
      change Pi.single v x v ∈
        v.adicCompletionIntegers (FunctionField P)
      rw [Pi.single_eq_same]
      exact hx
    · change Pi.single v x w ∈
          w.adicCompletionIntegers (FunctionField P)
      rw [Pi.single_eq_of_ne hwv]
      exact (w.adicCompletionIntegers (FunctionField P)).zero_mem

/-- One-place support preserves addition and multiplication but is
nonunital: the local unit maps to the idempotent selecting that place. -/
noncomputable def arithmeticFiniteAdeleSupportedAtPlaceNonUnitalRingHom
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    v.adicCompletion (FunctionField P) →ₙ+* ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtPlace P v
  map_zero' := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v 0 w = 0
    by_cases hwv : w = v
    · subst w
      simp
    · rw [Pi.single_eq_of_ne hwv]
  map_add' := by
    intro x y
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v (x + y) w = Pi.single v x w + Pi.single v y w
    by_cases hwv : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hwv]
  map_mul' := by
    intro x y
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
    by_cases hwv : w = v
    · subst w
      simp
    · simp [Pi.single_eq_of_ne hwv]

/-- The scalar one-place insertion as a global-function-field linear map. -/
noncomputable def arithmeticFiniteAdeleSupportedAtPlaceLinearMap
    (P : BasePrime)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    v.adicCompletion (FunctionField P) →ₗ[FunctionField P]
      ArithmeticFiniteAdeleRing P where
  toFun := arithmeticFiniteAdeleSupportedAtPlace P v
  map_add' := map_add
    (arithmeticFiniteAdeleSupportedAtPlaceNonUnitalRingHom P v)
  map_smul' a x := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    classical
    change Pi.single v (a • x) w =
      algebraMap (FunctionField P)
        (w.adicCompletion (FunctionField P)) a * Pi.single v x w
    by_cases hwv : w = v
    · subst w
      simp only [Pi.single_eq_same, Algebra.smul_def]
    · simp only [Pi.single_eq_of_ne hwv, mul_zero]

/-! ## Arbitrary-place cyclic-algebra projection and support -/

/-- The Cartwright--Steger cyclic algebra after scalar extension to one
arithmetic adic completion. -/
noncomputable abbrev ArithmeticAdicCyclicAlgebra
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  TensorProduct (FunctionField P)
    (v.adicCompletion (FunctionField P)) (CyclicAlgebra P r)

/-- Project the finite-adelic cyclic algebra to one arbitrary arithmetic
finite place. -/
noncomputable def arithmeticFiniteAdeleCyclicAlgebraAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleCyclicAlgebra P r →ₐ[FunctionField P]
      ArithmeticAdicCyclicAlgebra P r v :=
  Algebra.TensorProduct.map
    (arithmeticFiniteAdeleAtAlgHom P v)
    (AlgHom.id (FunctionField P) (CyclicAlgebra P r))

/-- Insert an arbitrary-place adic cyclic element coefficientwise into the
finite adeles, supported only at that place. -/
noncomputable def arithmeticFiniteAdeleCyclicSupportedAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticAdicCyclicAlgebra P r v →ₗ[FunctionField P]
      ArithmeticFiniteAdeleCyclicAlgebra P r :=
  TensorProduct.map
    (arithmeticFiniteAdeleSupportedAtPlaceLinearMap P v)
    LinearMap.id

@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_tmul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (a : ArithmeticFiniteAdeleRing P) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleAt P v a) x := by
  simp [arithmeticFiniteAdeleCyclicAlgebraAtPlace,
    arithmeticFiniteAdeleAtAlgHom]
  rfl

@[simp] theorem arithmeticFiniteAdeleCyclicSupportedAtPlace_tmul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (a : v.adicCompletion (FunctionField P)) (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v
        (TensorProduct.tmul (FunctionField P) a x) =
      TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtPlace P v a) x := by
  simp [arithmeticFiniteAdeleCyclicSupportedAtPlace,
    arithmeticFiniteAdeleSupportedAtPlaceLinearMap]
  rfl

/-- Coefficientwise support is a right inverse to projection at the same
arithmetic finite place. -/
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtPlace_tmul,
        arithmeticFiniteAdeleCyclicAlgebraAtPlace_tmul,
        arithmeticFiniteAdeleAt_supportedAtPlace]

/-- The construction-owned cyclic basis after extension to an arbitrary
arithmetic adic completion. -/
noncomputable def arithmeticAdicCyclicBasis
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    Module.Basis (Fin r.matrixRank × Fin r.matrixRank)
      (v.adicCompletion (FunctionField P))
      (ArithmeticAdicCyclicAlgebra P r v) :=
  (functionFieldCyclicBasis P r).baseChange
    (v.adicCompletion (FunctionField P))

/-- The integral cyclic lattice at one arbitrary arithmetic finite place,
expressed in the same cyclic basis as the global order. -/
noncomputable def ArithmeticAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    Set (ArithmeticAdicCyclicAlgebra P r v) :=
  {x | ∀ p, (arithmeticAdicCyclicBasis P r v).equivFun x p ∈
    v.adicCompletionIntegers (FunctionField P)}

/-- Cyclic coordinates commute with diagonal scalar extension to an
arbitrary arithmetic adic completion. -/
theorem arithmeticAdicCyclicBasis_equivFun_diagonal
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticAdicCyclicBasis P r v).equivFun
        (TensorProduct.tmul (FunctionField P) 1 x) p =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P))
          ((functionFieldCyclicBasis P r).equivFun x p) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    arithmeticAdicCyclicBasis, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.smul_def, mul_one]

/-- Every element of the actual arithmetic cyclic order is integral at
every arithmetic finite place. -/
theorem arithmeticAdicCyclic_diagonal_mem_integralLattice
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r) (hx : x ∈ arithmeticCyclicSpan P r) :
    TensorProduct.tmul (FunctionField P) 1 x ∈
      ArithmeticAdicCyclicIntegralLattice P r v := by
  intro p
  obtain ⟨a, ha⟩ :=
    exists_arithmetic_coordinate_of_mem_arithmeticCyclicSpan P r x hx p
  rw [arithmeticAdicCyclicBasis_equivFun_diagonal, ← ha]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem
    (ArithmeticRing P) (FunctionField P) v a

theorem one_mem_arithmeticAdicCyclicIntegralLattice
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    (1 : ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v := by
  exact arithmeticAdicCyclic_diagonal_mem_integralLattice
    P r v 1 (one_mem_arithmeticCyclicSpan P r)

/-- One-place cyclic support is the sum of the supported scalar cyclic
coordinates in the common construction-owned basis. -/
theorem arithmeticFiniteAdeleCyclicSupportedAtPlace_eq_sum
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x =
      ∑ p, TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtPlace P v
          ((arithmeticAdicCyclicBasis P r v).equivFun x p))
        (functionFieldCyclicBasis P r p) := by
  conv_lhs => rw [← (arithmeticAdicCyclicBasis P r v).sum_equivFun x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hterm : (arithmeticAdicCyclicBasis P r v).equivFun x p •
      arithmeticAdicCyclicBasis P r v p =
      TensorProduct.tmul (FunctionField P)
        ((arithmeticAdicCyclicBasis P r v).equivFun x p)
        (functionFieldCyclicBasis P r p) := by
    simp [arithmeticAdicCyclicBasis, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
  rw [hterm, arithmeticFiniteAdeleCyclicSupportedAtPlace_tmul]

private theorem arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis_atPlace
    (P : BasePrime) (r : Rank)
    (a : ArithmeticFiniteAdeleRing P)
    (q p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).repr
        (TensorProduct.tmul (FunctionField P) a
          (functionFieldCyclicBasis P r q)) p =
      if q = p then a else 0 := by
  rw [arithmeticFiniteAdeleCyclicBasis,
    Module.Basis.baseChange_repr_tmul]
  rw [(functionFieldCyclicBasis P r).repr_self]
  by_cases h : q = p <;> simp [h]

/-- Cyclic coordinates commute with support at an arbitrary arithmetic
finite place. -/
theorem arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticFiniteAdeleCyclicBasis P r).equivFun
        (arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) p =
      arithmeticFiniteAdeleSupportedAtPlace P v
        ((arithmeticAdicCyclicBasis P r v).equivFun x p) := by
  rw [Module.Basis.equivFun_apply,
    arithmeticFiniteAdeleCyclicSupportedAtPlace_eq_sum]
  have hsum := map_sum
    (arithmeticFiniteAdeleCyclicBasis P r).repr
    (fun q => TensorProduct.tmul (FunctionField P)
      (arithmeticFiniteAdeleSupportedAtPlace P v
        ((arithmeticAdicCyclicBasis P r v).equivFun x q))
      (functionFieldCyclicBasis P r q)) Finset.univ
  rw [hsum]
  change Finsupp.applyAddHom p
      (∑ q, (arithmeticFiniteAdeleCyclicBasis P r).repr
        (TensorProduct.tmul (FunctionField P)
          (arithmeticFiniteAdeleSupportedAtPlace P v
            ((arithmeticAdicCyclicBasis P r v).equivFun x q))
          (functionFieldCyclicBasis P r q))) = _
  rw [map_sum, Finset.sum_eq_single p]
  · exact arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis_atPlace
      P r _ p p |>.trans (by simp)
  · intro q _ hqp
    change ((arithmeticFiniteAdeleCyclicBasis P r).repr
      (TensorProduct.tmul (FunctionField P)
        (arithmeticFiniteAdeleSupportedAtPlace P v
          ((arithmeticAdicCyclicBasis P r v).equivFun x q))
        (functionFieldCyclicBasis P r q))) p = 0
    rw [arithmeticFiniteAdeleCyclicBasis_repr_tmul_basis_atPlace]
    simp [hqp]
  · simp

/-- One-place cyclic support is globally integral exactly when every local
cyclic coordinate is adic integral. -/
theorem arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x ∈
        ArithmeticFiniteAdeleCyclicIntegralLattice P r ↔
      x ∈ ArithmeticAdicCyclicIntegralLattice P r v := by
  simp only [ArithmeticFiniteAdeleCyclicIntegralLattice,
    ArithmeticAdicCyclicIntegralLattice, Set.mem_setOf_eq]
  simp_rw [arithmeticFiniteAdeleCyclicBasis_equivFun_supportedAtPlace,
    arithmeticFiniteAdeleSupportedAtPlace_mem_integral_iff]

/-- Projection of a globally diagonal cyclic point is its usual scalar
extension to the chosen adic completion. -/
@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_diagonal
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (cyclicAlgebraToArithmeticFiniteAdeles P r x) =
      TensorProduct.tmul (FunctionField P) 1 x := by
  simp [cyclicAlgebraToArithmeticFiniteAdeles_apply]

/-- Construction-owned cyclic coordinates commute with projection from the
finite adeles to any arithmetic adic completion. -/
theorem arithmeticAdicCyclicBasis_equivFun_atPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticAdicCyclicBasis P r v).equivFun
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x) p =
      arithmeticFiniteAdeleAt P v
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      have hleft := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          v.adicCompletion (FunctionField P) => f p)
        ((arithmeticAdicCyclicBasis P r v).equivFun.map_zero)
      have hright := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          ArithmeticFiniteAdeleRing P => f p)
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_zero)
      change (arithmeticAdicCyclicBasis P r v).equivFun 0 p = 0 at hleft
      change (arithmeticFiniteAdeleCyclicBasis P r).equivFun 0 p = 0 at hright
      rw [hleft, hright, map_zero]
  | add x y hx hy =>
      rw [map_add]
      have hleft := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          v.adicCompletion (FunctionField P) => f p)
        ((arithmeticAdicCyclicBasis P r v).equivFun.map_add
          (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x)
          (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v y))
      have hright := congrArg
        (fun f : (Fin r.matrixRank × Fin r.matrixRank) →
          ArithmeticFiniteAdeleRing P => f p)
        ((arithmeticFiniteAdeleCyclicBasis P r).equivFun.map_add x y)
      change (arithmeticAdicCyclicBasis P r v).equivFun
          (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x +
            arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v y) p =
        (arithmeticAdicCyclicBasis P r v).equivFun
            (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x) p +
          (arithmeticAdicCyclicBasis P r v).equivFun
            (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v y) p
        at hleft
      change (arithmeticFiniteAdeleCyclicBasis P r).equivFun (x + y) p =
        (arithmeticFiniteAdeleCyclicBasis P r).equivFun x p +
          (arithmeticFiniteAdeleCyclicBasis P r).equivFun y p at hright
      rw [hleft, hright, map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicAlgebraAtPlace_tmul]
      simp [Module.Basis.equivFun_apply, arithmeticAdicCyclicBasis,
        arithmeticFiniteAdeleCyclicBasis,
        Module.Basis.baseChange_repr_tmul]
      exact ((arithmeticFiniteAdeleAtAlgHom P v).toLinearMap.map_smul _ _).symm

/-- A place belongs to the nonintegral support of an adelic cyclic element
exactly when its projected local cyclic element is outside the local
integral lattice. -/
theorem mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticFiniteAdeleCyclicAlgebra P r) :
    v ∈ arithmeticFiniteAdeleCyclicNonintegralPlaces P r x ↔
      arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x ∉
        ArithmeticAdicCyclicIntegralLattice P r v := by
  constructor
  · rintro ⟨p, hp⟩ hlocal
    apply hp
    change arithmeticFiniteAdeleAt P v
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) ∈
        v.adicCompletionIntegers (FunctionField P)
    rw [← arithmeticAdicCyclicBasis_equivFun_atPlace P r v x p]
    exact hlocal p
  · intro hlocal
    change ¬ ∀ p, (arithmeticAdicCyclicBasis P r v).equivFun
      (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v x) p ∈
        v.adicCompletionIntegers (FunctionField P) at hlocal
    push Not at hlocal
    obtain ⟨p, hp⟩ := hlocal
    refine ⟨p, ?_⟩
    change arithmeticFiniteAdeleAt P v
      ((arithmeticFiniteAdeleCyclicBasis P r).equivFun x p) ∉
        v.adicCompletionIntegers (FunctionField P)
    rw [← arithmeticAdicCyclicBasis_equivFun_atPlace P r v x p]
    exact hp

/-- A cyclic element supported at `v` projects to zero at every distinct
arithmetic finite place. -/
theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w
        (arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
      rw [arithmeticFiniteAdeleCyclicSupportedAtPlace_tmul,
        arithmeticFiniteAdeleCyclicAlgebraAtPlace_tmul,
        arithmeticFiniteAdeleAt_supportedAtPlace_of_ne P v w hwv]
      simp

/-- Arbitrary-place cyclic support preserves multiplication.  It remains
nonunital, with image unit equal to the corresponding place idempotent. -/
theorem arithmeticFiniteAdeleCyclicSupportedAtPlace_mul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x y : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v (x * y) =
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x *
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
  | add x z hx hz => simp [add_mul, map_add, hx, hz]
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [arithmeticFiniteAdeleCyclicSupportedAtPlace]
      | add y z hy hz => simp [mul_add, map_add, hy, hz]
      | tmul b y =>
          simp [Algebra.TensorProduct.tmul_mul_tmul,
            show arithmeticFiniteAdeleSupportedAtPlace P v (a * b) =
                arithmeticFiniteAdeleSupportedAtPlace P v a *
                  arithmeticFiniteAdeleSupportedAtPlace P v b from
              map_mul
                (arithmeticFiniteAdeleSupportedAtPlaceNonUnitalRingHom P v)
                a b]

/-- The finite-adelic cyclic idempotent that is one at `v` and zero at every
other arithmetic finite place. -/
noncomputable def arithmeticFiniteAdeleCyclicPlaceIdempotent
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  arithmeticFiniteAdeleCyclicSupportedAtPlace P r v 1

theorem arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_self
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    arithmeticFiniteAdeleCyclicPlaceIdempotent P r v *
        arithmeticFiniteAdeleCyclicPlaceIdempotent P r v =
      arithmeticFiniteAdeleCyclicPlaceIdempotent P r v := by
  rw [arithmeticFiniteAdeleCyclicPlaceIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtPlace_mul]
  simp

theorem arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_supported
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicPlaceIdempotent P r v *
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x =
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x := by
  rw [arithmeticFiniteAdeleCyclicPlaceIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtPlace_mul]
  simp

theorem arithmeticFiniteAdeleCyclicSupported_mul_placeIdempotent
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x *
        arithmeticFiniteAdeleCyclicPlaceIdempotent P r v =
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x := by
  rw [arithmeticFiniteAdeleCyclicPlaceIdempotent,
    ← arithmeticFiniteAdeleCyclicSupportedAtPlace_mul]
  simp

/-- Replace the `v`-coordinate of the finite-adelic cyclic unit by `x` and
leave the identity at every other arithmetic finite place. -/
noncomputable def arithmeticFiniteAdeleCyclicPatchAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    ArithmeticFiniteAdeleCyclicAlgebra P r :=
  1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
    arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x

/-- Patching an integral adic cyclic element at one place and the identity
elsewhere preserves the all-place finite-adelic integral lattice. -/
theorem arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v)
    (hx : x ∈ ArithmeticAdicCyclicIntegralLattice P r v) :
    arithmeticFiniteAdeleCyclicPatchAtPlace P r v x ∈
      ArithmeticFiniteAdeleCyclicIntegralLattice P r := by
  apply ArithmeticFiniteAdeleCyclicIntegralLattice.add_mem P r
  · apply ArithmeticFiniteAdeleCyclicIntegralLattice.sub_mem P r
    · exact one_mem_arithmeticFiniteAdeleCyclicIntegralLattice P r
    · exact
        (arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
          P r v 1).mpr
            (one_mem_arithmeticAdicCyclicIntegralLattice P r v)
  · exact
      (arithmeticFiniteAdeleCyclicSupportedAtPlace_mem_integral_iff
        P r v x).mpr hx

theorem arithmeticFiniteAdeleCyclicPatchAtPlace_mul
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x y : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicPatchAtPlace P r v x *
        arithmeticFiniteAdeleCyclicPatchAtPlace P r v y =
      arithmeticFiniteAdeleCyclicPatchAtPlace P r v (x * y) := by
  change
    (1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v x) *
      (1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
        arithmeticFiniteAdeleCyclicSupportedAtPlace P r v y) =
    1 - arithmeticFiniteAdeleCyclicPlaceIdempotent P r v +
      arithmeticFiniteAdeleCyclicSupportedAtPlace P r v (x * y)
  noncomm_ring
    [arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_self P r v,
      arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_supported P r v x,
      arithmeticFiniteAdeleCyclicPlaceIdempotent_mul_supported P r v y,
      arithmeticFiniteAdeleCyclicSupported_mul_placeIdempotent P r v x,
      arithmeticFiniteAdeleCyclicSupported_mul_placeIdempotent P r v y,
      arithmeticFiniteAdeleCyclicSupportedAtPlace_mul P r v x y]

@[simp] theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v
        (arithmeticFiniteAdeleCyclicPatchAtPlace P r v x) = x := by
  simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
    arithmeticFiniteAdeleCyclicPlaceIdempotent]

theorem arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (x : ArithmeticAdicCyclicAlgebra P r v) :
    arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w
        (arithmeticFiniteAdeleCyclicPatchAtPlace P r v x) = 1 := by
  simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
    arithmeticFiniteAdeleCyclicPlaceIdempotent,
    arithmeticFiniteAdeleCyclicAlgebraAtPlace_supported_of_ne
      P r v w hwv]

/-- Patch a unit of the adic cyclic algebra at `v` into a genuine
finite-adelic cyclic-algebra unit that is the identity at every other
arithmetic finite place. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitSupportedAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ where
  val := arithmeticFiniteAdeleCyclicPatchAtPlace P r v u
  inv := arithmeticFiniteAdeleCyclicPatchAtPlace P r v
    ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
      ArithmeticAdicCyclicAlgebra P r v)
  val_inv := by
    rw [arithmeticFiniteAdeleCyclicPatchAtPlace_mul]
    have hu : (u : ArithmeticAdicCyclicAlgebra P r v) *
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v) = 1 := by
      exact congrArg Units.val (mul_inv_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
      arithmeticFiniteAdeleCyclicPlaceIdempotent]
  inv_val := by
    rw [arithmeticFiniteAdeleCyclicPatchAtPlace_mul]
    have hu :
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v) *
          (u : ArithmeticAdicCyclicAlgebra P r v) = 1 := by
      exact congrArg Units.val (inv_mul_cancel u)
    rw [hu]
    simp [arithmeticFiniteAdeleCyclicPatchAtPlace,
      arithmeticFiniteAdeleCyclicPlaceIdempotent]

/-- A one-place patched local unit has empty global denominator support
when both the local unit and its inverse have integral cyclic coordinates. -/
theorem arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_denominatorPlaces_eq_empty
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ)
    (hu : (u : ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v)
    (huInv : ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
        ArithmeticAdicCyclicAlgebra P r v) ∈
      ArithmeticAdicCyclicIntegralLattice P r v) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = ∅ := by
  have hval :=
    (arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty
      P r _).mp
      (arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral P r v u hu)
  have hinv :=
    (arithmeticFiniteAdeleCyclic_mem_integralLattice_iff_denominatorPlaces_empty
      P r _).mp
      (arithmeticFiniteAdeleCyclicPatchAtPlace_mem_integral P r v
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v) huInv)
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces]
  change arithmeticFiniteAdeleCyclicNonintegralPlaces P r
      (arithmeticFiniteAdeleCyclicPatchAtPlace P r v u) ∪
    arithmeticFiniteAdeleCyclicNonintegralPlaces P r
      (arithmeticFiniteAdeleCyclicPatchAtPlace P r v
        ((u⁻¹ : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
          ArithmeticAdicCyclicAlgebra P r v)) = ∅
  rw [hval, hinv, Set.empty_union]

@[simp] theorem arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = u := by
  apply Units.ext
  exact arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch P r v u

theorem arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (u : (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v u) = 1 := by
  apply Units.ext
  exact arithmeticFiniteAdeleCyclicAlgebraAtPlace_patch_of_ne P r v w hwv u

/-! ## Exact removal of one finite-adelic denominator coordinate -/

/-- Projection of finite-adelic cyclic units to the local cyclic units at an
arbitrary arithmetic finite place. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →*
      (ArithmeticAdicCyclicAlgebra P r v)ˣ :=
  Units.map
    (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v).toRingHom.toMonoidHom

/-- Denominator membership can be read entirely from the projected local
unit and its inverse. -/
theorem mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u ↔
      (arithmeticFiniteAdeleCyclicUnitAtPlace P r v u :
          ArithmeticAdicCyclicAlgebra P r v) ∉
          ArithmeticAdicCyclicIntegralLattice P r v ∨
        (((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹ :
          (ArithmeticAdicCyclicAlgebra P r v)ˣ) :
            ArithmeticAdicCyclicAlgebra P r v) ∉
          ArithmeticAdicCyclicIntegralLattice P r v := by
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces, Set.mem_union,
    mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff,
    mem_arithmeticFiniteAdeleCyclicNonintegralPlaces_iff]
  rfl

/-- Multiply by the one-place inverse of the `v`-projection.  This is the
canonical finite-adelic correction that makes the `v`-coordinate exactly
the identity and leaves every other coordinate unchanged. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitClearAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ :=
  arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v
      ((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹) * u

@[simp] theorem arithmeticFiniteAdeleCyclicUnitAtPlace_clear
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r v
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) = 1 := by
  rw [arithmeticFiniteAdeleCyclicUnitClearAtPlace, map_mul]
  change
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r v).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v
          ((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹)) *
      arithmeticFiniteAdeleCyclicUnitAtPlace P r v u = 1
  rw [arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection]
  exact inv_mul_cancel (arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)

theorem arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne
    (P : BasePrime) (r : Rank)
    (v w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hwv : w ≠ v)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by
  rw [arithmeticFiniteAdeleCyclicUnitClearAtPlace, map_mul]
  change
    Units.map
        (arithmeticFiniteAdeleCyclicAlgebraAtPlace P r w).toRingHom.toMonoidHom
        (arithmeticFiniteAdeleCyclicUnitSupportedAtPlace P r v
          ((arithmeticFiniteAdeleCyclicUnitAtPlace P r v u)⁻¹)) *
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u = _
  rw [arithmeticFiniteAdeleCyclicUnitSupportedAtPlace_projection_of_ne
    P r v w hwv, one_mul]

/-- Exact support effect of one-place correction: it deletes precisely the
chosen place and changes no other denominator membership. -/
theorem arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlace
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u) =
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u \ {v} := by
  ext w
  by_cases hwv : w = v
  · subst w
    rw [mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff,
      arithmeticFiniteAdeleCyclicUnitAtPlace_clear]
    simp [one_mem_arithmeticAdicCyclicIntegralLattice]
  · rw [Set.mem_diff, Set.mem_singleton_iff, and_iff_left hwv,
      mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff,
      mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_iff,
      arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne P r v w hwv]

/-- Sequentially clear a concrete list of arithmetic finite places.  Lists
avoid imposing an artificial commutativity requirement on the correction
operation; the support theorem below proves that the result is independent
of repetitions at the level needed here. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitClearAtPlaceList
    (P : BasePrime) (r : Rank) :
    List (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) →
      (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ →
        (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ
  | [], u => u
  | v :: places, u =>
      arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r places
        (arithmeticFiniteAdeleCyclicUnitClearAtPlace P r v u)

/-- Clearing a list removes exactly the set of places occurring in that
list from the denominator support. -/
theorem arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlaceList
    (P : BasePrime) (r : Rank)
    (places : List
      (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)))
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r places u) =
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u \
        (places.toFinset : Set
          (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))) := by
  induction places generalizing u with
  | nil => simp [arithmeticFiniteAdeleCyclicUnitClearAtPlaceList]
  | cons v places ih =>
      rw [arithmeticFiniteAdeleCyclicUnitClearAtPlaceList, ih,
        arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlace]
      ext w
      simp [Set.mem_diff, and_assoc, and_left_comm, and_comm]

/-- Clearing places not containing `w` preserves the `w`-projection
exactly. -/
theorem arithmeticFiniteAdeleCyclicUnitAtPlace_clearAtPlaceList_of_not_mem
    (P : BasePrime) (r : Rank)
    (places : List
      (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)))
    (w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hw : w ∉ places)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r places u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by
  induction places generalizing u with
  | nil => rfl
  | cons v places ih =>
      have hwv : w ≠ v := by
        intro h
        apply hw
        simp [h]
      have hwt : w ∉ places := by
        intro h
        exact hw (by simp [h])
      rw [arithmeticFiniteAdeleCyclicUnitClearAtPlaceList,
        ih hwt,
        arithmeticFiniteAdeleCyclicUnitAtPlace_clear_of_ne P r v w hwv]

/-- The finite list of all denominator places of a finite-adelic cyclic
unit. -/
noncomputable def arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    List (IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :=
  (arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_finite P r u).toFinset.toList

@[simp] theorem mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P)) :
    v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList P r u ↔
      v ∈ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u := by
  simp [arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList]

/-- Clearing the complete finite denominator list produces an adelic unit
with no denominator places. -/
theorem arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAll_eq_empty
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ) :
    arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r
          (arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList P r u) u) =
      ∅ := by
  rw [arithmeticFiniteAdeleCyclicUnitDenominatorPlaces_clearAtPlaceList]
  ext v
  simp [mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList]

/-- Complete denominator clearing preserves every coordinate that was not
in the original denominator support. -/
theorem arithmeticFiniteAdeleCyclicUnitAtPlace_clearAll_of_not_mem
    (P : BasePrime) (r : Rank)
    (u : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (w : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (hw : w ∉ arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u) :
    arithmeticFiniteAdeleCyclicUnitAtPlace P r w
        (arithmeticFiniteAdeleCyclicUnitClearAtPlaceList P r
          (arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList P r u) u) =
      arithmeticFiniteAdeleCyclicUnitAtPlace P r w u := by
  apply arithmeticFiniteAdeleCyclicUnitAtPlace_clearAtPlaceList_of_not_mem
  simpa [mem_arithmeticFiniteAdeleCyclicUnitDenominatorPlaceList]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
