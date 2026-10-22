import Mathlib

namespace QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator

open scoped BigOperators Polynomial

variable {k F ι : Type*}

/-- Finitely supported `K`-coordinate families whose entries come from the
direct polynomial chart. -/
def polynomialCoordinateFamily (k : Type*) [Field k] (ι : Type*) :
    Submodule k[X] (ι →₀ RatFunc k) where
  carrier := {c | ∀ j, c j ∈ Set.range (algebraMap k[X] (RatFunc k))}
  zero_mem' := by
    intro j
    exact ⟨0, by simp⟩
  add_mem' := by
    intro c d hc hd j
    rcases hc j with ⟨r, hr⟩
    rcases hd j with ⟨s, hs⟩
    refine ⟨r + s, ?_⟩
    simpa [Finsupp.add_apply, hr, hs]
  smul_mem' := by
    intro r c hc j
    rcases hc j with ⟨s, hs⟩
    refine ⟨r * s, ?_⟩
    simpa [Finsupp.smul_apply, Algebra.smul_def, hs] using
      (algebraMap k[X] (RatFunc k)).map_mul r s

variable [Field k] [Field F]
variable [Algebra (RatFunc k) F] [Algebra (Polynomial k) F]
  [IsScalarTower (Polynomial k) (RatFunc k) F]

/-- The direct polynomial-coordinate submodule selected by a genuine
`K`-basis. -/
noncomputable def directChartSubmodule (b : Module.Basis ι (RatFunc k) F) :
    Submodule (Polynomial k) F :=
  (polynomialCoordinateFamily k ι).comap
    (b.repr.restrictScalars (Polynomial k)).toLinearMap

/-- The pullback of the direct chart after multiplying by a polynomial. -/
noncomputable def scaledDirectChartSubmodule (b : Module.Basis ι (RatFunc k) F)
    (a : Polynomial k) :
    Submodule (Polynomial k) F :=
  (directChartSubmodule b).comap (LinearMap.lsmul (Polynomial k) F a)

/-- Coordinate linearity for the actual tower `R → K → F`. -/
theorem repr_smul_polynomial (b : Module.Basis ι (RatFunc k) F) (a : Polynomial k) (x : F) (j : ι) :
    b.repr (a • x) j = algebraMap (Polynomial k) (RatFunc k) a * b.repr x j := by
  simpa [Finsupp.smul_apply, Algebra.smul_def] using
    congrArg (fun c : ι →₀ RatFunc k => c j)
      ((b.repr.restrictScalars (Polynomial k)).map_smul a x)

/-- A finite polynomial submodule has one actual nonzero denominator which
puts every coordinate of every scaled element into the direct polynomial
subring of `k(X)`. -/
theorem exists_common_denominator_direct_chart
    [Fintype ι] (b : Module.Basis ι (RatFunc k) F) (L : Submodule (Polynomial k) F)
    [Module.Finite (Polynomial k) L] :
    ∃ a : Polynomial k, a ≠ 0 ∧ ∀ x : L, ∀ j : ι,
      b.repr (a • (x : F)) j ∈ Set.range (algebraMap (Polynomial k) (RatFunc k)) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := Polynomial k) (M := L)
  choose p q hq hqrep using fun i : Fin n => fun j : ι =>
    IsFractionRing.div_surjective (Polynomial k) (b.repr ((g i : L) : F) j)
  let a : Polynomial k := ∏ i : Fin n, ∏ j : ι, q i j
  have ha : a ≠ 0 := by
    dsimp [a]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact nonZeroDivisors.ne_zero (hq i j)
  let P : Submodule (Polynomial k) L :=
    (scaledDirectChartSubmodule b a).comap L.subtype
  have hgenerator : ∀ i : Fin n, g i ∈ P := by
    intro i
    change ∀ j : ι, b.repr (a • ((g i : L) : F)) j ∈
      Set.range (algebraMap (Polynomial k) (RatFunc k))
    intro j
    have hqne : algebraMap (Polynomial k) (RatFunc k) (q i j) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hq i j)
    have hclear : algebraMap (Polynomial k) (RatFunc k) (q i j) * b.repr ((g i : L) : F) j =
        algebraMap (Polynomial k) (RatFunc k) (p i j) := by
      simpa [mul_comm] using (div_eq_iff_mul_eq hqne).mp (hqrep i j)
    have hdiv : q i j ∣ a := by
      dsimp [a]
      exact
        (Finset.dvd_prod_of_mem (fun j : ι => q i j) (Finset.mem_univ j)).trans
          (Finset.dvd_prod_of_mem (fun i : Fin n => ∏ j : ι, q i j)
            (Finset.mem_univ i))
    rcases hdiv with ⟨c, hc⟩
    refine ⟨c * p i j, ?_⟩
    symm
    calc
      b.repr (a • ((g i : L) : F)) j =
          algebraMap (Polynomial k) (RatFunc k) a * b.repr ((g i : L) : F) j :=
        repr_smul_polynomial b a ((g i : L) : F) j
      _ = (algebraMap (Polynomial k) (RatFunc k) (q i j) *
          algebraMap (Polynomial k) (RatFunc k) c) *
          b.repr ((g i : L) : F) j := by
        rw [hc, map_mul]
      _ = algebraMap (Polynomial k) (RatFunc k) c *
          (algebraMap (Polynomial k) (RatFunc k) (q i j) * b.repr ((g i : L) : F) j) := by
        ac_rfl
      _ = algebraMap (Polynomial k) (RatFunc k) c *
          algebraMap (Polynomial k) (RatFunc k) (p i j) := by rw [hclear]
      _ = algebraMap (Polynomial k) (RatFunc k) (c * p i j) := by rw [map_mul]
  have htop : (⊤ : Submodule (Polynomial k) L) ≤ P := by
    rw [← hg]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    exact hgenerator i
  refine ⟨a, ha, ?_⟩
  intro x j
  have hx : x ∈ P := htop (by simp)
  change ∀ j : ι, b.repr (a • (x : F)) j ∈
    Set.range (algebraMap (Polynomial k) (RatFunc k)) at hx
  exact hx j

end QEC.Coding.AlgebraicGeometry.DirectChartCommonDenominator
