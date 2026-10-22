import QEC.Coding.Core.Definitions

/-!
# Weight descent for relative CSS distance

The finite descent step in [LZ22, proof of Theorem thm:123].
The geometric weight-reducing check required by Theorem thm:main is an explicit
premise here and remains to be constructed. The geometric premise is not a proof of LZ22 goodness.
-/

noncomputable section

namespace QEC.Coding

open Classical

universe u v

variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]

/-- Strict weight descent by trivial words makes every ambient word below the
threshold trivial. The induction preserves ambient membership and terminates
at the actual zero word, rather than assuming a distance conclusion. -/
theorem mem_trivial_of_weight_lt_of_add_weight_descent
    (ambient trivial : LinearCode F ι)
    (hsub : trivial.carrier ≤ ambient.carrier) (threshold : Nat)
    (hreduce : ∀ x : Word F ι, x ∈ ambient.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ trivial.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (x : Word F ι) (hx : x ∈ ambient.carrier)
    (hweight : HammingWeight x < threshold) : x ∈ trivial.carrier := by
  have descend : ∀ n : Nat, ∀ z : Word F ι,
      HammingWeight z = n → z ∈ ambient.carrier →
      HammingWeight z < threshold → z ∈ trivial.carrier := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hn hz hlt
      by_cases hzero : z = 0
      · subst z
        exact trivial.carrier.zero_mem
      obtain ⟨y, hy, hdecrease⟩ := hreduce z hz hzero hlt
      have hsmall : HammingWeight (z + y) < n := by
        simpa only [hn] using hdecrease
      have hsum : z + y ∈ trivial.carrier :=
        ih (HammingWeight (z + y)) hsmall (z + y) rfl
          (ambient.carrier.add_mem hz (hsub hy)) (hdecrease.trans hlt)
      have hdiff := trivial.carrier.sub_mem hsum hy
      simpa only [add_sub_cancel_right] using hdiff
  exact descend (HammingWeight x) x rfl hx hweight

/-- Consequently every nontrivial logical representative has weight at least
the threshold. No nonempty logical sector or attained minimum is assumed. -/
theorem logical_weight_ge_of_add_weight_descent
    (ambient trivial : LinearCode F ι)
    (hsub : trivial.carrier ≤ ambient.carrier) (threshold : Nat)
    (hreduce : ∀ x : Word F ι, x ∈ ambient.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ trivial.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (x : Word F ι) (hx : x ∈ ambient.carrier)
    (hlogical : x ∉ trivial.carrier) : threshold ≤ HammingWeight x := by
  by_contra hnot
  exact hlogical (mem_trivial_of_weight_lt_of_add_weight_descent
    ambient trivial hsub threshold hreduce x hx (Nat.lt_of_not_ge hnot))

/-- The same reduction in both actual CSS sectors bounds any attained CSS
minimum. This is only the final descent bridge: the two geometric reduction
premises must still be proved from expansion and local-code robustness. -/
theorem algebraicCSSMinimumDistance_ge_of_add_weight_descent
    (xCode zCode : LinearCode F ι)
    (hX : xCode.carrier ≤ zCode.dual.carrier)
    (hZ : zCode.carrier ≤ xCode.dual.carrier) (threshold : Nat)
    (hreduceX : ∀ x : Word F ι, x ∈ zCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ xCode.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (hreduceZ : ∀ x : Word F ι, x ∈ xCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ zCode.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    {distance : Nat}
    (hmin : AlgebraicCSSMinimumDistance xCode zCode distance) :
    threshold ≤ distance := by
  obtain ⟨x, hsector, hweight, _hleast⟩ := hmin
  rw [← hweight]
  rcases hsector with hsector | hsector
  · exact logical_weight_ge_of_add_weight_descent
      zCode.dual xCode hX threshold hreduceX x hsector.1 hsector.2
  · exact logical_weight_ge_of_add_weight_descent
      xCode.dual zCode hZ threshold hreduceZ x hsector.1 hsector.2

end QEC.Coding
