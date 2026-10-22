import QEC.Coding.ExpanderCodes.JacobiThetaSeries

/-!
# The parity reindexing in Jacobi's cube identity

The square of Jacobi's triangular series is indexed by pairs of integers.
This module formalizes the source's partition into equal-parity and
opposite-parity pairs and the two integral linear changes of variables.
-/

namespace QEC.Coding.TannerLiftedProduct

private def jacobiSameParityToFun
    (p : ℤ × ℤ) : {q : ℤ × ℤ // Even (q.1 + q.2)} :=
  ⟨(p.1 + p.2, p.1 - p.2), ⟨p.1, by ring⟩⟩

private noncomputable def jacobiSameParityInvFun
    (p : {q : ℤ × ℤ // Even (q.1 + q.2)}) : ℤ × ℤ :=
  ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)

private theorem jacobiSameParity_left_inv :
    Function.LeftInverse jacobiSameParityInvFun jacobiSameParityToFun := by
  intro p
  change (((p.1 + p.2) + (p.1 - p.2)) / 2,
    ((p.1 + p.2) - (p.1 - p.2)) / 2) = p
  apply Prod.ext <;> dsimp only
  all_goals omega

private theorem jacobiSameParity_right_inv :
    Function.RightInverse jacobiSameParityInvFun jacobiSameParityToFun := by
  intro p
  obtain ⟨s, hs⟩ := p.property
  apply Subtype.ext
  change ((p.1.1 + p.1.2) / 2 + (p.1.1 - p.1.2) / 2,
    (p.1.1 + p.1.2) / 2 - (p.1.1 - p.1.2) / 2) = p.1
  apply Prod.ext <;> dsimp only
  all_goals omega

/-- Equal-parity pairs are parametrized by `(s,t) ↦ (s+t,s-t)`. -/
noncomputable def jacobiSameParityEquiv :
    (ℤ × ℤ) ≃ {p : ℤ × ℤ // Even (p.1 + p.2)} where
  toFun := jacobiSameParityToFun
  invFun := jacobiSameParityInvFun
  left_inv := jacobiSameParity_left_inv
  right_inv := jacobiSameParity_right_inv

private def jacobiOppositeParityToFun
    (p : ℤ × ℤ) : {q : ℤ × ℤ // ¬ Even (q.1 + q.2)} :=
  ⟨(p.1 + p.2, p.2 - p.1 - 1), by
    intro h
    obtain ⟨r, hr⟩ := h
    dsimp only at hr
    omega⟩

private noncomputable def jacobiOppositeParityInvFun
    (p : {q : ℤ × ℤ // ¬ Even (q.1 + q.2)}) : ℤ × ℤ :=
  ((p.1.1 - p.1.2 - 1) / 2, (p.1.1 + p.1.2 + 1) / 2)

private theorem jacobiOppositeParity_left_inv :
    Function.LeftInverse jacobiOppositeParityInvFun
      jacobiOppositeParityToFun := by
  intro p
  change (((p.1 + p.2) - (p.2 - p.1 - 1) - 1) / 2,
    ((p.1 + p.2) + (p.2 - p.1 - 1) + 1) / 2) = p
  apply Prod.ext <;> dsimp only
  all_goals omega

private theorem jacobiOppositeParity_right_inv :
    Function.RightInverse jacobiOppositeParityInvFun
      jacobiOppositeParityToFun := by
  intro p
  obtain ⟨r, hr⟩ := Int.not_even_iff_odd.mp p.property
  apply Subtype.ext
  change ((p.1.1 - p.1.2 - 1) / 2 +
      (p.1.1 + p.1.2 + 1) / 2,
    (p.1.1 + p.1.2 + 1) / 2 -
      (p.1.1 - p.1.2 - 1) / 2 - 1) = p.1
  apply Prod.ext <;> dsimp only
  all_goals omega

/-- Opposite-parity pairs are parametrized by
`(s,t) ↦ (s+t,t-s-1)`. -/
noncomputable def jacobiOppositeParityEquiv :
    (ℤ × ℤ) ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun := jacobiOppositeParityToFun
  invFun := jacobiOppositeParityInvFun
  left_inv := jacobiOppositeParity_left_inv
  right_inv := jacobiOppositeParity_right_inv

/-- Every integer pair occurs in exactly one of the two parity charts. -/
noncomputable def jacobiParityReindex :
    ((ℤ × ℤ) ⊕ (ℤ × ℤ)) ≃ (ℤ × ℤ) :=
  (Equiv.sumCongr jacobiSameParityEquiv jacobiOppositeParityEquiv).trans
    (Equiv.sumCompl fun p : ℤ × ℤ => Even (p.1 + p.2))

@[simp] theorem jacobiParityReindex_inl (s t : ℤ) :
    jacobiParityReindex (Sum.inl (s, t)) = (s + t, s - t) := by
  rfl

@[simp] theorem jacobiParityReindex_inr (s t : ℤ) :
    jacobiParityReindex (Sum.inr (s, t)) = (s + t, t - s - 1) := by
  rfl

/-- Quadratic exponent conversion on the equal-parity chart. -/
theorem jacobi_sameParity_exponent (s t : ℤ) :
    (s + t) ^ 2 + (s + t) + (s - t) ^ 2 + (s - t) =
      2 * (s ^ 2 + s + t ^ 2) := by
  ring

/-- Quadratic exponent conversion on the opposite-parity chart. -/
theorem jacobi_oppositeParity_exponent (s t : ℤ) :
    (s + t) ^ 2 + (s + t) + (t - s - 1) ^ 2 + (t - s - 1) =
      2 * (s ^ 2 + s + t ^ 2) := by
  ring

/-- Weight conversion on the equal-parity chart. -/
theorem jacobi_sameParity_weight (s t : ℤ) :
    (2 * (s + t) + 1) * (2 * (s - t) + 1) =
      (2 * s + 1) ^ 2 - (2 * t) ^ 2 := by
  ring

/-- After the odd parity sign is included, the opposite-parity chart has
the same transformed weight. -/
theorem jacobi_oppositeParity_weight (s t : ℤ) :
    -(2 * (s + t) + 1) * (2 * (t - s - 1) + 1) =
      (2 * s + 1) ^ 2 - (2 * t) ^ 2 := by
  ring

end QEC.Coding.TannerLiftedProduct
