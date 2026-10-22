import QEC.Coding.ExpanderCodes.LPSQuaternionFactorization

/-!
# Exact finite LPS trace formula

The quaternion normal form identifies the coefficient of the trace theta
series with twice the identity coefficient of the finite LPS Hecke element.
Combining that count with the right-regular trace formula gives the exact
finite trace identity, including every normalization factor.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- The `n`-th Hecke polynomial evaluated on the centered finite LPS
adjacency operator. -/
noncomputable def lpsCenteredHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    Module.End ℂ (PSL(2, ZMod a.q) → ℂ) :=
  (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
    (algebraMap ℂ (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
    (cayleyRightRegularRepresentation.asAlgebraHom
      (cayleyCenteredGeneratorSum (lpsQuaternionLabel a)))

/-- Euclidean-space presentation of the centered LPS Hecke operator. -/
noncomputable def lpsCenteredEuclideanHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    Module.End ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q)) :=
  (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
    (algebraMap ℂ
      (Module.End ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (SmallSetExpansion.centeredAdjacencyEuclidean
      (rightCayleyGraph (lpsQuaternionLabel a))
      (Fintype.card (LPSGeneratorIndex p)))

/-- The centered adjacency underlying the Euclidean LPS Hecke operators is
self-adjoint. -/
theorem lpsCenteredAdjacencyEuclidean_isSymmetric
    (a : LPSResiduePrime p) :
    (SmallSetExpansion.centeredAdjacencyEuclidean
      (rightCayleyGraph (lpsQuaternionLabel a))
      (Fintype.card (LPSGeneratorIndex p))).IsSymmetric :=
  SmallSetExpansion.centeredAdjacencyEuclidean_isSymmetric
    (rightCayleyGraph (lpsQuaternionLabel a))
    (Fintype.card (LPSGeneratorIndex p))
    (rightCayleyGraph_lpsQuaternionLabel_isSymmetric a)

/-- The ordinary-function and Euclidean presentations of the centered
Hecke operator are conjugate under the canonical `L²` identification. -/
theorem lpsCenteredEuclideanHeckeOperator_eq_conj
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredEuclideanHeckeOperator a n =
      (cayleyEuclideanLinearEquiv (G := PSL(2, ZMod a.q))).conj
        (lpsCenteredHeckeOperator a n) := by
  rw [lpsCenteredEuclideanHeckeOperator,
    centeredAdjacencyEuclidean_rightCayleyGraph_eq_conj]
  unfold lpsCenteredHeckeOperator
  symm
  change (cayleyEuclideanLinearEquiv
      (G := PSL(2, ZMod a.q))).conjRingEquiv
        ((lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
          (algebraMap ℂ (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
          (cayleyRightRegularRepresentation.asAlgebraHom
            (cayleyCenteredGeneratorSum (lpsQuaternionLabel a)))) = _
  have hAlg :
      (cayleyEuclideanLinearEquiv
          (G := PSL(2, ZMod a.q))).conjRingEquiv.toRingHom.comp
          (algebraMap ℂ
            (Module.End ℂ (PSL(2, ZMod a.q) → ℂ))) =
        algebraMap ℂ
          (Module.End ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))) := by
    ext c f
    rfl
  have h :=
    Polynomial.hom_eval₂
      (p := lpsHeckePolynomial ℂ (p : ℂ) n)
      (algebraMap ℂ
        (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
      (cayleyEuclideanLinearEquiv
        (G := PSL(2, ZMod a.q))).conjRingEquiv.toRingHom
      (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum (lpsQuaternionLabel a)))
  rw [hAlg] at h
  exact h

/-- Polynomial functional calculus splits into the centered LPS operator
plus its one-dimensional constant-mode contribution. -/
theorem lpsFiniteHeckeElement_action_eq_centered_add_constant
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (lpsFiniteHeckeElement a n) =
      lpsCenteredHeckeOperator a n +
        ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) •
            cayleyConstantProjection := by
  let A : Module.End ℂ (PSL(2, ZMod a.q) → ℂ) :=
    cayleyRightRegularRepresentation.asAlgebraHom
      (cayleyGeneratorSum (lpsQuaternionLabel a))
  let C : Module.End ℂ (PSL(2, ZMod a.q) → ℂ) :=
    cayleyRightRegularRepresentation.asAlgebraHom
      (cayleyCenteredGeneratorSum (lpsQuaternionLabel a))
  let P : Module.End ℂ (PSL(2, ZMod a.q) → ℂ) :=
    cayleyConstantProjection
  have hA : A = C + ((p : ℂ) + 1) • P := by
    dsimp [A, C, P]
    rw [cayleyCenteredGeneratorSum_action_eq_sub_projection]
    have hcard : Fintype.card (LPSGeneratorIndex p) = p + 1 := by
      rw [card_lpsGeneratorIndex,
        card_lpsQuaternionShell_eq_prime_add_one
          a.degreePrime a.degreeModFour]
    rw [hcard]
    push_cast
    module
  rw [lpsFiniteHeckeElement_action]
  change (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
      (algebraMap ℂ (Module.End ℂ (PSL(2, ZMod a.q) → ℂ))) A = _
  rw [hA]
  exact lpsHeckePolynomial_eval₂_add_smul_idempotent
    (p : ℂ) ((p : ℂ) + 1) C P
    (by
      exact cayleyCenteredGeneratorSum_action_mul_constantProjection
        (lpsQuaternionLabel a))
    (by
      exact cayleyConstantProjection_mul_centeredGeneratorSum_action
        (lpsQuaternionLabel a))
    cayleyConstantProjection_mul_self n

/-- Exact trace formula: twice the trace of the `n`-th finite LPS Hecke
operator is the group order times the corresponding trace-theta coefficient.
No asymptotic or automorphic input remains in this identity. -/
theorem two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (cayleyRightRegularRepresentation.asAlgebraHom
            (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) := by
  rw [trace_lpsFiniteHeckeElement,
    coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff]
  ring

/-- The scalar by which the `n`-th LPS Hecke operator acts on constant
functions is the geometric sum `1 + p + ... + p^n`. -/
theorem lpsHeckePolynomial_eval_degree_eq_geomSum
    (p n : ℕ) :
    (lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) =
      ∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i := by
  exact lpsHeckePolynomial_eval_add_one_eq_geomSum ℂ (p : ℂ) n

/-- The trace of the centered Hecke operator is the full finite trace with
the single trivial-representation eigenvalue removed. -/
theorem trace_lpsCenteredHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (lpsCenteredHeckeOperator a n) =
      LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (cayleyRightRegularRepresentation.asAlgebraHom
            (lpsFiniteHeckeElement a n)) -
        ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
  have h := congrArg
    (LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ))
    (lpsFiniteHeckeElement_action_eq_centered_add_constant a n)
  simp only [map_add, map_smul, trace_cayleyConstantProjection,
    smul_eq_mul, mul_one] at h
  rw [h]
  ring

/-- The Euclidean and ordinary-function presentations of the centered
Hecke operator have the same trace. -/
theorem trace_lpsCenteredEuclideanHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n) =
      LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (lpsCenteredHeckeOperator a n) := by
  rw [lpsCenteredEuclideanHeckeOperator_eq_conj,
    LinearMap.trace_conj']

/-- Exact centered trace formula.  The only term not supplied by
the theta coefficient is the explicitly removed geometric-sum contribution
of the constant representation. -/
theorem two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
          (lpsCenteredHeckeOperator a n) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
  rw [trace_lpsCenteredHeckeOperator]
  calc
    2 * (LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
            (cayleyRightRegularRepresentation.asAlgebraHom
              (lpsFiniteHeckeElement a n)) -
          ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
            (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0)) =
        2 * LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
            (cayleyRightRegularRepresentation.asAlgebraHom
              (lpsFiniteHeckeElement a n)) -
          2 * ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
            (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by ring
    _ = (Fintype.card PSL(2, ZMod a.q) : ℂ) *
            ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
          2 * ((lpsHeckePolynomial ℂ (p : ℂ) n).eval ((p : ℂ) + 1) -
            (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
      rw [two_mul_trace_lpsFiniteHeckeElement_eq_card_mul_thetaCoeff]
    _ = _ := by rw [lpsHeckePolynomial_eval_degree_eq_geomSum]

/-- Euclidean-space form of the exact centered trace formula. -/
theorem two_mul_trace_lpsCenteredEuclideanHeckeOperator_eq_theta_sub_trivial
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
          (lpsCenteredEuclideanHeckeOperator a n) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℂ) ^ i) -
          (lpsHeckePolynomial ℂ (p : ℂ) n).eval 0) := by
  rw [trace_lpsCenteredEuclideanHeckeOperator,
    two_mul_trace_lpsCenteredHeckeOperator_eq_theta_sub_trivial]

end QEC.Coding.TannerLiftedProduct
