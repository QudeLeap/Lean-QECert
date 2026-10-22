import QEC.Coding.ExpanderCodes.CayleySpectrum
import QEC.Coding.ExpanderCodes.LPSFamily
import QEC.Coding.ExpanderCodes.LPSQuaternionReduction

/-!
# The LPS adjacency operator as a quaternion-shell correspondence

This file identifies the labelled LPS Cayley adjacency with translation by
the norm-`p` quaternion shell after multiplicative projective reduction.  It
is the finite algebraic side of the Hecke correspondence.  The remaining
Ramanujan input is the analytic/arithmetic bound on this correspondence,
not an ambiguity in how it acts on the concrete finite quotient.
-/

open scoped MatrixGroups

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- The normalized norm-`p` shell, regarded inside the multiplicative
submonoid on which reduction modulo the LPS residue prime is invertible. -/
noncomputable def lpsQuaternionShellAwayLabel
    (a : LPSResiduePrime p) :
    LPSGeneratorIndex p → lpsQuaternionAwaySubmonoid a.q :=
  fun t => lpsQuaternionAwayElement a t.1
    (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.2)

/-- The projective norm-`p` Hecke label obtained by multiplicative
quaternion reduction. -/
noncomputable def lpsPGLHeckeLabel
    (a : LPSResiduePrime p) :
    LPSGeneratorIndex p → PGL(2, ZMod a.q) :=
  fun t => lpsQuaternionAwayPGL a.q (lpsQuaternionShellAwayLabel a t)

/-- The Hecke label agrees exactly with the projectivization of the concrete
`PSL(2,q)` graph label. -/
@[simp] theorem lpsPGLHeckeLabel_eq_toPGL
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) :
    lpsPGLHeckeLabel a t =
      Matrix.ProjectiveSpecialLinearGroup.toPGL
        (lpsQuaternionLabel a t) := by
  rw [lpsPGLHeckeLabel, lpsQuaternionShellAwayLabel,
    lpsQuaternionLabel, toPGL_lpsQuaternionPSL,
    lpsQuaternionPGL_eq_away]

/-- Pullback along `PSL(2,q) → PGL(2,q)` intertwines the concrete LPS
adjacency sum with the norm-`p` quaternion-shell correspondence. -/
theorem cayleyRightTranslationSum_lps_eq_pglHecke
    (a : LPSResiduePrime p)
    (f : PGL(2, ZMod a.q) → ℂ)
    (g : PSL(2, ZMod a.q)) :
    cayleyRightTranslationSum (lpsQuaternionLabel a)
        (fun h => f (Matrix.ProjectiveSpecialLinearGroup.toPGL h)) g =
      cayleyRightTranslationSum (lpsPGLHeckeLabel a) f
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by
  classical
  unfold cayleyRightTranslationSum
  apply Finset.sum_congr rfl
  intro t _ht
  change f (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (g * lpsQuaternionLabel a t)) =
    f (Matrix.ProjectiveSpecialLinearGroup.toPGL g *
      lpsPGLHeckeLabel a t)
  rw [map_mul, ← lpsPGLHeckeLabel_eq_toPGL]

/-- Pointwise weighted adjacency on the concrete LPS Cayley graph is the
pullback of the projective norm-`p` Hecke correspondence. -/
theorem complexWeightedNeighborSum_lps_eq_pglHecke
    (a : LPSResiduePrime p)
    (f : PGL(2, ZMod a.q) → ℂ)
    (g : PSL(2, ZMod a.q)) :
    SmallSetExpansion.complexWeightedNeighborSum
        (rightCayleyGraph (lpsQuaternionLabel a))
        (fun h => f (Matrix.ProjectiveSpecialLinearGroup.toPGL h)) g =
      cayleyRightTranslationSum (lpsPGLHeckeLabel a) f
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g) := by
  rw [complexWeightedNeighborSum_rightCayleyGraph]
  exact cayleyRightTranslationSum_lps_eq_pglHecke a f g

end QEC.Coding.TannerLiftedProduct
