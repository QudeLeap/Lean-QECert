import QEC.Coding.ExpanderCodes.CayleySpectrum
import QEC.Coding.ExpanderCodes.LPSHeckeCorrespondence
import QEC.Coding.ExpanderCodes.LPSHeckePolynomial

/-!
# Finite trace formula for Cayley Hecke polynomials

This module evaluates the LPS Hecke recurrence inside a finite group algebra.
The right regular trace is then exactly the group order times the identity
coefficient.  The remaining LPS arithmetic step is therefore isolated as an
identity-coefficient count.
-/

namespace QEC.Coding.TannerLiftedProduct

universe v

variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

/-- Evaluate the `n`-th LPS Hecke polynomial at a labelled Cayley generator
sum inside the complex group algebra. -/
noncomputable def cayleyHeckeElement
    (label : W → G) (p : ℂ) (n : ℕ) : MonoidAlgebra ℂ G :=
  (lpsHeckePolynomial ℂ p n).eval₂
    (algebraMap ℂ (MonoidAlgebra ℂ G)) (cayleyGeneratorSum label)

@[simp] theorem cayleyHeckeElement_zero (label : W → G) (p : ℂ) :
    cayleyHeckeElement label p 0 = 1 := by
  simp [cayleyHeckeElement]

@[simp] theorem cayleyHeckeElement_one (label : W → G) (p : ℂ) :
    cayleyHeckeElement label p 1 = cayleyGeneratorSum label := by
  simp [cayleyHeckeElement]

/-- The Hecke recurrence holds internally in the finite group algebra. -/
theorem cayleyHeckeElement_add_two
    (label : W → G) (p : ℂ) (n : ℕ) :
    cayleyHeckeElement label p (n + 2) =
      cayleyHeckeElement label p (n + 1) * cayleyGeneratorSum label -
        algebraMap ℂ (MonoidAlgebra ℂ G) p *
          cayleyHeckeElement label p n := by
  rw [cayleyHeckeElement, lpsHeckePolynomial_add_two]
  simp [cayleyHeckeElement]

/-- The regular action of the group-algebra Hecke element is the same
polynomial evaluated at Cayley adjacency. -/
theorem cayleyHeckeElement_action
    (label : W → G) (p : ℂ) (n : ℕ) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyHeckeElement label p n) =
      (lpsHeckePolynomial ℂ p n).eval₂
        (algebraMap ℂ (Module.End ℂ (G → ℂ)))
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum label)) := by
  unfold cayleyHeckeElement
  simpa using
    (Polynomial.hom_eval₂ (p := lpsHeckePolynomial ℂ p n)
      (algebraMap ℂ (MonoidAlgebra ℂ G))
      cayleyRightRegularRepresentation.asAlgebraHom.toRingHom
      (cayleyGeneratorSum label))

/-- The trace of the `n`-th Cayley Hecke operator is group order times the
identity coefficient of the corresponding group-algebra element. -/
theorem trace_cayleyHeckeElement
    (label : W → G) (p : ℂ) (n : ℕ) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyHeckeElement label p n)) =
      (Fintype.card G : ℂ) * (cayleyHeckeElement label p n).coeff 1 :=
  trace_cayleyRightRegularRepresentation_asAlgebraHom _

section LPS

open scoped MatrixGroups

variable {p : ℕ}

/-- The concrete finite Hecke element acting on the LPS quotient
`PSL(2, ZMod q)`.  No graph or spectral datum is left as a parameter. -/
noncomputable def lpsFiniteHeckeElement
    (a : LPSResiduePrime p) (n : ℕ) :
    MonoidAlgebra ℂ PSL(2, ZMod a.q) :=
  cayleyHeckeElement (lpsQuaternionLabel a) (p : ℂ) n

@[simp] theorem lpsFiniteHeckeElement_zero
    (a : LPSResiduePrime p) :
    lpsFiniteHeckeElement a 0 = 1 := by
  simp [lpsFiniteHeckeElement]

@[simp] theorem lpsFiniteHeckeElement_one
    (a : LPSResiduePrime p) :
    lpsFiniteHeckeElement a 1 =
      cayleyGeneratorSum (lpsQuaternionLabel a) := by
  simp [lpsFiniteHeckeElement]

/-- The concrete LPS finite Hecke elements satisfy the source recurrence. -/
theorem lpsFiniteHeckeElement_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsFiniteHeckeElement a (n + 2) =
      lpsFiniteHeckeElement a (n + 1) *
          cayleyGeneratorSum (lpsQuaternionLabel a) -
        algebraMap ℂ (MonoidAlgebra ℂ PSL(2, ZMod a.q)) (p : ℂ) *
          lpsFiniteHeckeElement a n := by
  exact cayleyHeckeElement_add_two (lpsQuaternionLabel a) (p : ℂ) n

/-- The regular action of the concrete finite Hecke element is the Hecke
polynomial in the actual LPS Cayley adjacency element. -/
theorem lpsFiniteHeckeElement_action
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (lpsFiniteHeckeElement a n) =
      (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
        (algebraMap ℂ
          (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
        (cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum (lpsQuaternionLabel a))) := by
  exact cayleyHeckeElement_action (lpsQuaternionLabel a) (p : ℂ) n

/-- The trace of the actual finite LPS Hecke operator has been reduced to
one concrete identity coefficient. -/
theorem trace_lpsFiniteHeckeElement
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (PSL(2, ZMod a.q) → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom
          (lpsFiniteHeckeElement a n)) =
      (Fintype.card PSL(2, ZMod a.q) : ℂ) *
        (lpsFiniteHeckeElement a n).coeff 1 := by
  exact trace_cayleyHeckeElement (lpsQuaternionLabel a) (p : ℂ) n

end LPS

end QEC.Coding.TannerLiftedProduct
