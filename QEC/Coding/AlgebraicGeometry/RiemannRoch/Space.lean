/-
All-place valuation-bound submodule.

This is the underlying valuation definition of the eventual Riemann--Roch
space over the genuine `GlobalPlace k F` carrier.  Its present results are
only the local valuation consequences: zero/additive/scalar closure,
monotonicity, product containment, and residue evaluation at a place where a
member is forced regular.

It does not yet prove any global theorem: no finite support of principal
divisors, finite residue degree, global divisor degree, product formula,
negative-degree vanishing, finite-dimensionality, Riemann--Roch formula, or
canonical-divisor statement.  In particular it does not claim a completed
global theory.
-/

import QEC.Coding.AlgebraicGeometry.Places.GlobalPlace
import QEC.Coding.AlgebraicGeometry.Divisors.ValuationBound

namespace QEC.Coding.AlgebraicGeometry

open scoped WithZero

namespace GlobalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- The actual valuation family carried by the all-place carrier. -/
def valuationFamily : GlobalPlace k F → Valuation F ℤᵐ⁰ := fun P => P.valuation

/-- The valuation-bound submodule underlying the future all-place
Riemann--Roch space. -/
def riemannRochSubmodule (G : Divisor (GlobalPlace k F)) : Submodule k F :=
  ValuationBound.space valuationFamily G

/-- Membership is exactly the collection of all local valuation bounds. -/
theorem mem_riemannRochSubmodule_iff (G : Divisor (GlobalPlace k F)) (f : F) :
    f ∈ riemannRochSubmodule G ↔
      ∀ P, P.valuation f ≤ WithZero.exp (G P) :=
  Iff.rfl

theorem zero_mem_riemannRochSubmodule (G : Divisor (GlobalPlace k F)) :
    (0 : F) ∈ riemannRochSubmodule G :=
  (riemannRochSubmodule G).zero_mem

theorem add_mem_riemannRochSubmodule {G : Divisor (GlobalPlace k F)} {f g : F}
    (hf : f ∈ riemannRochSubmodule G) (hg : g ∈ riemannRochSubmodule G) :
    f + g ∈ riemannRochSubmodule G :=
  (riemannRochSubmodule G).add_mem hf hg

theorem smul_mem_riemannRochSubmodule {G : Divisor (GlobalPlace k F)}
    (a : k) {f : F} (hf : f ∈ riemannRochSubmodule G) :
    a • f ∈ riemannRochSubmodule G :=
  (riemannRochSubmodule G).smul_mem a hf

theorem riemannRochSubmodule_mono {G H : Divisor (GlobalPlace k F)}
    (hGH : G ≤ H) : riemannRochSubmodule G ≤ riemannRochSubmodule H :=
  ValuationBound.space_mono valuationFamily hGH

theorem mul_mem_riemannRochSubmodule_add {G H : Divisor (GlobalPlace k F)} {f g : F}
    (hf : f ∈ riemannRochSubmodule G) (hg : g ∈ riemannRochSubmodule H) :
    f * g ∈ riemannRochSubmodule (G + H) :=
  ValuationBound.mul_mem_space_add valuationFamily hf hg

/-- A valuation-bound member has an actual residue evaluation at any place
whose divisor coefficient is nonpositive. -/
noncomputable def evaluateAtNonpositive (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (f : riemannRochSubmodule G) (hGP : G P ≤ 0) : residueField P :=
  evaluateRegular P (f : F)
    ((f.property P).trans (WithZero.exp_le_exp.mpr hGP))

end GlobalPlace

end QEC.Coding.AlgebraicGeometry
