import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.SmithTrace
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicDiagonalMatrixResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Smith primary traces as finite rational-place residues

This module transports the primary trace of a polynomial Smith cokernel from
the height-one ideal quotient to the actual residue field of the corresponding
finite rational place.  The Smith trace formula and the diagonal logarithmic
residue formula then identify the transported trace with the normalized
residue of the actual diagonal differential.

This is a finite rational-place comparison only.  It does not yet compare the
trace of a differential in an extension field with the sum of its upper-place
residues, or prove a global residue theorem, duality, genus, canonical degree,
or Riemann--Roch.
-/

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry

namespace GlobalPlace

variable {k : Type*} [Field k] [Finite k]

/-- The polynomial quotient by a finite height-one prime is canonically the
residue field of the corresponding normalized rational place. -/
noncomputable def rationalAdicIdealResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (k[X] ⧸ p.asIdeal) ≃+* (rationalAdic p).residueField :=
  (Ideal.quotEquivOfEq (rationalAdic_asIdeal_eq_span p)).trans
    (rationalAdicResidueEquiv p)

/-- The rational-place ideal-quotient equivalence sends a polynomial class
to the actual reduction of that polynomial in the valuation ring. -/
@[simp]
theorem rationalAdicIdealResidueEquiv_mk
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    rationalAdicIdealResidueEquiv p (Ideal.Quotient.mk p.asIdeal b) =
      (rationalAdic p).residue
        (rationalAdicPolynomialToValuationRing p b) := by
  change rationalAdicResidueEquiv p
      (AdjoinRoot.mk (rationalAdicPolynomial p) b) = _
  exact rationalAdicResidueEquiv_mk p b

end GlobalPlace

namespace Differential

variable {k : Type*} [Field k] [Finite k]

private theorem primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (P : Ideal k[X]) [P.IsMaximal]
    (q : k[X]) (hq : Irreducible q) (hP : P = Ideal.span {q})
    (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity P (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    primaryTorsionTrace P (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity P
          (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ P) *
        Ideal.Quotient.mk P
          (LinearMap.toMatrix target target g i i) := by
  subst P
  simp_rw [multiplicity_span_singleton_eq q (a _) hq (ha _)] at hdepth ⊢
  exact primaryTorsionTrace_cokernel_eq_sum_diagonal
    source target a ha f g hdiag hcomm q hq depth hdepth

private theorem primaryTorsionTrace_cokernel_eq_sum_diagonal_at_rationalAdicIdeal
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    primaryTorsionTrace p.asIdeal (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity p.asIdeal
          (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ p.asIdeal) *
        Ideal.Quotient.mk p.asIdeal
          (LinearMap.toMatrix target target g i i) := by
  exact primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    source target a ha f g hdiag hcomm p.asIdeal
      (GlobalPlace.rationalAdicPolynomial p)
      (GlobalPlace.rationalAdicPolynomial_irreducible p)
      (GlobalPlace.rationalAdic_asIdeal_eq_span p) depth hdepth

/-- A Smith-diagonal polynomial cokernel has primary trace equal, after the
canonical finite-place residue transport, to the normalized residue of its
actual diagonal logarithmic differential. -/
theorem
    rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism f g hcomm) depth) =
      simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
          (LinearMap.toMatrix target target g) a ha) := by
  rw [primaryTorsionTrace_cokernel_eq_sum_diagonal_at_rationalAdicIdeal
    source target a ha f g hdiag hcomm p depth hdepth,
    map_sum,
    simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_natCast, GlobalPlace.rationalAdicIdealResidueEquiv_mk]
  exact mul_comm _ _

/-- Smith bases can be chosen so that the primary trace of an injective
polynomial cokernel is the normalized finite-place residue of the resulting
diagonal logarithmic differential. -/
theorem exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_simplePoleResidue
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (b : Module.Basis (Fin n) k[X] N)
    (f g : N →ₗ[k[X]] N) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    ∃ source target : Module.Basis (Fin n) k[X] N, ∃ a : Fin n → k[X],
      ∃ ha : ∀ i, a i ≠ 0,
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        GlobalPlace.rationalAdicIdealResidueEquiv p
            (primaryTorsionTrace p.asIdeal
              (cokernelEndomorphism f g hcomm)
                (∑ i, multiplicity p.asIdeal
                  (Ideal.span ({a i} : Set k[X])))) =
          simplePoleResidue (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
              (LinearMap.toMatrix target target g) a ha) := by
  obtain ⟨source, target, a, ha, hdiag, hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute b f g hf hcomm
  refine ⟨source, target, a, ha, hdiag, hgdiag, ?_⟩
  apply
    rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
      source target a ha f g hdiag hcomm p
  intro i
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le
      (multiplicity p.asIdeal (Ideal.span ({a j} : Set k[X]))))
    (Finset.mem_univ i)

end Differential

end QEC.Coding.AlgebraicGeometry
