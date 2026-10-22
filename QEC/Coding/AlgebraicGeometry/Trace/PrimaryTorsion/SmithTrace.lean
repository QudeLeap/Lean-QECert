import QEC.Coding.AlgebraicGeometry.Trace.PolynomialSmithMatrix
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.PiTrace
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.CyclicTraceStabilization
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.TraceEquiv

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Primary trace on a Smith cokernel

An injective endomorphism of a finite free module over a principal ideal
domain has a Smith diagonalization.  Its cokernel is therefore linearly
equivalent to a finite product of cyclic quotients.  If a second endomorphism
commutes with the first, its induced cokernel endomorphism has diagonal blocks
given by the diagonal entries of its matrix in the Smith target basis.

Combining the product trace decomposition with stabilized cyclic traces gives
the primary trace as the finite sum of those diagonal entries weighted by the
corresponding multiplicities.  The proof is symbolic and does not enumerate a
quotient, product carrier, or finite field.  It does not prove a residue,
duality, genus, or Riemann--Roch theorem.
-/

open scoped Polynomial

namespace QEC.Coding.AlgebraicGeometry

open Module

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

noncomputable local instance cokernelModuleFinite [Module.Finite R M]
    (f : M →ₗ[R] M) : Module.Finite R (M ⧸ LinearMap.range f) :=
  Module.Finite.quotient R (LinearMap.range f)

noncomputable local instance cyclicQuotientModuleFinite (a : R) :
    Module.Finite R (R ⧸ Ideal.span {a}) :=
  Module.Finite.quotient R (Ideal.span {a})

private theorem range_le_comap_of_commute (f g : M →ₗ[R] M)
    (hcomm : f.comp g = g.comp f) :
    LinearMap.range f ≤ (LinearMap.range f).comap g := by
  rintro _ ⟨x, rfl⟩
  refine ⟨g x, ?_⟩
  exact LinearMap.congr_fun hcomm x

/-- The endomorphism induced on the cokernel of an endomorphism by a
commuting endomorphism. -/
def cokernelEndomorphism (f g : M →ₗ[R] M)
    (hcomm : f.comp g = g.comp f) :
    (M ⧸ LinearMap.range f) →ₗ[R] (M ⧸ LinearMap.range f) :=
  (LinearMap.range f).mapQ (LinearMap.range f) g
    (range_le_comap_of_commute f g hcomm)

@[simp]
private theorem cokernelEndomorphism_mk (f g : M →ₗ[R] M)
    (hcomm : f.comp g = g.comp f) (x : M) :
    cokernelEndomorphism f g hcomm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (g x) :=
  rfl

variable [IsDomain R] [IsPrincipalIdealRing R]

private def smithCoordinateSubmodule {n : ℕ} (a : Fin n → R) :
    Submodule R (Fin n → R) :=
  Submodule.pi Set.univ fun i => Ideal.span {a i}

private theorem target_repr_apply_eq_mul_of_toMatrix_eq_diagonal
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (x : M) (i : Fin n) :
    target.repr (f x) i = a i * source.repr x i := by
  have h := congrFun
    (LinearMap.toMatrix_mulVec_repr source target f x) i
  rw [hdiag] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using h.symm

private theorem range_map_target_equivFun_eq_smithCoordinateSubmodule
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    (LinearMap.range f).map
        (target.equivFun : M →ₗ[R] Fin n → R) =
      smithCoordinateSubmodule a := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    rw [smithCoordinateSubmodule, Submodule.mem_pi]
    intro i _hi
    rw [Ideal.mem_span_singleton]
    refine ⟨source.repr z i, ?_⟩
    exact target_repr_apply_eq_mul_of_toMatrix_eq_diagonal
      source target a f hdiag z i
  · intro hy
    have hyi : ∀ i, y i ∈ Ideal.span ({a i} : Set R) := by
      intro i
      exact (Submodule.mem_pi.mp hy) i (Set.mem_univ i)
    have hydiv : ∀ i, a i ∣ y i := by
      intro i
      exact Ideal.mem_span_singleton.mp (hyi i)
    choose c hc using hydiv
    let x : M := source.equivFun.symm c
    refine ⟨f x, ⟨x, rfl⟩, ?_⟩
    apply funext
    intro i
    change target.repr (f x) i = y i
    rw [target_repr_apply_eq_mul_of_toMatrix_eq_diagonal
      source target a f hdiag]
    have hxcoord : source.repr x i = c i := by
      exact congrFun (source.equivFun.apply_symm_apply c) i
    rw [hxcoord]
    exact (hc i).symm

private noncomputable def smithCokernelEquiv
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    (M ⧸ LinearMap.range f) ≃ₗ[R]
      ∀ i, R ⧸ Ideal.span ({a i} : Set R) :=
  (Submodule.Quotient.equiv
      (LinearMap.range f) (smithCoordinateSubmodule a)
      target.equivFun
      (range_map_target_equivFun_eq_smithCoordinateSubmodule
        source target a f hdiag)).trans
    (Submodule.quotientPi fun i => Ideal.span ({a i} : Set R))

@[simp]
private theorem smithCokernelEquiv_mk
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (x : M) :
    smithCokernelEquiv source target a f hdiag
        (Submodule.Quotient.mk x) =
      fun i => Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
        (target.repr x i) :=
  rfl

private theorem smithCokernelEquiv_symm_single_mk
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (i : Fin n) (r : R) :
    (smithCokernelEquiv source target a f hdiag).symm
        (LinearMap.single R
          (fun j => R ⧸ Ideal.span ({a j} : Set R)) i
          (Ideal.Quotient.mk (Ideal.span ({a i} : Set R)) r)) =
      Submodule.Quotient.mk (r • target i) := by
  apply (smithCokernelEquiv source target a f hdiag).injective
  rw [LinearEquiv.apply_symm_apply]
  apply funext
  intro j
  rw [smithCokernelEquiv_mk]
  by_cases hij : i = j
  · subst j
    simp only [LinearMap.single_apply, Pi.single_eq_same, map_smul,
      Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · simp [LinearMap.single_apply, Pi.single_apply, map_smul,
      Basis.repr_self, hij]

private theorem piDiagonalBlock_conj_smithCokernelEquiv
    {n : ℕ} (source target : Basis (Fin n) R M)
    (a : Fin n → R) (f g : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f) (i : Fin n) :
    piDiagonalBlock
        ((smithCokernelEquiv source target a f hdiag).conj
          (cokernelEndomorphism f g hcomm)) i =
      cyclicQuotientMul (a i)
        (LinearMap.toMatrix target target g i i) := by
  apply LinearMap.ext
  intro z
  induction z using Quotient.inductionOn' with
  | _ r =>
      change
        (smithCokernelEquiv source target a f hdiag
          (cokernelEndomorphism f g hcomm
            ((smithCokernelEquiv source target a f hdiag).symm
              (LinearMap.single R
                (fun j => R ⧸ Ideal.span ({a j} : Set R)) i
                (Ideal.Quotient.mk (Ideal.span ({a i} : Set R)) r))))) i =
          Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
            (LinearMap.toMatrix target target g i i * r)
      rw [smithCokernelEquiv_symm_single_mk,
        cokernelEndomorphism_mk, smithCokernelEquiv_mk]
      rw [map_smul, map_smul]
      change Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
          (r * target.repr (g (target i)) i) =
        Ideal.Quotient.mk (Ideal.span ({a i} : Set R))
          (LinearMap.toMatrix target target g i i * r)
      rw [LinearMap.toMatrix_apply]
      congr 1
      ring

/-- For a Smith-diagonal presentation of an injective endomorphism, the
primary trace of a commuting endomorphism on its cokernel is the sum of the
diagonal target-basis coefficients weighted by the corresponding
multiplicities. -/
theorem primaryTorsionTrace_cokernel_eq_sum_diagonal
    [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    (source target : Basis (Fin n) R M)
    (a : Fin n → R) (ha : ∀ i, a i ≠ 0)
    (f g : M →ₗ[R] M)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (q : R) (hq : Irreducible q) [hmax : (Ideal.span {q}).IsMaximal]
    (depth : ℕ) (hdepth : ∀ i, multiplicity q (a i) ≤ depth) :
    primaryTorsionTrace (Ideal.span {q})
        (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity q (a i) : R ⧸ Ideal.span {q}) *
        Ideal.Quotient.mk (Ideal.span {q})
          (LinearMap.toMatrix target target g i i) := by
  let E := smithCokernelEquiv source target a f hdiag
  let G := E.conj (cokernelEndomorphism f g hcomm)
  have hintertwines : (E : (M ⧸ LinearMap.range f) →ₗ[R]
      ∀ i, R ⧸ Ideal.span ({a i} : Set R)).comp
        (cokernelEndomorphism f g hcomm) =
      G.comp (E : (M ⧸ LinearMap.range f) →ₗ[R]
        ∀ i, R ⧸ Ideal.span ({a i} : Set R)) := by
    apply LinearMap.ext
    intro x
    simp only [G, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  calc
    primaryTorsionTrace (Ideal.span {q})
        (cokernelEndomorphism f g hcomm) depth =
      primaryTorsionTrace (Ideal.span {q}) G depth :=
        primaryTorsionTrace_eq_of_intertwining
          (Ideal.span {q}) E (cokernelEndomorphism f g hcomm)
            G hintertwines depth
    _ = ∑ i, primaryTorsionTrace (Ideal.span {q})
        (piDiagonalBlock G i) depth :=
      primaryTorsionTrace_pi_eq_sum_diagonal (Ideal.span {q}) G depth
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [piDiagonalBlock_conj_smithCokernelEquiv
        source target a f g hdiag hcomm i]
      exact primaryTorsionTrace_cyclicQuotient_of_multiplicity_le
        q (a i) (LinearMap.toMatrix target target g i i)
          hq (ha i) depth (hdepth i)

/-- Smith bases may be chosen so that the cokernel primary trace of every
commuting endomorphism has the diagonal multiplicity formula at the sum of
the Smith multiplicities. -/
theorem exists_smith_primaryTorsionTrace_cokernel_eq_sum
    [IsNoetherianRing R] [Module.Finite R M]
    {n : ℕ} (b : Basis (Fin n) R M)
    (f g : M →ₗ[R] M) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (q : R) (hq : Irreducible q) [hmax : (Ideal.span {q}).IsMaximal] :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        primaryTorsionTrace (Ideal.span {q})
            (cokernelEndomorphism f g hcomm)
              (∑ i, multiplicity q (a i)) =
          ∑ i, (multiplicity q (a i) : R ⧸ Ideal.span {q}) *
            Ideal.Quotient.mk (Ideal.span {q})
              (LinearMap.toMatrix target target g i i) := by
  obtain ⟨source, target, a, ha, hdiag, hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute b f g hf hcomm
  refine ⟨source, target, a, ha, hdiag, hgdiag, ?_⟩
  apply primaryTorsionTrace_cokernel_eq_sum_diagonal
    source target a ha f g hdiag hcomm q hq
  intro i
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le (multiplicity q (a j)))
    (Finset.mem_univ i)

variable {k : Type*} [Field k] [Finite k]

private theorem primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (source target : Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (P : Ideal k[X]) [P.IsMaximal]
    (q : k[X]) (hq : Irreducible q) (hP : P = Ideal.span {q})
    (depth : ℕ)
    (hdepth : ∀ i, multiplicity P (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    primaryTorsionTrace P (cokernelEndomorphism f g hcomm) depth =
      ∑ i, (multiplicity P (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ P) *
        Ideal.Quotient.mk P
          (LinearMap.toMatrix target target g i i) := by
  subst P
  simp_rw [multiplicity_span_singleton_eq q (a _) hq (ha _)] at hdepth ⊢
  exact primaryTorsionTrace_cokernel_eq_sum_diagonal
    source target a ha f g hdiag hcomm q hq depth hdepth

/-- At a finite rational place, Smith bases identify the primary trace on an
injective polynomial cokernel with the diagonal sum weighted by the actual
principal-ideal multiplicities. -/
theorem exists_polynomialSmith_primaryTorsionTrace_cokernel_eq_sum
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (b : Basis (Fin n) k[X] N)
    (f g : N →ₗ[k[X]] N) (hf : Function.Injective f)
    (hcomm : f.comp g = g.comp f)
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    ∃ source target : Basis (Fin n) k[X] N, ∃ a : Fin n → k[X],
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
        (∀ i, LinearMap.toMatrix source source g i i =
          LinearMap.toMatrix target target g i i) ∧
        primaryTorsionTrace p.asIdeal
            (cokernelEndomorphism f g hcomm)
              (∑ i, multiplicity p.asIdeal
                (Ideal.span ({a i} : Set k[X]))) =
          ∑ i, (multiplicity p.asIdeal
              (Ideal.span ({a i} : Set k[X])) : k[X] ⧸ p.asIdeal) *
            Ideal.Quotient.mk p.asIdeal
              (LinearMap.toMatrix target target g i i) := by
  obtain ⟨source, target, a, ha, hdiag, hgdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal_of_commute b f g hf hcomm
  refine ⟨source, target, a, ha, hdiag, hgdiag, ?_⟩
  let q := GlobalPlace.rationalAdicPolynomial p
  apply primaryTorsionTrace_cokernel_eq_sum_diagonal_of_eq_span
    source target a ha f g hdiag hcomm p.asIdeal q
      (GlobalPlace.rationalAdicPolynomial_irreducible p)
        (GlobalPlace.rationalAdic_asIdeal_eq_span p)
  intro i
  exact Finset.single_le_sum
    (fun j _hj => Nat.zero_le
      (multiplicity p.asIdeal (Ideal.span ({a j} : Set k[X]))))
    (Finset.mem_univ i)

end QEC.Coding.AlgebraicGeometry
