import QEC.Coding.Core.Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Finite symplectic linear algebra

This module bundles the coordinatewise vector-space structure and the standard
nondegenerate alternating form on the finite symplectic vectors used by binary
Pauli representatives.
-/

noncomputable section

namespace QEC
namespace Coding

universe u v

namespace SymplecticVector

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/-- Symplectic vectors are linearly equivalent to their pair of coordinate words. -/
def toProdEquiv : SymplecticVector F ι ≃ Word F ι × Word F ι where
  toFun v := (v.xPart, v.zPart)
  invFun p := { xPart := p.1, zPart := p.2 }
  left_inv v := by cases v; rfl
  right_inv p := by cases p; rfl

instance instAddCommGroup : AddCommGroup (SymplecticVector F ι) :=
  (toProdEquiv (F := F) (ι := ι)).addCommGroup

instance instModule : Module F (SymplecticVector F ι) :=
  (toProdEquiv (F := F) (ι := ι)).module F

@[simp] theorem xPart_zero : (0 : SymplecticVector F ι).xPart = 0 := rfl
@[simp] theorem zPart_zero : (0 : SymplecticVector F ι).zPart = 0 := rfl

@[simp] theorem xPart_add (a b : SymplecticVector F ι) :
    (a + b).xPart = a.xPart + b.xPart := rfl

@[simp] theorem zPart_add (a b : SymplecticVector F ι) :
    (a + b).zPart = a.zPart + b.zPart := rfl

@[simp] theorem xPart_smul (c : F) (a : SymplecticVector F ι) :
    (c • a).xPart = c • a.xPart := rfl

@[simp] theorem zPart_smul (c : F) (a : SymplecticVector F ι) :
    (c • a).zPart = c • a.zPart := rfl

/-- The coordinate-pair equivalence as a linear equivalence. -/
def toProdLinearEquiv :
    SymplecticVector F ι ≃ₗ[F] Word F ι × Word F ι where
  toEquiv := toProdEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instFiniteDimensional : FiniteDimensional F (SymplecticVector F ι) :=
  LinearEquiv.finiteDimensional (toProdLinearEquiv (F := F) (ι := ι)).symm

end SymplecticVector

namespace FiniteSymplectic

variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

/-- The standard finite-coordinate symplectic form as a Mathlib bilinear form. -/
def form : LinearMap.BilinForm F (SymplecticVector F ι) where
  toFun a :=
    { toFun := fun b => symplecticForm a b
      map_add' := by
        intro b c
        change
          (∑ i, (a.xPart i * (b.zPart i + c.zPart i) -
            a.zPart i * (b.xPart i + c.xPart i))) =
          (∑ i, (a.xPart i * b.zPart i - a.zPart i * b.xPart i)) +
            ∑ i, (a.xPart i * c.zPart i - a.zPart i * c.xPart i)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      map_smul' := by
        intro c b
        change
          (∑ i, (a.xPart i * (c * b.zPart i) - a.zPart i * (c * b.xPart i))) =
            c * ∑ i, (a.xPart i * b.zPart i - a.zPart i * b.xPart i)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring }
  map_add' := by
    intro a b
    ext c
    change
      (∑ i, ((a.xPart i + b.xPart i) * c.zPart i -
        (a.zPart i + b.zPart i) * c.xPart i)) =
      (∑ i, (a.xPart i * c.zPart i - a.zPart i * c.xPart i)) +
        ∑ i, (b.xPart i * c.zPart i - b.zPart i * c.xPart i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  map_smul' := by
    intro c a
    ext b
    change
      (∑ i, ((c * a.xPart i) * b.zPart i - (c * a.zPart i) * b.xPart i)) =
        c * ∑ i, (a.xPart i * b.zPart i - a.zPart i * b.xPart i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

@[simp] theorem form_apply (a b : SymplecticVector F ι) :
    form a b = symplecticForm a b := rfl

/-- The standard symplectic form is alternating. -/
theorem form_isAlt : (form (F := F) (ι := ι)).IsAlt := by
  intro v
  change symplecticForm v v = 0
  rw [symplecticForm]
  apply Finset.sum_eq_zero
  intro i _hi
  exact sub_eq_zero.mpr (mul_comm _ _)

/-- The standard finite-coordinate symplectic form is nondegenerate. -/
theorem form_nondegenerate : (form (F := F) (ι := ι)).Nondegenerate := by
  let B := form (F := F) (ι := ι)
  have hleft : B.SeparatingLeft := by
    intro v hv
    have hx : v.xPart = 0 :=
      (wordPairing_nondegenerate (F := F) (ι := ι)).1 v.xPart (fun z => by
        simpa [B, form, symplecticForm, wordPairing_apply, dotProduct] using
          hv ({ xPart := 0, zPart := z } : SymplecticVector F ι))
    have hz : v.zPart = 0 :=
      (wordPairing_nondegenerate (F := F) (ι := ι)).1 v.zPart (fun x => by
        have hneg : -wordPairing (F := F) (ι := ι) v.zPart x = 0 := by
          simpa [B, form, symplecticForm, wordPairing_apply, dotProduct] using
            hv ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        exact neg_eq_zero.mp hneg)
    rcases v with ⟨x, z⟩
    simp only at hx hz
    subst x
    subst z
    rfl
  refine ⟨hleft, ?_⟩
  intro v hv
  apply hleft v
  intro w
  exact form_isAlt.isRefl w v (hv w)

/--
Outside a subspace, some vector in its symplectic orthogonal has nonzero
pairing with the given vector. This is the finite-dimensional
double-orthogonal separation step used for logical Pauli partners.
-/
theorem exists_mem_orthogonal_pairing_ne_zero
    (S : Submodule F (SymplecticVector F ι))
    {e : SymplecticVector F ι}
    (_heOrthogonal : e ∈ (form (F := F) (ι := ι)).orthogonal S)
    (he : e ∉ S) :
    ∃ f, f ∈ (form (F := F) (ι := ι)).orthogonal S ∧ form e f ≠ 0 := by
  by_contra h
  push Not at h
  have heDouble :
      e ∈ (form (F := F) (ι := ι)).orthogonal
        ((form (F := F) (ι := ι)).orthogonal S) := by
    intro f hf
    exact form_isAlt.isRefl e f (h f hf)
  have heS : e ∈ S := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate
      form_isAlt.isRefl S] at heDouble
    exact heDouble
  exact he heS

end FiniteSymplectic
end Coding
end QEC
