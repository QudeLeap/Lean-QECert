import QEC.Coding.FiniteFieldMultiplication.Selector
import QEC.Distillation.MultiplicativeQuditProtocol.Register

/-!
# Disjoint inverse-permuted binary CCZ triples

[Ngu24, Eq. (mfe-transversal)] uses inverse physical permutations. The
existing MFE API uses forward pullback, so the physical permutations here
are their inverses. Cardinality counts all qubits in one encoded block.
-/

noncomputable section

namespace QEC.Distillation.Ngu24Binary

open Coding
open scoped BigOperators

universe u
variable (J : Type u)

/-- Physical permutation; its inverse is the MFE's forward pullback. -/
def binaryPi2 : Equiv.Perm (J × Fin 512) :=
  (Equiv.refl J).prodCongr f256MFEpi2.symm

/-- Physical permutation; its inverse is the MFE's forward pullback. -/
def binaryPi3 : Equiv.Perm (J × Fin 512) :=
  (Equiv.refl J).prodCongr f256MFEpi3.symm

@[simp] theorem binaryPi2_symm_apply (j : J) (q : Fin 512) :
    (binaryPi2 J).symm (j, q) = (j, f256MFEpi2 q) := rfl

@[simp] theorem binaryPi3_symm_apply (j : J) (q : Fin 512) :
    (binaryPi3 J).symm (j, q) = (j, f256MFEpi3 q) := rfl

/-- One actual physical vertex in each separately tagged code block. -/
def binaryTripleVertex (x : J × Fin 512) (tag : ThreeCopyTag) :
    TaggedThreeCopyCoordinate (J × Fin 512) :=
  (tag, match tag with
    | .first => x
    | .second => (binaryPi2 J).symm x
    | .third => (binaryPi3 J).symm x)

theorem binaryTripleVertex_injective (x : J × Fin 512) :
    Function.Injective (binaryTripleVertex J x) := by
  intro a b h
  exact congrArg Prod.fst h

variable [Fintype J]

/-- The literal three-qubit support with the source's inverse permutations. -/
def binaryTripleSupport (x : J × Fin 512) : Finset (TaggedThreeCopyCoordinate (J × Fin 512)) :=
  Finset.univ.map ⟨binaryTripleVertex J x, binaryTripleVertex_injective J x⟩

theorem binaryTripleSupport_card (x : J × Fin 512) :
    (binaryTripleSupport J x).card = 3 := by
  rw [binaryTripleSupport, Finset.card_map, Finset.card_univ]
  rfl

theorem binaryTripleSupport_disjoint {x y : J × Fin 512} (hne : x ≠ y) :
    Disjoint (binaryTripleSupport J x) (binaryTripleSupport J y) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hx hy
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hy
  have h : binaryTripleVertex J x a = binaryTripleVertex J y b := ha.trans hb.symm
  have ht : a = b := congrArg Prod.fst h
  subst b
  have hc := congrArg Prod.snd h
  apply hne
  cases a with
  | first => exact hc
  | second => exact (binaryPi2 J).symm.injective hc
  | third => exact (binaryPi3 J).symm.injective hc

/-- All selected triples, indexed by their distinct first-block vertices. -/
def binarySelectedSites : Finset (J × Fin 512) :=
  Finset.univ.product f256SelectedCoordinates

theorem binarySelectedSites_card :
    (binarySelectedSites J).card = Fintype.card J * f256SelectedCoordinates.card := by
  simp [binarySelectedSites]

theorem binarySelectedSites_card_lower :
    Fintype.card J ≤ (binarySelectedSites J).card := by
  rw [binarySelectedSites_card]
  simpa using Nat.mul_le_mul_left (Fintype.card J) f256SelectedCoordinates_card_ge_one

/-- The denominator counts every qubit of one block, including unselected sites. -/
theorem binarySelectedSites_global_density :
    (Fintype.card (J × Fin 512) : ℚ) / 512 ≤ (binarySelectedSites J).card := by
  have h : (Fintype.card J : ℚ) ≤ (binarySelectedSites J).card := by
    exact_mod_cast binarySelectedSites_card_lower J
  simpa using h

end QEC.Distillation.Ngu24Binary
