import QEC.Semantics.Dynamics.ThermalEncoding
import QEC.Semantics.Dynamics.FourBlockGenerator

/-!
# Finite spectral projectors and grouped Bohr frequencies

Equal energies and equal frequency gaps are grouped before forming jump operators.
The public Hamiltonian constructors use the actual spectral theorem; the basis
lemmas below supply their finite linear-algebra proofs.
-/

namespace QEC.Semantics.Davies

open Classical
open scoped BigOperators
noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix entries in an orthonormal basis, on the existing operator carrier. -/
def entry (b : OrthonormalBasis ι ℂ V) (A : Operator V) (i j : ι) : ℂ :=
  inner ℂ (b i) (A (b j))

@[simp] theorem entry_zero (b : OrthonormalBasis ι ℂ V) (i j : ι) :
    entry b 0 i j = 0 := by simp [entry]
@[simp] theorem entry_add (b : OrthonormalBasis ι ℂ V) (A B : Operator V) (i j : ι) :
    entry b (A + B) i j = entry b A i j + entry b B i j := by simp [entry]
@[simp] theorem entry_sub (b : OrthonormalBasis ι ℂ V) (A B : Operator V) (i j : ι) :
    entry b (A - B) i j = entry b A i j - entry b B i j := by simp [entry]
@[simp] theorem entry_smul (b : OrthonormalBasis ι ℂ V) (c : ℂ)
    (A : Operator V) (i j : ι) : entry b (c • A) i j = c * entry b A i j := by
  simp [entry]
@[simp] theorem entry_real_smul (b : OrthonormalBasis ι ℂ V) (c : ℝ)
    (A : Operator V) (i j : ι) : entry b (c • A) i j = (c : ℂ) * entry b A i j := by
  simp [entry]
@[simp] theorem entry_ite (b : OrthonormalBasis ι ℂ V) (p : Prop) [Decidable p]
    (A B : Operator V) (i j : ι) :
    entry b (if p then A else B) i j = if p then entry b A i j else entry b B i j := by
  split_ifs <;> rfl
@[simp] theorem entry_one (b : OrthonormalBasis ι ℂ V) (i j : ι) :
    entry b 1 i j = if i = j then 1 else 0 := by simp [entry, b.inner_eq_ite]
@[simp] theorem entry_sum {κ : Type*} (s : Finset κ) (b : OrthonormalBasis ι ℂ V)
    (A : κ → Operator V) (i j : ι) :
    entry b (∑ k ∈ s, A k) i j = ∑ k ∈ s, entry b (A k) i j := by
  simp [entry, LinearMap.sum_apply, inner_sum]

theorem entry_ext (b : OrthonormalBasis ι ℂ V) {A B : Operator V}
    (h : ∀ i j, entry b A i j = entry b B i j) : A = B := by
  apply b.toBasis.ext
  intro j
  apply b.repr.injective
  ext i
  simpa only [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, entry] using h i j

theorem entry_mul (b : OrthonormalBasis ι ℂ V) (A B : Operator V) (i j : ι) :
    entry b (A * B) i j = ∑ k, entry b A i k * entry b B k j := by
  change inner ℂ (b i) (A (B (b j))) = _
  rw [← b.sum_repr' (B (b j)), map_sum, inner_sum]
  simp only [map_smul, inner_smul_right, entry]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem entry_adjoint (b : OrthonormalBasis ι ℂ V) (A : Operator V) (i j : ι) :
    entry b (LinearMap.adjoint A) i j = star (entry b A j i) := by
  simp only [entry, LinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (A (b i)) (b j)).symm

/-- A rank-one matrix unit, retaining basis labels even at degenerate energies. -/
def matrixUnit (b : OrthonormalBasis ι ℂ V) (i j : ι) : Operator V :=
  (InnerProductSpace.rankOne ℂ (b i) (b j)).toLinearMap

@[simp] theorem entry_matrixUnit (b : OrthonormalBasis ι ℂ V) (i j k l : ι) :
    entry b (matrixUnit b i j) k l = if k = i ∧ j = l then 1 else 0 := by
  simp [entry, matrixUnit, InnerProductSpace.rankOne_apply, b.inner_eq_ite]
  split_ifs <;> simp_all

/-- Actual diagonal operator with the indicated real energies. -/
def diagonal (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) : Operator V :=
  ∑ i, (energy i : ℂ) • matrixUnit b i i

@[simp] theorem entry_diagonal (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (i j : ι) :
    entry b (diagonal b energy) i j = if i = j then (energy i : ℂ) else 0 := by
  simp only [diagonal, entry_sum, entry_smul, entry_matrixUnit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki; simp [Ne.symm hki]
  · simp

/-- Full projector onto one energy, including every degenerate basis vector. -/
def energyProjector (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E : ℝ) : Operator V :=
  ∑ i, if energy i = E then matrixUnit b i i else 0

@[simp] theorem entry_energyProjector (b : OrthonormalBasis ι ℂ V)
    (energy : ι → ℝ) (E : ℝ) (i j : ι) :
    entry b (energyProjector b energy E) i j =
      if i = j ∧ energy i = E then 1 else 0 := by
  simp only [energyProjector, entry_sum, entry_ite, entry_matrixUnit, entry_zero]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j <;> simp [hij]
  · intro k _ hki; simp [Ne.symm hki]
  · simp

/-- Distinct energy values; multiplicity remains inside each projector. -/
def energyValues (energy : ι → ℝ) : Finset ℝ := Finset.univ.image energy

@[simp] theorem mem_energyValues (energy : ι → ℝ) (E : ℝ) :
    E ∈ energyValues energy ↔ ∃ i, energy i = E := by simp [energyValues]

theorem energyProjector_adjoint (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E : ℝ) :
    LinearMap.adjoint (energyProjector b energy E) = energyProjector b energy E := by
  apply entry_ext b
  intro i j
  rw [entry_adjoint]
  by_cases hij : i = j
  · subst j; simp only [entry_energyProjector]; split_ifs <;> simp
  · simp [entry_energyProjector, hij, Ne.symm hij]

theorem energyProjector_mul (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E F : ℝ) :
    energyProjector b energy E * energyProjector b energy F =
      if E = F then energyProjector b energy E else 0 := by
  apply entry_ext b
  intro i j
  rw [entry_mul]
  simp only [entry_energyProjector, entry_ite, entry_zero, ite_and]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst j; split_ifs <;> simp_all
  · simp [hij]

theorem sum_energyProjector (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) :
    (∑ E ∈ energyValues energy, energyProjector b energy E) = 1 := by
  apply entry_ext b
  intro i j
  by_cases hij : i = j
  · subst j
    simp [entry_energyProjector, energyValues]
  · simp [entry_energyProjector, hij]

theorem diagonal_mul_projector (b : OrthonormalBasis ι ℂ V)
    (energy : ι → ℝ) (E : ℝ) :
    diagonal b energy * energyProjector b energy E =
      (E : ℂ) • energyProjector b energy E := by
  apply entry_ext b
  intro i j
  rw [entry_mul]
  simp only [entry_diagonal, entry_energyProjector, entry_smul, ite_and]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst j; split_ifs <;> simp_all
  · simp [hij]

/-- A distinct finite frequency set, not a multiset of transitions. -/
def frequencies (energy : ι → ℝ) : Finset ℝ :=
  (Finset.univ : Finset (ι × ι)).image (fun ij => energy ij.2 - energy ij.1)

@[simp] theorem mem_frequencies (energy : ι → ℝ) (ω : ℝ) :
    ω ∈ frequencies energy ↔ ∃ i j, energy j - energy i = ω := by
  simp [frequencies]

theorem neg_mem_frequencies (energy : ι → ℝ) {ω : ℝ}
    (h : ω ∈ frequencies energy) : -ω ∈ frequencies energy := by
  obtain ⟨i,j,h⟩ := (mem_frequencies energy ω).mp h
  exact (mem_frequencies energy (-ω)).mpr ⟨j,i,by linarith⟩

abbrev Frequency (energy : ι → ℝ) := {ω // ω ∈ frequencies energy}

def negFrequency (energy : ι → ℝ) : Frequency energy ≃ Frequency energy where
  toFun ω := ⟨-ω.1, neg_mem_frequencies energy ω.2⟩
  invFun ω := ⟨-ω.1, neg_mem_frequencies energy ω.2⟩
  left_inv ω := by ext; simp
  right_inv ω := by ext; simp

/-- Coherent sum of all matrix entries with one energy gap. -/
def frequencyComponent (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) (ω : ℝ) : Operator V :=
  ∑ i, ∑ j, if energy j - energy i = ω then entry b A i j • matrixUnit b i j else 0

@[simp] theorem entry_frequencyComponent (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) (ω : ℝ) (i j : ι) :
    entry b (frequencyComponent b energy A ω) i j =
      if energy j - energy i = ω then entry b A i j else 0 := by
  simp only [frequencyComponent, entry_sum, entry_ite, entry_smul, entry_matrixUnit, entry_zero]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [hkj]
    · simp
  · intro k _ hki
    apply Finset.sum_eq_zero
    intro l _
    simp [Ne.symm hki]
  · simp

theorem sum_frequencyComponent (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) : (∑ ω : Frequency energy, frequencyComponent b energy A ω.1) = A := by
  apply entry_ext b
  intro i j
  simp only [entry_sum, entry_frequencyComponent]
  let w : Frequency energy := ⟨energy j - energy i, (mem_frequencies _ _).mpr ⟨i,j,rfl⟩⟩
  have he : ∀ ω : Frequency energy, energy j - energy i = ω.1 ↔ ω = w := by
    intro ω
    constructor
    · intro h; exact Subtype.ext h.symm
    · rintro rfl; rfl
  simp_rw [he]
  simp

theorem frequencyComponent_adjoint (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) (ω : ℝ) :
    LinearMap.adjoint (frequencyComponent b energy A ω) =
      frequencyComponent b energy (LinearMap.adjoint A) (-ω) := by
  apply entry_ext b
  intro i j
  rw [entry_adjoint]
  simp only [entry_frequencyComponent, entry_adjoint]
  have he : energy i - energy j = ω ↔ energy j - energy i = -ω := by constructor <;> intro h <;> linarith
  simp only [he]
  split_ifs <;> simp

theorem frequencyComponent_add (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A B : Operator V) (ω : ℝ) :
    frequencyComponent b energy (A+B) ω = frequencyComponent b energy A ω +
      frequencyComponent b energy B ω := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_add]
  split_ifs <;> simp

/-- Canonical actual spectral basis of a self-adjoint Hamiltonian. -/
def hamiltonianBasis (H : Operator V) (hH : H.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V := hH.eigenvectorBasis rfl

def hamiltonianEnergies (H : Operator V) (hH : H.IsSymmetric) :
    Fin (Module.finrank ℂ V) → ℝ := hH.eigenvalues rfl

theorem hamiltonian_diagonal (H : Operator V) (hH : H.IsSymmetric) :
    diagonal (hamiltonianBasis H hH) (hamiltonianEnergies H hH) = H := by
  apply entry_ext (hamiltonianBasis H hH)
  intro i j
  rw [entry_diagonal]
  simp [entry, hamiltonianBasis, hamiltonianEnergies, hH.apply_eigenvectorBasis,
    inner_smul_right, OrthonormalBasis.inner_eq_ite]
  split_ifs with h
  · subst j; rfl
  · rfl

@[simp] theorem entry_diagonal_mul (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (i j : ι) :
    entry b (diagonal b e * A) i j = (e i : ℂ) * entry b A i j := by
  rw [entry_mul]
  simp [entry_diagonal]

@[simp] theorem entry_mul_diagonal (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (i j : ι) :
    entry b (A * diagonal b e) i j = entry b A i j * (e j : ℂ) := by
  rw [entry_mul]
  simp [entry_diagonal]

theorem entry_eq_zero_of_commute (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : Commute (diagonal b e) A) (i j : ι)
    (hne : e i ≠ e j) : entry b A i j = 0 := by
  have h := congrArg (fun T => entry b T i j) hA.eq
  simp only [entry_diagonal_mul, entry_mul_diagonal] at h
  have hc : (e i : ℂ) - (e j : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  apply (mul_eq_zero.mp (show ((e i : ℂ) - (e j : ℂ)) * entry b A i j = 0 by linear_combination h)).resolve_left hc

theorem frequencyComponent_mul_right (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A B : Operator V) (hB : Commute (diagonal b e) B) (ω : ℝ) :
    frequencyComponent b e (A * B) ω = frequencyComponent b e A ω * B := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_mul]
  have hs : (if e j-e i = ω then ∑ k, entry b A i k * entry b B k j else 0) =
      ∑ k, if e j-e i = ω then entry b A i k * entry b B k j else 0 := by
    split_ifs <;> simp
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  by_cases he : e k = e j
  · simp only [he]
    split_ifs <;> simp
  · rw [entry_eq_zero_of_commute b e B hB k j he]
    split_ifs <;> simp

theorem frequencyComponent_mul_left (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A B : Operator V) (hA : Commute (diagonal b e) A) (ω : ℝ) :
    frequencyComponent b e (A * B) ω = A * frequencyComponent b e B ω := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_mul]
  have hs : (if e j-e i = ω then ∑ k, entry b A i k * entry b B k j else 0) =
      ∑ k, if e j-e i = ω then entry b A i k * entry b B k j else 0 := by
    split_ifs <;> simp
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  by_cases he : e i = e k
  · simp only [he]
    split_ifs <;> simp
  · rw [entry_eq_zero_of_commute b e A hA i k he]
    split_ifs <;> simp

@[simp] theorem frequencyComponent_zero (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (ω : ℝ) : frequencyComponent b e 0 ω = 0 := by
  apply entry_ext b
  intro i j
  simp

theorem frequencyComponent_sub (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A B : Operator V) (ω : ℝ) :
    frequencyComponent b e (A - B) ω = frequencyComponent b e A ω -
      frequencyComponent b e B ω := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_sub]
  split_ifs <;> simp

/-- Commutation with the Hamiltonian means commutation with whole energy spaces,
including rotations between basis vectors of a degenerate eigenspace. -/
theorem energyProjector_commute (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : Commute (diagonal b e) A) (E : ℝ) :
    Commute (energyProjector b e E) A := by
  change energyProjector b e E * A = A * energyProjector b e E
  apply entry_ext b
  intro i j
  simp only [entry_mul, entry_energyProjector]
  simp only [ite_and, ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases he : e i = e j
  · simp [he]
  · rw [entry_eq_zero_of_commute b e A hA i j he]
    simp

theorem frequencyComponent_commutator (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (ω : ℝ) :
    diagonal b e * frequencyComponent b e A ω -
      frequencyComponent b e A ω * diagonal b e =
      (-ω : ℂ) • frequencyComponent b e A ω := by
  apply entry_ext b
  intro i j
  simp only [entry_sub, entry_diagonal_mul, entry_mul_diagonal,
    entry_smul, entry_frequencyComponent]
  split_ifs with h
  · have hc : (e j : ℂ) - (e i : ℂ) = (ω : ℂ) := by exact_mod_cast h
    push_cast
    linear_combination -(entry b A i j) * hc
  · simp

/-- Protection transfers through grouped frequency extraction without selecting
rank-one projectors inside a degenerate eigenspace. -/
theorem frequencyComponent_protected (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A O P : Operator V) (hO : Commute (diagonal b e) O)
    (hP : Commute (diagonal b e) P) (h : (A * O - O * A) * P = 0) (ω : ℝ) :
    (frequencyComponent b e A ω * O - O * frequencyComponent b e A ω) * P = 0 := by
  have he := congrArg (fun T => frequencyComponent b e T ω) h
  rw [frequencyComponent_mul_right b e _ P hP,
    frequencyComponent_sub, frequencyComponent_mul_right b e A O hO,
    frequencyComponent_mul_left b e O A hO, frequencyComponent_zero] at he
  exact he

theorem diagonal_apply_basis (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (i : ι) :
    diagonal b e (b i) = (e i : ℂ) • b i := by
  simp [diagonal, matrixUnit, LinearMap.sum_apply, InnerProductSpace.rankOne_apply,
    b.inner_eq_ite]

theorem diagonal_apply_repr (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (x : V) (i : ι) :
    b.repr (diagonal b e x) i = (e i : ℂ) * b.repr x i := by
  have he : diagonal b e x = ∑ j, b.repr x j • diagonal b e (b j) := by
    simpa only [map_sum, map_smul] using (congrArg (diagonal b e) (b.sum_repr x)).symm
  rw [he]
  simp only [OrthonormalBasis.repr_apply_apply, inner_sum, inner_smul_right,
    diagonal_apply_basis, b.inner_eq_ite]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji; simp [Ne.symm hji]
  · simp

theorem energyProjector_apply_repr (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (E : ℝ) (x : V) (i : ι) :
    b.repr (energyProjector b e E x) i = if e i = E then b.repr x i else 0 := by
  have he : energyProjector b e E x = ∑ j, b.repr x j • energyProjector b e E (b j) := by
    simpa only [map_sum, map_smul] using (congrArg (energyProjector b e E) (b.sum_repr x)).symm
  rw [he]
  simp only [OrthonormalBasis.repr_apply_apply, inner_sum, inner_smul_right]
  change (∑ j, inner ℂ (b j) x * entry b (energyProjector b e E) i j) = _
  simp only [entry_energyProjector]
  rw [Finset.sum_eq_single i]
  · split_ifs <;> simp_all
  · intro j _ hji; simp [Ne.symm hji]
  · simp

/-- Every vector of an eigenspace, not only selected basis vectors, has the
expected energy-projector action. -/
theorem energyProjector_apply_eigenvector (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (x : V) (lam E : ℝ) (hx : diagonal b e x = (lam : ℂ) • x) :
    energyProjector b e E x = if lam = E then x else 0 := by
  apply b.repr.injective
  ext i
  have h := congrArg (fun y => b.repr y i) hx
  rw [diagonal_apply_repr] at h
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at h
  have hz (he : e i ≠ lam) : b.repr x i = 0 := by
    have hne : (e i : ℂ) - (lam : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast he)
    exact (mul_eq_zero.mp (show ((e i : ℂ)-(lam : ℂ))*b.repr x i = 0 by
      linear_combination h)).resolve_left hne
  rw [energyProjector_apply_repr]
  by_cases hlam : lam = E
  · subst E
    by_cases he : e i = lam
    · simp [he]
    · simp [he, hz he]
  · by_cases he : e i = E
    · have hne : e i ≠ lam := by intro h; exact hlam (h.symm.trans he)
      simp [hlam, he, hz hne]
    · simp [hlam, he]

theorem energyProjector_fixed_iff (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (x : V) (E : ℝ) :
    energyProjector b e E x = x ↔ diagonal b e x = (E : ℂ) • x := by
  constructor
  · intro hx
    have h := congrArg (fun A : Operator V => A x) (diagonal_mul_projector b e E)
    change diagonal b e (energyProjector b e E x) = (E : ℂ) • energyProjector b e E x at h
    rw [hx] at h
    exact h
  · intro hx
    simpa using energyProjector_apply_eigenvector b e x E E hx

/-- Energy projectors depend on the Hamiltonian, not on an eigenbasis choice. -/
theorem energyProjector_basis_independent {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : OrthonormalBasis ι' ℂ V) (f : ι' → ℝ)
    (hH : diagonal b e = diagonal c f) (E : ℝ) :
    energyProjector b e E = energyProjector c f E := by
  apply c.toBasis.ext
  intro i
  change energyProjector b e E (c i) = energyProjector c f E (c i)
  have hv : diagonal b e (c i) = (f i : ℂ) • c i := by
    rw [hH]; exact diagonal_apply_basis c f i
  rw [energyProjector_apply_eigenvector b e (c i) (f i) E hv,
    energyProjector_apply_eigenvector c f (c i) (f i) E (diagonal_apply_basis c f i)]

theorem entry_projector_mul (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (E : ℝ) (A : Operator V) (i j : ι) :
    entry b (energyProjector b e E * A) i j = if e i = E then entry b A i j else 0 := by
  rw [entry_mul]
  simp only [entry_energyProjector]
  rw [Finset.sum_eq_single i]
  · split_ifs <;> simp_all
  · intro k _ hki; simp [Ne.symm hki]
  · simp

theorem entry_mul_projector (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (E : ℝ) (A : Operator V) (i j : ι) :
    entry b (A * energyProjector b e E) i j = if e j = E then entry b A i j else 0 := by
  rw [entry_mul]
  simp only [entry_energyProjector]
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp_all
  · intro k _ hkj; simp [hkj]
  · simp

/-- The exact grouped spectral-block characterization. -/
theorem frequencyComponent_block (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (E F ω : ℝ) :
    energyProjector b e E * frequencyComponent b e A ω * energyProjector b e F =
      if F-E = ω then energyProjector b e E * A * energyProjector b e F else 0 := by
  apply entry_ext b
  intro i j
  simp only [entry_mul_projector, entry_projector_mul, entry_frequencyComponent,
    entry_ite, entry_zero]
  by_cases hi : e i = E <;> by_cases hj : e j = F <;> simp [hi,hj]

theorem sum_projector_blocks (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) :
    (∑ E ∈ energyValues e, ∑ F ∈ energyValues e,
      energyProjector b e E * A * energyProjector b e F) = A := by
  simp only [← Finset.mul_sum, sum_energyProjector, mul_one, ← Finset.sum_mul, one_mul]

/-- Equal-frequency blocks are summed before constructing any quadratic jump. -/
theorem frequencyComponent_eq_projector_sum (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (ω : ℝ) :
    frequencyComponent b e A ω = ∑ E ∈ energyValues e, ∑ F ∈ energyValues e,
      if F-E = ω then energyProjector b e E * A * energyProjector b e F else 0 := by
  conv_lhs => rw [← sum_projector_blocks b e (frequencyComponent b e A ω)]
  simp only [frequencyComponent_block]

theorem diagonal_adjoint (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    LinearMap.adjoint (diagonal b e) = diagonal b e := by
  apply entry_ext b
  intro i j
  rw [entry_adjoint]
  by_cases hij : i = j
  · subst j; simp
  · simp [entry_diagonal, hij, Ne.symm hij]

theorem diagonal_symmetric (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    (diagonal b e).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (diagonal_adjoint b e)

end
end QEC.Semantics.Davies
