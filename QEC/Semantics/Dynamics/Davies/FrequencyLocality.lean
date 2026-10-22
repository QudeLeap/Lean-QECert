import QEC.Semantics.Dynamics.Davies.Hamiltonian
import QEC.Semantics.Core.SubsystemOperatorAlgebra

/-! # Constructive finite spectral filtering and commuting-remainder locality -/

namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Source-minus-target energy convention: eigenoperators have eigenvalue +ω. -/
def energyDifference (H A : Operator V) : Operator V := A*H-H*A

theorem entry_energyDifference (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (i j : ι) :
    entry b (energyDifference (diagonal b e) A) i j =
      ((e j-e i : ℝ) : ℂ) * entry b A i j := by
  simp only [energyDifference, entry_sub, entry_mul_diagonal, entry_diagonal_mul]
  push_cast
  ring

theorem frequencyComponent_smul (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : ℂ) (A : Operator V) (ω : ℝ) :
    frequencyComponent b e (c • A) ω = c • frequencyComponent b e A ω := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_smul]
  split_ifs <;> simp

theorem frequencyComponent_sum {κ : Type*} (s : Finset κ)
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V) (ω : ℝ) :
    frequencyComponent b e (∑ k ∈ s, A k) ω =
      ∑ k ∈ s, frequencyComponent b e (A k) ω := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_sum]
  split_ifs <;> simp

theorem frequencyComponent_of_not_mem (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (ω : ℝ) (hω : ω ∉ frequencies e) :
    frequencyComponent b e A ω = 0 := by
  apply entry_ext b
  intro i j
  have h : e j-e i ≠ ω := fun he => hω ((mem_frequencies e ω).2 ⟨i,j,he⟩)
  simp [entry_frequencyComponent, h]

/-- Spectral uniqueness for any actual eigenoperator, without a chosen common basis. -/
theorem frequencyComponent_of_eigenoperator (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (freq ω : ℝ) (hA : energyDifference (diagonal b e) A = (freq : ℂ) • A) :
    frequencyComponent b e A ω = if freq=ω then A else 0 := by
  apply entry_ext b
  intro i j
  have he := congrArg (fun B => entry b B i j) hA
  rw [entry_energyDifference, entry_smul] at he
  have hz : e j-e i ≠ freq → entry b A i j = 0 := by
    intro h
    have hn : ((e j-e i : ℝ) : ℂ) - (freq : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    exact (mul_eq_zero.mp (show (((e j-e i : ℝ) : ℂ)-(freq : ℂ))*entry b A i j=0 by
      linear_combination he)).resolve_left hn
  simp only [entry_frequencyComponent, entry_ite, entry_zero]
  split_ifs with hgap hl hfreq
  · rfl
  · exact hz (by intro h; exact hl (h.symm.trans hgap))
  · exact (hz (by simpa [hfreq] using hgap)).symm
  · rfl

/-- Actual coherent component of a self-adjoint Hamiltonian, at every real frequency. -/
def actualFrequency (H : Operator V) (hH : H.IsSymmetric) (A : Operator V) (ω : ℝ) :
    Operator V := frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω

theorem actualFrequency_energyDifference (H : Operator V) (hH : H.IsSymmetric)
    (A : Operator V) (ω : ℝ) :
    energyDifference H (actualFrequency H hH A ω) = (ω : ℂ) • actualFrequency H hH A ω := by
  have h := frequencyComponent_commutator (hamiltonianBasis H hH)
    (hamiltonianEnergies H hH) A ω
  rw [hamiltonian_diagonal] at h
  change _ = (ω : ℂ) • frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω
  unfold energyDifference actualFrequency
  rw [show frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω * H -
      H * frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω =
      -(H * frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω -
      frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω * H) by abel]
  rw [h]
  simp

/-- Terms commuting with both the local Hamiltonian and coupling do not affect its frequencies. -/
theorem actualFrequency_add_commuting_remainder (L R A : Operator V)
    (hL : L.IsSymmetric) (hH : (L+R).IsSymmetric)
    (hLR : Commute L R) (hRA : Commute R A) (ω : ℝ) :
    actualFrequency (L+R) hH A ω = actualFrequency L hL A ω := by
  let b := hamiltonianBasis L hL
  let e := hamiltonianEnergies L hL
  have hR : Commute (diagonal b e) R := by simpa [b,e,hamiltonian_diagonal] using hLR
  have hc : ∀ freq, Commute R (frequencyComponent b e A freq) := by
    intro freq
    have h := congrArg (fun B => frequencyComponent b e B freq) hRA.eq
    rw [frequencyComponent_mul_left b e R A hR,
      frequencyComponent_mul_right b e A R hR] at h
    exact h
  have heig : ∀ freq, energyDifference (L+R) (frequencyComponent b e A freq) =
      (freq : ℂ) • frequencyComponent b e A freq := by
    intro freq
    have h := actualFrequency_energyDifference L hL A freq
    change energyDifference L (frequencyComponent b e A freq) = _ at h
    simp only [energyDifference, mul_add, add_mul] at h ⊢
    rw [(hc freq).eq]
    convert h using 1 <;> abel
  have hsum := sum_frequencyComponent b e A
  unfold actualFrequency
  conv_lhs => rw [← hsum]
  rw [frequencyComponent_sum]
  have hselect : ∀ freq,
      frequencyComponent (hamiltonianBasis (L+R) hH) (hamiltonianEnergies (L+R) hH)
        (frequencyComponent b e A freq) ω =
        if freq=ω then frequencyComponent b e A freq else 0 := by
    intro freq
    apply frequencyComponent_of_eigenoperator
    simpa only [hamiltonian_diagonal] using heig freq
  simp_rw [hselect]
  by_cases hw : ω ∈ frequencies e
  · let w : Frequency e := ⟨ω,hw⟩
    rw [Finset.sum_eq_single w]
    · simp [w,b,e]
    · intro k _ hk
      have hn : k.val ≠ ω := fun h => hk (Subtype.ext h)
      simp [hn]
    · simp
  · rw [frequencyComponent_of_not_mem b e A ω hw]
    apply Finset.sum_eq_zero
    intro k _
    have hn : k.val ≠ ω := fun h => hw (h ▸ k.property)
    simp [hn]

theorem actualFrequency_of_eigenoperator (H A : Operator V) (hH : H.IsSymmetric)
    (freq ω : ℝ) (hA : energyDifference H A = (freq : ℂ) • A) :
    actualFrequency H hH A ω = if freq=ω then A else 0 := by
  apply frequencyComponent_of_eigenoperator
  simpa only [hamiltonian_diagonal] using hA

theorem actualFrequency_add (H A B : Operator V) (hH : H.IsSymmetric) (ω : ℝ) :
    actualFrequency H hH (A+B) ω = actualFrequency H hH A ω + actualFrequency H hH B ω :=
  frequencyComponent_add _ _ _ _ _

theorem actualFrequency_zeroHamiltonian (A : Operator V) (ω : ℝ) :
    actualFrequency 0 LinearMap.IsSymmetric.zero A ω = if 0=ω then A else 0 := by
  apply actualFrequency_of_eigenoperator
  simp [energyDifference]

/-- A scalar-normalized commutator step which removes one unwanted frequency. -/
def frequencyFilterStep (H : Operator V) (ω ν : ℝ) (A : Operator V) : Operator V :=
  (((ω-ν : ℝ) : ℂ)⁻¹) • (energyDifference H A - (ν : ℂ) • A)

def frequencyFilter (H : Operator V) (ω : ℝ) (l : List ℝ) (A : Operator V) : Operator V :=
  l.foldr (frequencyFilterStep H ω) A

theorem entry_frequencyFilter (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (ω : ℝ) (l : List ℝ) (A : Operator V) (i j : ι) :
    entry b (frequencyFilter (diagonal b e) ω l A) i j =
      (l.map (fun ν => (((ω-ν : ℝ) : ℂ)⁻¹) * ((e j-e i-ν : ℝ) : ℂ))).prod *
        entry b A i j := by
  induction l with
  | nil => simp [frequencyFilter]
  | cons ν l ih =>
    change entry b (frequencyFilterStep (diagonal b e) ω ν
      (frequencyFilter (diagonal b e) ω l A)) i j = _
    simp only [frequencyFilterStep, entry_smul, entry_sub, entry_energyDifference,
      ih, List.map_cons, List.prod_cons]
    push_cast
    ring

/-- Explicit finite interpolation recovers the coherent component, including degeneracies. -/
theorem frequencyFilter_eq_component (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (ω : ℝ) (hω : ω ∈ frequencies e) (A : Operator V) :
    frequencyFilter (diagonal b e) ω ((frequencies e).erase ω).toList A =
      frequencyComponent b e A ω := by
  apply entry_ext b
  intro i j
  rw [entry_frequencyFilter, entry_frequencyComponent]
  by_cases hg : e j-e i = ω
  · rw [if_pos hg]
    have hp : (((frequencies e).erase ω).toList.map
        (fun ν => (((ω-ν : ℝ) : ℂ)⁻¹) * ((e j-e i-ν : ℝ) : ℂ))).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      obtain ⟨ν,hν,rfl⟩ := List.mem_map.mp hx
      have hn : ν ≠ ω := (Finset.mem_erase.mp (Finset.mem_toList.mp hν)).1
      rw [hg]
      exact inv_mul_cancel₀ (by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hn)))
    rw [hp, one_mul]
  · rw [if_neg hg]
    have hm : e j-e i ∈ (frequencies e).erase ω :=
      Finset.mem_erase.mpr ⟨hg,(mem_frequencies _ _).2 ⟨i,j,rfl⟩⟩
    have hz : (0 : ℂ) ∈ (((frequencies e).erase ω).toList.map
        (fun ν => (((ω-ν : ℝ) : ℂ)⁻¹) * ((e j-e i-ν : ℝ) : ℂ))) := by
      apply List.mem_map.mpr
      exact ⟨e j-e i, Finset.mem_toList.mpr hm, by simp⟩
    rw [List.prod_eq_zero hz, zero_mul]

variable {q : Type} [Fintype q] [DecidableEq q]

theorem frequencyFilter_supported (S : FiniteSubsystem q)
    (H A : Operator (Qubit.QubitRegister q)) (ω : ℝ) (l : List ℝ)
    (hH : S.OperatorSupportedOnRegister H) (hA : S.OperatorSupportedOnRegister A) :
    S.OperatorSupportedOnRegister (frequencyFilter H ω l A) := by
  induction l with
  | nil => exact hA
  | cons ν l ih =>
    exact S.supported_smul _ (S.supported_sub
      (S.supported_sub (S.supported_mul ih hH) (S.supported_mul hH ih))
      (S.supported_smul _ ih))

/-- Real tensor support of a spectral component, with the local witness constructed by filtering. -/
theorem actualFrequency_supported (S : FiniteSubsystem q)
    (H A : Operator (Qubit.QubitRegister q)) (hH : H.IsSymmetric)
    (hsH : S.OperatorSupportedOnRegister H) (hsA : S.OperatorSupportedOnRegister A) (ω : ℝ) :
    S.OperatorSupportedOnRegister (actualFrequency H hH A ω) := by
  let b := hamiltonianBasis H hH
  let e := hamiltonianEnergies H hH
  by_cases hw : ω ∈ frequencies e
  · have he := frequencyFilter_eq_component b e ω hw A
    rw [hamiltonian_diagonal] at he
    rw [actualFrequency, ← he]
    exact frequencyFilter_supported S H A ω _ hsH hsA
  · have he := frequencyComponent_of_not_mem b e A ω hw
    change S.OperatorSupportedOnRegister (frequencyComponent b e A ω)
    rw [he]
    exact S.supported_zero

end
end QEC.Semantics.Davies
