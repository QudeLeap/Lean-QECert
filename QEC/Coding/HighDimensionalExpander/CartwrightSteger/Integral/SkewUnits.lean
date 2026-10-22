import QEC.Coding.HighDimensionalExpander.CartwrightSteger.Integral.SkewRing

/-!
# Units of the Cartwright--Steger skew Laurent ring

This module proves the unit classification used in LSV05b Proposition 4.8:
every unit of `F_(q^d){z, z⁻¹}` is a single skew monomial `c z^n`.
The proof uses the extreme exponents of the finite support and proves that
the corresponding twisted-convolution coefficients cannot cancel.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

open Multiplicative SkewMonoidAlgebra

/-- Integer exponents occurring in a skew Laurent polynomial. -/
noncomputable def skewLaurentIntSupport
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) : Finset ℤ :=
  f.support.map ⟨Multiplicative.toAdd, Multiplicative.toAdd.injective⟩

@[simp] theorem mem_skewLaurentIntSupport
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) (n : ℤ) :
    n ∈ skewLaurentIntSupport P r f ↔
      Multiplicative.ofAdd n ∈ f.support := by
  simp [skewLaurentIntSupport]

theorem skewLaurentIntSupport_nonempty
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    (skewLaurentIntSupport P r f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hs : f.support = ∅ := by
    apply Finset.map_eq_empty.mp
    exact hempty
  exact hf (SkewMonoidAlgebra.support_eq_empty.mp hs)

theorem exists_skewLaurent_support_max
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    ∃ a : ℤ, Multiplicative.ofAdd a ∈ f.support ∧
      ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a := by
  let s := skewLaurentIntSupport P r f
  have hs : s.Nonempty := skewLaurentIntSupport_nonempty P r hf
  let a := s.max' hs
  refine ⟨a, ?_, ?_⟩
  · exact (mem_skewLaurentIntSupport P r f a).mp (s.max'_mem hs)
  · intro x hx
    exact s.le_max' x ((mem_skewLaurentIntSupport P r f x).mpr hx)

theorem exists_skewLaurent_support_min
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    ∃ a : ℤ, Multiplicative.ofAdd a ∈ f.support ∧
      ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x := by
  let s := skewLaurentIntSupport P r f
  have hs : s.Nonempty := skewLaurentIntSupport_nonempty P r hf
  let a := s.min' hs
  refine ⟨a, ?_, ?_⟩
  · exact (mem_skewLaurentIntSupport P r f a).mp (s.min'_mem hs)
  · intro x hx
    exact s.min'_le x ((mem_skewLaurentIntSupport P r f x).mpr hx)

theorem skewLaurent_coeff_mul_at_support_max_ne_zero
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmaxa : ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hmaxb : ∀ x, Multiplicative.ofAdd x ∈ g.support → x ≤ b) :
    (f * g).coeff (Multiplicative.ofAdd (a + b)) ≠ 0 := by
  rw [SkewMonoidAlgebra.coeff_mul_left,
    SkewMonoidAlgebra.sum_def']
  rw [Finset.sum_eq_single (Multiplicative.ofAdd a)]
  · have hfa : f.coeff (Multiplicative.ofAdd a) ≠ 0 :=
      SkewMonoidAlgebra.mem_support_iff.mp ha
    have hgb : g.coeff (Multiplicative.ofAdd b) ≠ 0 :=
      SkewMonoidAlgebra.mem_support_iff.mp hb
    have hact : Multiplicative.ofAdd a •
        g.coeff (Multiplicative.ofAdd b) ≠ 0 := by
      change constantFrobeniusZRingAction P r (Multiplicative.ofAdd a)
        (g.coeff (Multiplicative.ofAdd b)) ≠ 0
      exact (map_ne_zero (constantFrobeniusZRingAction P r
        (Multiplicative.ofAdd a))).mpr hgb
    simpa using mul_ne_zero hfa hact
  · intro x hx hxa
    let xInt := Multiplicative.toAdd x
    have hxrepr : Multiplicative.ofAdd xInt = x := rfl
    have hxmem : Multiplicative.ofAdd xInt ∈ f.support := hxrepr ▸ hx
    have hxlt : xInt < a := lt_of_le_of_ne (hmaxa xInt hxmem) (by
      intro h
      apply hxa
      rw [← hxrepr]
      exact congrArg Multiplicative.ofAdd h)
    have hnot : Multiplicative.ofAdd (-xInt + (a + b)) ∉ g.support := by
      intro hmem
      have hle := hmaxb (-xInt + (a + b)) hmem
      omega
    have heq : x⁻¹ * Multiplicative.ofAdd (a + b) =
        Multiplicative.ofAdd (-xInt + (a + b)) := by
      apply Multiplicative.toAdd.injective
      simp [xInt]
    rw [heq, SkewMonoidAlgebra.notMem_support_iff.mp hnot]
    simp
  · exact fun hnot => (hnot ha).elim

theorem skewLaurent_support_max_mul
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmaxa : ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hmaxb : ∀ x, Multiplicative.ofAdd x ∈ g.support → x ≤ b) :
    Multiplicative.ofAdd (a + b) ∈ (f * g).support ∧
      ∀ x, Multiplicative.ofAdd x ∈ (f * g).support → x ≤ a + b := by
  constructor
  · exact SkewMonoidAlgebra.mem_support_iff.mpr
      (skewLaurent_coeff_mul_at_support_max_ne_zero P r
        ha hmaxa hb hmaxb)
  · intro x hx
    have hx' := SkewMonoidAlgebra.support_mul f g hx
    rw [Finset.mem_mul] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := hx'
    have hueq : u = Multiplicative.ofAdd u.toAdd := rfl
    have hveq : v = Multiplicative.ofAdd v.toAdd := rfl
    have hule := hmaxa u.toAdd (hueq ▸ hu)
    have hvle := hmaxb v.toAdd (hveq ▸ hv)
    have hsum := congrArg Multiplicative.toAdd huv
    change u.toAdd + v.toAdd = x at hsum
    omega

theorem skewLaurent_coeff_mul_at_support_min_ne_zero
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmina : ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hminb : ∀ x, Multiplicative.ofAdd x ∈ g.support → b ≤ x) :
    (f * g).coeff (Multiplicative.ofAdd (a + b)) ≠ 0 := by
  rw [SkewMonoidAlgebra.coeff_mul_left,
    SkewMonoidAlgebra.sum_def']
  rw [Finset.sum_eq_single (Multiplicative.ofAdd a)]
  · have hfa : f.coeff (Multiplicative.ofAdd a) ≠ 0 :=
      SkewMonoidAlgebra.mem_support_iff.mp ha
    have hgb : g.coeff (Multiplicative.ofAdd b) ≠ 0 :=
      SkewMonoidAlgebra.mem_support_iff.mp hb
    have hact : Multiplicative.ofAdd a •
        g.coeff (Multiplicative.ofAdd b) ≠ 0 := by
      change constantFrobeniusZRingAction P r (Multiplicative.ofAdd a)
        (g.coeff (Multiplicative.ofAdd b)) ≠ 0
      exact (map_ne_zero (constantFrobeniusZRingAction P r
        (Multiplicative.ofAdd a))).mpr hgb
    simpa using mul_ne_zero hfa hact
  · intro x hx hxa
    let xInt := Multiplicative.toAdd x
    have hxrepr : Multiplicative.ofAdd xInt = x := rfl
    have hxmem : Multiplicative.ofAdd xInt ∈ f.support := hxrepr ▸ hx
    have hxgt : a < xInt := lt_of_le_of_ne (hmina xInt hxmem) (by
      intro h
      apply hxa
      rw [← hxrepr]
      exact congrArg Multiplicative.ofAdd h.symm)
    have hnot : Multiplicative.ofAdd (-xInt + (a + b)) ∉ g.support := by
      intro hmem
      have hle := hminb (-xInt + (a + b)) hmem
      omega
    have heq : x⁻¹ * Multiplicative.ofAdd (a + b) =
        Multiplicative.ofAdd (-xInt + (a + b)) := by
      apply Multiplicative.toAdd.injective
      simp [xInt]
    rw [heq, SkewMonoidAlgebra.notMem_support_iff.mp hnot]
    simp
  · exact fun hnot => (hnot ha).elim

theorem skewLaurent_support_min_mul
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmina : ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hminb : ∀ x, Multiplicative.ofAdd x ∈ g.support → b ≤ x) :
    Multiplicative.ofAdd (a + b) ∈ (f * g).support ∧
      ∀ x, Multiplicative.ofAdd x ∈ (f * g).support → a + b ≤ x := by
  constructor
  · exact SkewMonoidAlgebra.mem_support_iff.mpr
      (skewLaurent_coeff_mul_at_support_min_ne_zero P r
        ha hmina hb hminb)
  · intro x hx
    have hx' := SkewMonoidAlgebra.support_mul f g hx
    rw [Finset.mem_mul] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := hx'
    have hueq : u = Multiplicative.ofAdd u.toAdd := rfl
    have hveq : v = Multiplicative.ofAdd v.toAdd := rfl
    have hule := hmina u.toAdd (hueq ▸ hu)
    have hvle := hminb v.toAdd (hveq ▸ hv)
    have hsum := congrArg Multiplicative.toAdd huv
    change u.toAdd + v.toAdd = x at hsum
    omega

/-- Every unit of the actual skew Laurent ring is a nonzero constant times
one integral power of `z`. -/
theorem exists_constant_zpow_of_skewLaurent_unit
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerSkewLaurentRing P r)ˣ) :
    ∃ c : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      (u : CartwrightStegerSkewLaurentRing P r) =
        SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
          (c : ConstantExtension P r) := by
  let f : CartwrightStegerSkewLaurentRing P r := u
  let g : CartwrightStegerSkewLaurentRing P r := ↑u⁻¹
  have hf : f ≠ 0 := Units.ne_zero u
  have hg : g ≠ 0 := Units.ne_zero u⁻¹
  obtain ⟨a, ha, hmaxa⟩ := exists_skewLaurent_support_max P r hf
  obtain ⟨b, hb, hmaxb⟩ := exists_skewLaurent_support_max P r hg
  obtain ⟨c, hc, hminc⟩ := exists_skewLaurent_support_min P r hf
  obtain ⟨d, hd, hmind⟩ := exists_skewLaurent_support_min P r hg
  have hprod : f * g = 1 := by
    change (u : CartwrightStegerSkewLaurentRing P r) *
      (↑u⁻¹ : CartwrightStegerSkewLaurentRing P r) = 1
    change ↑(u * u⁻¹) = (1 : CartwrightStegerSkewLaurentRing P r)
    rw [mul_inv_cancel]
    rfl
  have hmaxProd := (skewLaurent_support_max_mul P r
    ha hmaxa hb hmaxb).1
  have hminProd := (skewLaurent_support_min_mul P r
    hc hminc hd hmind).1
  rw [hprod, SkewMonoidAlgebra.support_one] at hmaxProd hminProd
  have hab : a + b = 0 := by
    have heq : Multiplicative.ofAdd (a + b) = 1 :=
      Finset.mem_singleton.mp hmaxProd
    exact congrArg Multiplicative.toAdd heq
  have hcd : c + d = 0 := by
    have heq : Multiplicative.ofAdd (c + d) = 1 :=
      Finset.mem_singleton.mp hminProd
    exact congrArg Multiplicative.toAdd heq
  have hca : c ≤ a := hminc a ha
  have hdb : d ≤ b := hmind b hb
  have hac : a = c := by omega
  subst c
  have hsupp : f.support = {Multiplicative.ofAdd a} := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxrepr : x = Multiplicative.ofAdd x.toAdd := rfl
      have hle := hmaxa x.toAdd (hxrepr ▸ hx)
      have hge := hminc x.toAdd (hxrepr ▸ hx)
      have hxa : x.toAdd = a := by omega
      apply Finset.mem_singleton.mpr
      apply Multiplicative.toAdd.injective
      exact hxa
    · exact Finset.singleton_subset_iff.mpr ha
  have hcoeff : f.coeff (Multiplicative.ofAdd a) ≠ 0 :=
    SkewMonoidAlgebra.mem_support_iff.mp ha
  let coeffUnit : (ConstantExtension P r)ˣ :=
    Units.mk0 (f.coeff (Multiplicative.ofAdd a)) hcoeff
  refine ⟨coeffUnit, a, ?_⟩
  apply SkewMonoidAlgebra.ext
  intro x
  by_cases hx : x = Multiplicative.ofAdd a
  · subst x
    rw [SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
    rfl
  · have hxnot : x ∉ f.support := by
      rw [hsupp]
      intro hmem
      exact hx (Finset.mem_singleton.mp hmem)
    rw [SkewMonoidAlgebra.notMem_support_iff.mp hxnot]
    rw [SkewMonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hx)]

end QEC.Coding.HighDimensionalExpander.CartwrightSteger
