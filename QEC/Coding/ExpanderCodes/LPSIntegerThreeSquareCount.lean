import QEC.Coding.ExpanderCodes.LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Elementary three-square counts for the actual LPS trace form

Three distinct integer circle points have a nonzero integer chord determinant.
The proved circumradius identity rules out three points in a box of width L
when 2*L^6<n. In the nonnegative quadrant, circle monotonicity gives an
injective rank for occupied boxes. Actual finite fibers therefore have at
most two points. Splitting at n=2*K^6 gives at most 6*K^3 nonnegative two-square
solutions whenever n<=K^8, and slicing by the third coordinate gives at most
12*K^7 nonnegative three-square solutions. The actual sign fibers have at
most eight points, giving the integer bound 96*K^7.

The terminal consumer bounds a fixed-first-coordinate fiber of the actual
lpsTraceQuadraticShell q n by 96*K^7 when n<=4*q^2*K^8. Its remaining three
coordinates are injected into the proved integer three-square count, with
the common represented integer derived from the native quadratic form.
No cardinality or spectral result is assumed.

This is an internally derived arithmetic prerequisite motivated by the LPS
return-count argument in Davidoff--Sarnak--Valette, section 4.4, printed
pages 125-128. The bound is weaker than their sharp three-square estimate;
it does not realize that sharper estimate or a Ramanujan theorem. Actual
first-coordinate congruence counts, centered spectral multiplicity and a
trace-to-spectrum estimate remain separate obligations. Any later use of
spectral amplification also requires its full operator and coding proofs.
The exact PK22 arbitrary-finite-field, every-rate, explicit unbounded family
remains unproved. Parent issue449 remains OPEN and public records unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsIntegerCircleSquaredDistance (a b : ℤ × ℤ) : ℤ :=
  (b.1-a.1)^2 + (b.2-a.2)^2

def lpsIntegerCircleChordDet (a b c : ℤ × ℤ) : ℤ :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

lemma lpsIntegerCircleSquaredDistance_nonneg (a b : ℤ × ℤ) :
    0 ≤ lpsIntegerCircleSquaredDistance a b := by
  unfold lpsIntegerCircleSquaredDistance
  positivity

lemma lpsIntegerCircleSquaredDistance_eq_zero_iff (a b : ℤ × ℤ) :
    lpsIntegerCircleSquaredDistance a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hx : (b.1-a.1)^2=0 := by
      unfold lpsIntegerCircleSquaredDistance at h
      nlinarith [sq_nonneg (b.2-a.2)]
    have hy : (b.2-a.2)^2=0 := by
      unfold lpsIntegerCircleSquaredDistance at h
      nlinarith [sq_nonneg (b.1-a.1)]
    exact Prod.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm
      (sub_eq_zero.mp (sq_eq_zero_iff.mp hy)).symm
  · rintro rfl
    simp [lpsIntegerCircleSquaredDistance]

lemma lpsIntegerCircleSquaredDistance_le_of_abs_bounds
    (a b : ℤ × ℤ) (L : ℤ) (hL : 0 ≤ L)
    (hx : |b.1-a.1| ≤ L) (hy : |b.2-a.2| ≤ L) :
    lpsIntegerCircleSquaredDistance a b ≤ 2*L^2 := by
  have hx' : |b.1-a.1|^2 ≤ L^2 := (sq_le_sq₀ (abs_nonneg _) hL).2 hx
  have hy' : |b.2-a.2|^2 ≤ L^2 := (sq_le_sq₀ (abs_nonneg _) hL).2 hy
  unfold lpsIntegerCircleSquaredDistance
  nlinarith [sq_abs (b.1-a.1),sq_abs (b.2-a.2)]

lemma lpsIntegerCircleChordCircumradius
    (a b c : ℤ × ℤ) (n : ℤ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n) :
    4*n*(lpsIntegerCircleChordDet a b c)^2 =
      lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
        lpsIntegerCircleSquaredDistance b c := by
  have hu : 2*(a.1*(b.1-a.1)+a.2*(b.2-a.2)) =
      -((b.1-a.1)^2+(b.2-a.2)^2) := by nlinarith [ha,hb]
  have hv : 2*(a.1*(c.1-a.1)+a.2*(c.2-a.2)) =
      -((c.1-a.1)^2+(c.2-a.2)^2) := by nlinarith [ha,hc]
  calc
    4*n*(lpsIntegerCircleChordDet a b c)^2 =
        (2*(a.1*(b.1-a.1)+a.2*(b.2-a.2)))^2 * ((c.1-a.1)^2+(c.2-a.2)^2) -
        2*(2*(a.1*(b.1-a.1)+a.2*(b.2-a.2))) *
          (2*(a.1*(c.1-a.1)+a.2*(c.2-a.2))) *
          ((b.1-a.1)*(c.1-a.1)+(b.2-a.2)*(c.2-a.2)) +
        (2*(a.1*(c.1-a.1)+a.2*(c.2-a.2)))^2 * ((b.1-a.1)^2+(b.2-a.2)^2) := by
      rw [← ha]
      unfold lpsIntegerCircleChordDet
      ring
    _ = lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
        lpsIntegerCircleSquaredDistance b c := by
      rw [hu,hv]
      unfold lpsIntegerCircleSquaredDistance
      ring

lemma lpsIntegerCircleThreeDistinct_det_ne_zero
    (a b c : ℤ × ℤ) (n : ℤ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    lpsIntegerCircleChordDet a b c ≠ 0 := by
  intro h
  have hprod := lpsIntegerCircleChordCircumradius a b c n ha hb hc
  have hp0 : lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
      lpsIntegerCircleSquaredDistance b c = 0 := by
    calc
      _ = 4*n*(lpsIntegerCircleChordDet a b c)^2 := hprod.symm
      _ = 0 := by rw [h]; ring
  exact (mul_ne_zero
    (mul_ne_zero ((lpsIntegerCircleSquaredDistance_eq_zero_iff a b).not.mpr hab)
      ((lpsIntegerCircleSquaredDistance_eq_zero_iff a c).not.mpr hac))
    ((lpsIntegerCircleSquaredDistance_eq_zero_iff b c).not.mpr hbc)) hp0

lemma lpsIntegerCircleThreeDistinct_distance_bound
    (a b c : ℤ × ℤ) (n L : ℤ) (hn : 0 ≤ n)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (habL : lpsIntegerCircleSquaredDistance a b ≤ 2*L^2)
    (hacL : lpsIntegerCircleSquaredDistance a c ≤ 2*L^2)
    (hbcL : lpsIntegerCircleSquaredDistance b c ≤ 2*L^2) : n ≤ 2*L^6 := by
  have hdet : 1 ≤ (lpsIntegerCircleChordDet a b c)^2 := by
    have := sq_pos_of_ne_zero (lpsIntegerCircleThreeDistinct_det_ne_zero a b c n ha hb hc hab hac hbc)
    omega
  have hleft : 4*n ≤ 4*n*(lpsIntegerCircleChordDet a b c)^2 := by
    calc
      4*n = 4*n*1 := by ring
      _ ≤ 4*n*(lpsIntegerCircleChordDet a b c)^2 := mul_le_mul_of_nonneg_left hdet (by omega)
  have hab0 := lpsIntegerCircleSquaredDistance_nonneg a b
  have hac0 := lpsIntegerCircleSquaredDistance_nonneg a c
  have hbc0 := lpsIntegerCircleSquaredDistance_nonneg b c
  have hprod : lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
      lpsIntegerCircleSquaredDistance b c ≤ 8*L^6 := by
    calc
      _ ≤ (2*L^2)*(2*L^2)*(2*L^2) := by
        gcongr
      _ = 8*L^6 := by ring
  nlinarith [lpsIntegerCircleChordCircumradius a b c n ha hb hc]

lemma lpsIntegerCircleThinBox_no_three_distinct
    (a b c : ℤ × ℤ) (n L : ℤ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hsmall : 2*L^6<n)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (habx : |b.1-a.1| ≤ L) (haby : |b.2-a.2| ≤ L)
    (hacx : |c.1-a.1| ≤ L) (hacy : |c.2-a.2| ≤ L)
    (hbcx : |c.1-b.1| ≤ L) (hbcy : |c.2-b.2| ≤ L) :
    a=b ∨ a=c ∨ b=c := by
  by_contra h
  push Not at h
  have hbound := lpsIntegerCircleThreeDistinct_distance_bound a b c n L hn ha hb hc h.1 h.2.1 h.2.2
    (lpsIntegerCircleSquaredDistance_le_of_abs_bounds a b L hL habx haby)
    (lpsIntegerCircleSquaredDistance_le_of_abs_bounds a c L hL hacx hacy)
    (lpsIntegerCircleSquaredDistance_le_of_abs_bounds b c L hL hbcx hbcy)
  omega

lemma lpsIntegerPositiveCircle_strict_antitone
    (x y x' y' n : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (h : x^2+y^2=n) (h' : x'^2+y'^2=n) (hxx : x<x') : y'<y := by
  have hxx' : x^2 < x'^2 := (sq_lt_sq₀ hx hx').2 hxx
  have hyy : y'^2 < y^2 := by nlinarith [h,h']
  exact (sq_lt_sq₀ hy' hy).1 hyy

lemma lpsNatPair_intCast_injective :
    Function.Injective (fun a : ℕ × ℕ => ((a.1 : ℤ), (a.2 : ℤ))) := by
  intro a b h
  apply Prod.ext
  · have hf : (a.1 : ℤ)=(b.1 : ℤ) := congrArg Prod.fst h
    exact_mod_cast hf
  · have hf : (a.2 : ℤ)=(b.2 : ℤ) := congrArg Prod.snd h
    exact_mod_cast hf

lemma lpsNatSameQuotient_abs_sub_le (a b L : ℕ) (hL : 0 < L)
    (h : a / L = b / L) : |(b : ℤ) - (a : ℤ)| ≤ (L : ℤ) := by
  have ea := Nat.mod_add_div a L
  have eb := Nat.mod_add_div b L
  have ha := Nat.mod_lt a hL
  have hb := Nat.mod_lt b hL
  rw [h] at ea
  exact abs_le.mpr ⟨by omega, by omega⟩

lemma lpsNatCircle_y_antitone (a b : ℕ × ℕ) (n : ℕ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hx : a.1 ≤ b.1) : b.2 ≤ a.2 := by
  by_contra h
  have hy : (a.2 : ℤ) < (b.2 : ℤ) := by exact_mod_cast (show a.2 < b.2 by omega)
  have haZ : (a.2 : ℤ)^2+(a.1 : ℤ)^2=(n : ℤ) := by exact_mod_cast (by simpa [add_comm] using ha)
  have hbZ : (b.2 : ℤ)^2+(b.1 : ℤ)^2=(n : ℤ) := by exact_mod_cast (by simpa [add_comm] using hb)
  have hxZ : (a.1 : ℤ) ≤ (b.1 : ℤ) := by exact_mod_cast hx
  have hlt := lpsIntegerPositiveCircle_strict_antitone (a.2 : ℤ) (a.1 : ℤ)
    (b.2 : ℤ) (b.1 : ℤ) (n : ℤ) (by positivity) (by positivity)
    (by positivity) (by positivity) haZ hbZ hy
  omega

def lpsNatCircleBoxRank (M L : ℕ) (a : ℕ × ℕ) : ℕ := a.1/L + (M-a.2/L)

lemma lpsNatCircleBoxRank_eq_imp_quotients_eq (a b : ℕ × ℕ) (n M L : ℕ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n)
    (haB : a.1/L ≤ M ∧ a.2/L ≤ M) (hbB : b.1/L ≤ M ∧ b.2/L ≤ M)
    (h : lpsNatCircleBoxRank M L a = lpsNatCircleBoxRank M L b) :
    a.1/L=b.1/L ∧ a.2/L=b.2/L := by
  unfold lpsNatCircleBoxRank at h
  rcases le_total a.1 b.1 with hab | hba
  · have hx : a.1/L ≤ b.1/L := Nat.div_le_div_right hab
    have hy : b.2/L ≤ a.2/L := Nat.div_le_div_right (lpsNatCircle_y_antitone a b n ha hb hab)
    constructor <;> omega
  · have hx : b.1/L ≤ a.1/L := Nat.div_le_div_right hba
    have hy : a.2/L ≤ b.2/L := Nat.div_le_div_right (lpsNatCircle_y_antitone b a n hb ha hba)
    constructor <;> omega

lemma lpsNatCircleBoxRank_fiber_card_le_two (s : Finset (ℕ × ℕ)) (n M L j : ℕ)
    (hL : 0 < L) (hsmall : 2*L^6 < n)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n)
    (hB : ∀ a ∈ s, a.1/L ≤ M ∧ a.2/L ≤ M) :
    (s.filter fun a => lpsNatCircleBoxRank M L a = j).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (s.filter fun a => lpsNatCircleBoxRank M L a = j).card)
  obtain ⟨haS,haR⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbS,hbR⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcS,hcR⟩ := Finset.mem_filter.mp hc
  have qab := lpsNatCircleBoxRank_eq_imp_quotients_eq a b n M L (hs a haS) (hs b hbS)
    (hB a haS) (hB b hbS) (haR.trans hbR.symm)
  have qac := lpsNatCircleBoxRank_eq_imp_quotients_eq a c n M L (hs a haS) (hs c hcS)
    (hB a haS) (hB c hcS) (haR.trans hcR.symm)
  have qbc := lpsNatCircleBoxRank_eq_imp_quotients_eq b c n M L (hs b hbS) (hs c hcS)
    (hB b hbS) (hB c hcS) (hbR.trans hcR.symm)
  have haZ : (a.1 : ℤ)^2+(a.2 : ℤ)^2=(n : ℤ) := by exact_mod_cast hs a haS
  have hbZ : (b.1 : ℤ)^2+(b.2 : ℤ)^2=(n : ℤ) := by exact_mod_cast hs b hbS
  have hcZ : (c.1 : ℤ)^2+(c.2 : ℤ)^2=(n : ℤ) := by exact_mod_cast hs c hcS
  have he := lpsIntegerCircleThinBox_no_three_distinct
    ((a.1 : ℤ),(a.2 : ℤ)) ((b.1 : ℤ),(b.2 : ℤ)) ((c.1 : ℤ),(c.2 : ℤ))
    (n : ℤ) (L : ℤ) (by positivity) (by positivity) (by exact_mod_cast hsmall)
    haZ hbZ hcZ
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qab.1)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qab.2)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qac.1)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qac.2)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qbc.1)
    (lpsNatSameQuotient_abs_sub_le _ _ L hL qbc.2)
  rcases he with he | he | he
  · exact hab (lpsNatPair_intCast_injective he)
  · exact hac (lpsNatPair_intCast_injective he)
  · exact hbc (lpsNatPair_intCast_injective he)

lemma lpsNatCircle_card_le_boxes (s : Finset (ℕ × ℕ)) (n M L : ℕ)
    (hL : 0 < L) (hsmall : 2*L^6 < n)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n)
    (hB : ∀ a ∈ s, a.1/L ≤ M ∧ a.2/L ≤ M) : s.card ≤ 2*(2*M+1) := by
  classical
  have hmap : ∀ a ∈ s, lpsNatCircleBoxRank M L a ∈ Finset.range (2*M+1) := by
    intro a ha
    have hr : lpsNatCircleBoxRank M L a ≤ M+M :=
      Nat.add_le_add (hB a ha).1 (Nat.sub_le M _)
    exact Finset.mem_range.mpr (by omega)
  have hh := Finset.card_le_mul_card_image_of_maps_to hmap 2
    (fun j _ => lpsNatCircleBoxRank_fiber_card_le_two s n M L j hL hsmall hs hB)
  simpa using hh

lemma lpsNatCircle_firstCoordinate_injOn (s : Finset (ℕ × ℕ)) (n : ℕ)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n) : (s : Set (ℕ × ℕ)).InjOn Prod.fst := by
  intro a ha b hb h
  have haN := hs a ha
  have hbN := hs b hb
  have hsq : a.2^2=b.2^2 := by change a.1=b.1 at h; rw [h] at haN; omega
  exact Prod.ext h (by simpa only [Nat.sqrt_eq'] using congrArg Nat.sqrt hsq)

lemma lpsNatCircle_card_le_coordinate_bound (s : Finset (ℕ × ℕ)) (n R : ℕ)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n) (hR : ∀ a ∈ s, a.1 ≤ R) : s.card ≤ R+1 := by
  classical
  have hm : Set.MapsTo Prod.fst (s : Set (ℕ × ℕ)) (Finset.range (R+1) : Set ℕ) := by
    intro a ha
    exact Finset.mem_range.mpr (by have := hR a ha; omega)
  simpa using Finset.card_le_card_of_injOn Prod.fst hm (lpsNatCircle_firstCoordinate_injOn s n hs)

lemma lpsNatSquare_coordinate_bound (x n R : ℕ) (hx : x^2 ≤ n) (hn : n ≤ R^2) : x ≤ R := by
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (hx.trans hn)

lemma lpsNatCircle_coordinates_bound (a : ℕ × ℕ) (n R : ℕ)
    (ha : a.1^2+a.2^2=n) (hn : n ≤ R^2) : a.1 ≤ R ∧ a.2 ≤ R := by
  constructor
  · exact lpsNatSquare_coordinate_bound a.1 n R (by omega) hn
  · exact lpsNatSquare_coordinate_bound a.2 n R (by omega) hn

lemma lpsNatCircle_card_le_six_mul_cube (s : Finset (ℕ × ℕ)) (n K : ℕ)
    (hK : 0 < K) (hn : n ≤ K^8) (hs : ∀ a ∈ s, a.1^2+a.2^2=n) :
    s.card ≤ 6*K^3 := by
  have hk3 : 0 < K^3 := pow_pos hK _
  by_cases hsmall : n ≤ 2*K^6
  · have hnR : n ≤ (2*K^3)^2 := by
      calc
        n ≤ 2*K^6 := hsmall
        _ ≤ 4*K^6 := by omega
        _ = (2*K^3)^2 := by ring
    have hc := lpsNatCircle_card_le_coordinate_bound s n (2*K^3) hs
      (fun a ha => (lpsNatCircle_coordinates_bound a n (2*K^3) (hs a ha) hnR).1)
    omega
  · have hnR : n ≤ (K^4)^2 := by simpa only [← pow_mul] using hn
    have hdiv : K^4/K=K^3 := by
      rw [show K^4=K^3*K by ring, Nat.mul_div_cancel _ hK]
    have hB : ∀ a ∈ s, a.1/K ≤ K^3 ∧ a.2/K ≤ K^3 := by
      intro a ha
      have hb := lpsNatCircle_coordinates_bound a n (K^4) (hs a ha) hnR
      constructor
      · simpa only [hdiv] using (Nat.div_le_div_right hb.1 : a.1/K ≤ K^4/K)
      · simpa only [hdiv] using (Nat.div_le_div_right hb.2 : a.2/K ≤ K^4/K)
    have hc := lpsNatCircle_card_le_boxes s n (K^3) K hK (by omega) hs hB
    omega

lemma lpsNatThreeSquare_card_le_twelve_mul_seventh
    (s : Finset ((ℕ × ℕ) × ℕ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^8)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=n) : s.card ≤ 12*K^7 := by
  classical
  have hnR : n ≤ (K^4)^2 := by simpa only [← pow_mul] using hn
  have hmap : ∀ a ∈ s, a.2 ∈ Finset.range (K^4+1) := by
    intro a ha
    have hc := lpsNatSquare_coordinate_bound a.2 n (K^4) (by have := hs a ha; omega) hnR
    exact Finset.mem_range.mpr (by omega)
  have hfib : ∀ j ∈ Finset.range (K^4+1), (s.filter fun a => a.2=j).card ≤ 6*K^3 := by
    intro j _hj
    let t := s.filter fun a => a.2=j
    have hi : (t : Set ((ℕ × ℕ) × ℕ)).InjOn Prod.fst := by
      intro a ha b hb h
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      exact Prod.ext h (ha2.trans hb2.symm)
    have he : t.card=(t.image Prod.fst).card := (Finset.card_image_of_injOn hi).symm
    rw [he]
    apply lpsNatCircle_card_le_six_mul_cube _ (n-j^2) K hK ((Nat.sub_le _ _).trans hn)
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hbS,hbj⟩ := Finset.mem_filter.mp hb
    have hbN := hs b hbS
    rw [hbj] at hbN
    omega
  have hc := Finset.card_le_mul_card_image_of_maps_to hmap (6*K^3) hfib
  have hk4 : 1 ≤ K^4 := by have := pow_pos hK 4; omega
  calc
    s.card ≤ 6*K^3*(K^4+1) := by simpa using hc
    _ ≤ 6*K^3*(2*K^4) := Nat.mul_le_mul_left _ (by omega)
    _ = 12*K^7 := by ring

lemma lpsInteger_mem_signed_pair_of_natAbs_eq (x : ℤ) (n : ℕ) (h : x.natAbs=n) :
    x ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ) := by
  have he : |x|=(n : ℤ) := by rw [← Int.natCast_natAbs, h]
  rcases le_total 0 x with hp | hn
  · rw [abs_of_nonneg hp] at he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl he
  · rw [abs_of_nonpos hn] at he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (by omega)

def lpsIntegerThreeSquareAbs (a : (ℤ × ℤ) × ℤ) : (ℕ × ℕ) × ℕ :=
  ((a.1.1.natAbs,a.1.2.natAbs),a.2.natAbs)

def lpsIntegerThreeSquareSignedBox (a : (ℕ × ℕ) × ℕ) : Finset ((ℤ × ℤ) × ℤ) :=
  (({(a.1.1 : ℤ), -(a.1.1 : ℤ)} : Finset ℤ).product
    {(a.1.2 : ℤ), -(a.1.2 : ℤ)}).product {(a.2 : ℤ), -(a.2 : ℤ)}

lemma lpsIntegerThreeSquareSignedBox_card_le_eight (a : (ℕ × ℕ) × ℕ) :
    (lpsIntegerThreeSquareSignedBox a).card ≤ 8 := by
  have hx : ({(a.1.1 : ℤ), -(a.1.1 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have hy : ({(a.1.2 : ℤ), -(a.1.2 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have hz : ({(a.2 : ℤ), -(a.2 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  unfold lpsIntegerThreeSquareSignedBox
  simp only [Finset.product_eq_sprod, Finset.card_product]
  exact Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz

lemma lpsIntegerThreeSquareAbs_fiber_card_le_eight
    (s : Finset ((ℤ × ℤ) × ℤ)) (a : (ℕ × ℕ) × ℕ) :
    (s.filter fun b => lpsIntegerThreeSquareAbs b=a).card ≤ 8 := by
  classical
  have hsub : (s.filter fun b => lpsIntegerThreeSquareAbs b=a) ⊆ lpsIntegerThreeSquareSignedBox a := by
    intro b hb
    have he := (Finset.mem_filter.mp hb).2
    have hx : b.1.1.natAbs=a.1.1 := congrArg (fun v : (ℕ × ℕ) × ℕ => v.1.1) he
    have hy : b.1.2.natAbs=a.1.2 := congrArg (fun v : (ℕ × ℕ) × ℕ => v.1.2) he
    have hz : b.2.natAbs=a.2 := congrArg Prod.snd he
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨lpsInteger_mem_signed_pair_of_natAbs_eq _ _ hx,
        lpsInteger_mem_signed_pair_of_natAbs_eq _ _ hy⟩,
      lpsInteger_mem_signed_pair_of_natAbs_eq _ _ hz⟩
  exact (Finset.card_le_card hsub).trans (lpsIntegerThreeSquareSignedBox_card_le_eight a)

lemma lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh
    (s : Finset ((ℤ × ℤ) × ℤ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^8)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=(n : ℤ)) : s.card ≤ 96*K^7 := by
  classical
  have hNat : ∀ a ∈ s.image lpsIntegerThreeSquareAbs, a.1.1^2+a.1.2^2+a.2^2=n := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have hh : (b.1.1.natAbs : ℤ)^2+(b.1.2.natAbs : ℤ)^2+(b.2.natAbs : ℤ)^2=(n : ℤ) := by
      simpa only [Int.natCast_natAbs, sq_abs] using hs b hb
    change b.1.1.natAbs^2+b.1.2.natAbs^2+b.2.natAbs^2=n
    exact_mod_cast hh
  have hcount := lpsNatThreeSquare_card_le_twelve_mul_seventh (s.image lpsIntegerThreeSquareAbs) n K hK hn hNat
  have hc := Finset.card_le_mul_card_image s 8 (fun a _ => lpsIntegerThreeSquareAbs_fiber_card_le_eight s a)
  calc
    s.card ≤ 8*(s.image lpsIntegerThreeSquareAbs).card := hc
    _ ≤ 8*(12*K^7) := Nat.mul_le_mul_left _ hcount
    _ = 96*K^7 := by ring

lemma card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh
    (q n K : ℕ) (hq : 0 < q) (hK : 0 < K) (hn : n ≤ 4*q^2*K^8) (x : ℤ) :
    ((lpsTraceQuadraticShell q n).filter fun t => t.a=x).card ≤ 96*K^7 := by
  classical
  let s := (lpsTraceQuadraticShell q n).filter fun t => t.a=x
  by_cases hne : s.Nonempty
  · obtain ⟨t0,ht0⟩ := hne
    let f : LPSQuaternion → (ℤ × ℤ) × ℤ := fun t => ((t.b,t.c),t.d)
    let scale : ℤ := 4*(q : ℤ)^2
    have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
    have hscale : 0 < scale := by dsimp [scale]; positivity
    have hform : ∀ t ∈ s, t.a^2+scale*(t.b^2+t.c^2+t.d^2)=(n : ℤ) := by
      intro t ht
      have hnT := (mem_lpsTraceQuadraticShell_iff hq t).mp (Finset.mem_filter.mp ht).1
      calc
        _ = lpsTraceQuadraticForm q t := by unfold lpsTraceQuadraticForm; dsimp [scale]; ring
        _ = (n : ℤ) := hnT
    have hzero : 0 ≤ t0.b^2+t0.c^2+t0.d^2 := by positivity
    let m := (t0.b^2+t0.c^2+t0.d^2).toNat
    have hm : (m : ℤ)=t0.b^2+t0.c^2+t0.d^2 := Int.toNat_of_nonneg hzero
    have hnZ : (n : ℤ) ≤ scale*(K : ℤ)^8 := by dsimp [scale]; exact_mod_cast hn
    have hprod : scale*(t0.b^2+t0.c^2+t0.d^2) ≤ scale*(K : ℤ)^8 := by
      linarith [hform t0 ht0, sq_nonneg t0.a]
    have hmK : m ≤ K^8 := by
      have hh := le_of_mul_le_mul_left hprod hscale
      rw [← hm] at hh
      exact_mod_cast hh
    have hi : (s : Set LPSQuaternion).InjOn f := by
      intro a ha b hb h
      apply LPSQuaternion.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact congrArg (fun v : (ℤ × ℤ) × ℤ => v.1.1) h
      · exact congrArg (fun v : (ℤ × ℤ) × ℤ => v.1.2) h
      · exact congrArg Prod.snd h
    have hsI : ∀ a ∈ s.image f, a.1.1^2+a.1.2^2+a.2^2=(m : ℤ) := by
      intro a ha
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
      have h0 := hform t0 ht0
      have hT := hform t ht
      have h0a := (Finset.mem_filter.mp ht0).2
      have hTa := (Finset.mem_filter.mp ht).2
      rw [h0a] at h0
      rw [hTa] at hT
      have he : scale*(t.b^2+t.c^2+t.d^2)=scale*(t0.b^2+t0.c^2+t0.d^2) := by linarith
      change t.b^2+t.c^2+t.d^2=(m : ℤ)
      rw [hm]
      exact mul_left_cancel₀ (ne_of_gt hscale) he
    change s.card ≤ 96*K^7
    rw [← Finset.card_image_of_injOn hi]
    exact lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh (s.image f) m K hK hmK hsI
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change s.card ≤ 96*K^7
    rw [he]
    simp

end
end QEC.Coding.TannerLiftedProduct
