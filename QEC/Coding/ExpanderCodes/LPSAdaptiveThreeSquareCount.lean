import QEC.Coding.ExpanderCodes.LPSTraceFirstCoordinateCount
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Adaptive three-square and actual LPS return counts

Choose a box scale L with 2*L^6<n<=128*L^6 using Nat.findGreatest.
The proved thin-box circle estimate, its monotone rank injection and actual
coordinate bounds give at most 50*K^2 nonnegative circle points for n<=K^6.
Slicing the actual third coordinate and handling the eight signed fibers
then give 100*K^5 nonnegative and 800*K^5 integer three-square points.
All finite-set conclusions are derived from the displayed norm equation.

Actual native quadratic-shell fibers therefore have cardinality<=800*K^5
when n<=4*q^2*K^6. The actual first-coordinate image bound gives whole
quadratic and congruence shell counts<=1600*(2*r/q^2+1)*K^5 for prime q
not dividing 2*r and r^2<=4*q^2*K^6. The proved factor-two identity gives
native alternating closed reduced-word count<=800*(2*p^k/q^2+1)*K^5 at
length2*k for actual LPSResiduePrime p under p^(2*k)<=4*q^2*K^6, K>0.

This is our own weaker elementary arithmetic derivation motivated by
Davidoff--Sarnak--Valette section4.4, printed pages125-128. It does not
supply their sharp counting theorem or a spectral theorem. The displayed
scale cap remains an arithmetic input, not an optimized Chebyshev choice.
Centered PSL2 multiplicity, a spectral gap, amplification, compatible code
construction and the exact explicit arbitrary-field/every-rate PK22 family
remain obligations. Parent issue449 stays OPEN and public records remain
unproved; the selected Gauss/curve route is unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsNatCircle_exists_adaptive_box_scale (n : ℕ) (hn : 2 < n) :
    ∃ L : ℕ, 0 < L ∧ 2*L^6 < n ∧ n ≤ 128*L^6 := by
  let P : ℕ → Prop := fun L => 2*L^6 < n
  let L := Nat.findGreatest P n
  have h1 : P 1 := by dsimp [P]; simpa using hn
  have hL1 : 1 ≤ L := Nat.le_findGreatest (by omega) h1
  have hsmall : 2*L^6 < n := Nat.findGreatest_spec (by omega : 1 ≤ n) h1
  have hself : L ≤ L^6 := le_self_pow₀ hL1 (by decide : 6 ≠ 0)
  have hLn : L+1 ≤ n := by omega
  have hnext : ¬P (L+1) := Nat.findGreatest_is_greatest (by dsimp [L]; omega) hLn
  have hnext' : n ≤ 2*(L+1)^6 := by dsimp [P] at hnext; omega
  have htwice : L+1 ≤ 2*L := by omega
  have hpow : (L+1)^6 ≤ (2*L)^6 := by gcongr
  refine ⟨L,by omega,hsmall,?_⟩
  calc
    n ≤ 2*(L+1)^6 := hnext'
    _ ≤ 2*(2*L)^6 := Nat.mul_le_mul_left _ hpow
    _ = 128*L^6 := by ring

lemma lpsNatCircle_card_le_fifty_mul_square (s : Finset (ℕ × ℕ)) (n K : ℕ)
    (hK : 0 < K) (hn : n ≤ K^6) (hs : ∀ a ∈ s, a.1^2+a.2^2=n) :
    s.card ≤ 50*K^2 := by
  have hk2 : 1 ≤ K^2 := by have := pow_pos hK 2; omega
  by_cases hsmall : n ≤ 2
  · have hc := lpsNatCircle_card_le_coordinate_bound s n 2 hs
      (fun a ha => (lpsNatCircle_coordinates_bound a n 2 (hs a ha) (by omega)).1)
    omega
  · obtain ⟨L,hL,hthin,hbound⟩ := lpsNatCircle_exists_adaptive_box_scale n (by omega)
    have hLK : L ≤ K := (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp (by omega : L^6 ≤ K^6)
    have hnR : n ≤ (12*L^3)^2 := by
      calc
        n ≤ 128*L^6 := hbound
        _ ≤ 144*L^6 := by omega
        _ = (12*L^3)^2 := by ring
    have hdiv : (12*L^3)/L=12*L^2 := by
      rw [show 12*L^3=(12*L^2)*L by ring,Nat.mul_div_cancel _ hL]
    have hL2K2 : L^2 ≤ K^2 := by gcongr
    have hB : ∀ a ∈ s, a.1/L ≤ 12*K^2 ∧ a.2/L ≤ 12*K^2 := by
      intro a ha
      have hb := lpsNatCircle_coordinates_bound a n (12*L^3) (hs a ha) hnR
      constructor
      · have hh : a.1/L ≤ (12*L^3)/L := Nat.div_le_div_right hb.1
        rw [hdiv] at hh
        exact hh.trans (Nat.mul_le_mul_left _ hL2K2)
      · have hh : a.2/L ≤ (12*L^3)/L := Nat.div_le_div_right hb.2
        rw [hdiv] at hh
        exact hh.trans (Nat.mul_le_mul_left _ hL2K2)
    have hc := lpsNatCircle_card_le_boxes s n (12*K^2) L hL hthin hs hB
    omega

lemma lpsNatThreeSquare_card_le_hundred_mul_fifth
    (s : Finset ((ℕ × ℕ) × ℕ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^6)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=n) : s.card ≤ 100*K^5 := by
  classical
  have hnR : n ≤ (K^3)^2 := by simpa only [← pow_mul] using hn
  have hmap : ∀ a ∈ s, a.2 ∈ Finset.range (K^3+1) := by
    intro a ha
    have hc := lpsNatSquare_coordinate_bound a.2 n (K^3) (by have := hs a ha; omega) hnR
    exact Finset.mem_range.mpr (by omega)
  have hfib : ∀ j ∈ Finset.range (K^3+1), (s.filter fun a => a.2=j).card ≤ 50*K^2 := by
    intro j _hj
    let t := s.filter fun a => a.2=j
    have hi : (t : Set ((ℕ × ℕ) × ℕ)).InjOn Prod.fst := by
      intro a ha b hb h
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      exact Prod.ext h (ha2.trans hb2.symm)
    have he : t.card=(t.image Prod.fst).card := (Finset.card_image_of_injOn hi).symm
    rw [he]
    apply lpsNatCircle_card_le_fifty_mul_square _ (n-j^2) K hK ((Nat.sub_le _ _).trans hn)
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hbS,hbj⟩ := Finset.mem_filter.mp hb
    have hbN := hs b hbS
    rw [hbj] at hbN
    omega
  have hc := Finset.card_le_mul_card_image_of_maps_to hmap (50*K^2) hfib
  have hk3 : 1 ≤ K^3 := by have := pow_pos hK 3; omega
  calc
    s.card ≤ 50*K^2*(K^3+1) := by simpa using hc
    _ ≤ 50*K^2*(2*K^3) := Nat.mul_le_mul_left _ (by omega)
    _ = 100*K^5 := by ring

lemma lpsIntegerThreeSquare_card_le_eightHundred_mul_fifth
    (s : Finset ((ℤ × ℤ) × ℤ)) (n K : ℕ) (hK : 0 < K) (hn : n ≤ K^6)
    (hs : ∀ a ∈ s, a.1.1^2+a.1.2^2+a.2^2=(n : ℤ)) : s.card ≤ 800*K^5 := by
  classical
  have hNat : ∀ a ∈ s.image lpsIntegerThreeSquareAbs, a.1.1^2+a.1.2^2+a.2^2=n := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    have hh : (b.1.1.natAbs : ℤ)^2+(b.1.2.natAbs : ℤ)^2+(b.2.natAbs : ℤ)^2=(n : ℤ) := by
      simpa only [Int.natCast_natAbs, sq_abs] using hs b hb
    change b.1.1.natAbs^2+b.1.2.natAbs^2+b.2.natAbs^2=n
    exact_mod_cast hh
  have hcount := lpsNatThreeSquare_card_le_hundred_mul_fifth (s.image lpsIntegerThreeSquareAbs) n K hK hn hNat
  have hc := Finset.card_le_mul_card_image s 8 (fun a _ => lpsIntegerThreeSquareAbs_fiber_card_le_eight s a)
  calc
    s.card ≤ 8*(s.image lpsIntegerThreeSquareAbs).card := hc
    _ ≤ 8*(100*K^5) := Nat.mul_le_mul_left _ hcount
    _ = 800*K^5 := by ring

lemma card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth
    (q n K : ℕ) (hq : 0 < q) (hK : 0 < K) (hn : n ≤ 4*q^2*K^6) (x : ℤ) :
    ((lpsTraceQuadraticShell q n).filter fun t => t.a=x).card ≤ 800*K^5 := by
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
    have hnZ : (n : ℤ) ≤ scale*(K : ℤ)^6 := by dsimp [scale]; exact_mod_cast hn
    have hprod : scale*(t0.b^2+t0.c^2+t0.d^2) ≤ scale*(K : ℤ)^6 := by
      linarith [hform t0 ht0, sq_nonneg t0.a]
    have hmK : m ≤ K^6 := by
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
    change s.card ≤ 800*K^5
    rw [← Finset.card_image_of_injOn hi]
    exact lpsIntegerThreeSquare_card_le_eightHundred_mul_fifth (s.image f) m K hK hmK hsI
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change s.card ≤ 800*K^5
    rw [he]
    simp

lemma card_lpsTraceQuadraticShell_square_le_adaptive (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^6) :
    (lpsTraceQuadraticShell q (r^2)).card ≤ 1600*(2*r/q^2+1)*K^5 := by
  classical
  have hf := Finset.card_le_mul_card_image (lpsTraceQuadraticShell q (r^2)) (800*K^5)
    (fun x _ => card_lpsTraceQuadraticShell_firstCoordinate_le_eightHundred_mul_fifth q (r^2) K hq.pos hK hcap x)
  have hi := lpsTraceQuadraticShell_firstCoordinate_image_card_le q r hq hqr
  calc
    _ ≤ (800*K^5)*((lpsTraceQuadraticShell q (r^2)).image LPSQuaternion.a).card := hf
    _ ≤ (800*K^5)*(2*(2*r/q^2+1)) := Nat.mul_le_mul_left _ hi
    _ = 1600*(2*r/q^2+1)*K^5 := by ring

lemma card_lpsTraceCongruenceShell_square_le_adaptive (q r K : ℕ) (hq : q.Prime) (hK : 0 < K)
    (hqr : ¬(q : ℤ) ∣ 2*(r : ℤ)) (hcap : r^2 ≤ 4*q^2*K^6) :
    (lpsTraceCongruenceShell q (r^2)).card ≤ 1600*(2*r/q^2+1)*K^5 := by
  have hr : 0 < r := by
    by_contra h
    have hr0 : r=0 := by omega
    apply hqr
    simp [hr0]
  rw [← card_lpsTraceQuadraticShell_eq_congruenceShell hq.pos (pow_pos hr 2)]
  exact card_lpsTraceQuadraticShell_square_le_adaptive q r K hq hK hqr hcap

lemma lpsAlternatingClosedReducedWordCount_even_le_adaptive {p : ℕ} (a : LPSResiduePrime p)
    (k K : ℕ) (hK : 0 < K) (hcap : p^(2*k) ≤ 4*a.q^2*K^6) :
    lpsAlternatingClosedReducedWordCount a (2*k) ≤ 800*(2*p^k/a.q^2+1)*K^5 := by
  have hq : ¬(a.q : ℤ) ∣ 2*((p^k : ℕ) : ℤ) := by
    exact_mod_cast lpsResiduePrime_not_dvd_twice_degree_pow a k
  have hcap' : (p^k)^2 ≤ 4*a.q^2*K^6 := by simpa only [← pow_mul, Nat.mul_comm k 2] using hcap
  have hb := card_lpsTraceCongruenceShell_square_le_adaptive a.q (p^k) K a.prime hK hq hcap'
  have hc := card_traceCongruenceShell_eq_two_mul_alternatingClosedCount a (2*k)
  have hn : p^(2*k)=(p^k)^2 := by rw [← pow_mul]; congr 1; omega
  have htwice : 2*lpsAlternatingClosedReducedWordCount a (2*k) ≤ 2*(800*(2*p^k/a.q^2+1)*K^5) := by
    calc
      _ = (lpsTraceCongruenceShell a.q (p^(2*k))).card := hc.symm
      _ = (lpsTraceCongruenceShell a.q ((p^k)^2)).card := by rw [hn]
      _ ≤ 1600*(2*p^k/a.q^2+1)*K^5 := hb
      _ = 2*(800*(2*p^k/a.q^2+1)*K^5) := by ring
  exact Nat.le_of_mul_le_mul_left htwice (by decide : 0 < 2)

end
end QEC.Coding.TannerLiftedProduct
