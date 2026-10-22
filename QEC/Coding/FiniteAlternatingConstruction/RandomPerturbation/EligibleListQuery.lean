import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EligibilityQuery

/-! # Actual four-label eligibility filtering preserves domain-label multiplicity -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def eligibleListQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (L : List (Triangle P)) : (Finset (Triangle P) × Bool) × ℕ := by
  classical
  let unique := dedupQuery (triangleLabelEqQuery P) L
  let s : Finset (Triangle P) := ⟨↑unique.1,by
    rw [dedupQuery_value _ (triangleLabelEqQuery_correct P)]
    exact List.nodup_dedup L⟩
  let pairs := listAllQuery (fun a => listAllQuery (eligiblePairQuery P J r a) unique.1) unique.1
  exact ((s,decide (unique.1.length = 4) && pairs.1),unique.2+pairs.2+unique.1.length+2)

theorem eligibleListQuery_set (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (L : List (Triangle P)) : (eligibleListQuery P J r L).1.1 = L.toFinset := by
  classical
  ext a
  simp only [eligibleListQuery,Finset.mem_mk,Multiset.mem_coe,
    dedupQuery_value _ (triangleLabelEqQuery_correct P),List.mem_dedup,List.mem_toFinset]

theorem eligibleListQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) :
    (eligibleListQuery P J r L).1.2 = true ↔ Eligible P J r (eligibleListQuery P J r L).1.1 := by
  classical
  rw [eligibleListQuery_set]
  simp only [eligibleListQuery,Bool.and_eq_true,decide_eq_true_eq,listAllQuery_correct,
    eligiblePairQuery_correct P J hr,dedupQuery_value _ (triangleLabelEqQuery_correct P)]
  have hcard : L.dedup.length = L.toFinset.card := (List.card_toFinset L).symm
  rw [hcard]
  change (L.toFinset.card = 4 ∧ ∀ a ∈ L.dedup, ∀ b ∈ L.dedup,
    triangleColor P a = triangleColor P b ∧ dist (oldAnchor P J a) (oldAnchor P J b) ≤ r) ↔
      (L.toFinset.card = 4 ∧
        (∀ a ∈ L.toFinset, ∀ b ∈ L.toFinset, triangleColor P a = triangleColor P b) ∧
        ∀ a ∈ L.toFinset, ∀ b ∈ L.toFinset, dist (oldAnchor P J a) (oldAnchor P J b) ≤ r)
  have hm (a : Triangle P) : a ∈ L.dedup ↔ a ∈ L.toFinset := by
    simp only [List.mem_dedup,List.mem_toFinset]
  constructor
  · rintro ⟨hc,hpairs⟩
    exact ⟨hc,fun a ha b hb => (hpairs a ((hm a).mpr ha) b ((hm b).mpr hb)).1,
      fun a ha b hb => (hpairs a ((hm a).mpr ha) b ((hm b).mpr hb)).2⟩
  · rintro ⟨hc,hcolors,hdist⟩
    exact ⟨hc,fun a ha b hb => ⟨hcolors a ((hm a).mp ha) b ((hm b).mp hb),
      hdist a ((hm a).mp ha) b ((hm b).mp hb)⟩⟩

theorem eligibleListQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r : ℝ) (L : List (Triangle P)) (hL : L.length = 4) :
    (eligibleListQuery P J r L).2 ≤ 100000*(Fintype.card (Triangle P)+1)^2 := by
  classical
  let unique := dedupQuery (triangleLabelEqQuery P) L
  have hu : unique.1.length ≤ 4 := by
    rw [dedupQuery_value _ (triangleLabelEqQuery_correct P)]
    exact ((List.dedup_sublist L).length_le).trans hL.le
  let C := 6*Fintype.card (Triangle P)*(Fintype.card (Triangle P)+6)+2007
  have hd := dedupQuery_cost_le (triangleLabelEqQuery P) (triangleLabelEqQuery_correct P)
    (2*Fintype.card (Triangle P)+1) (triangleLabelEqQuery_cost_le P) L
  rw [hL] at hd
  have hc (a : Triangle P) : (listAllQuery (eligiblePairQuery P J r a) unique.1).2 ≤ 4*(C+1) := by
    have h := listAllQuery_cost_le (eligiblePairQuery P J r a) unique.1 C
      (fun b _ => eligiblePairQuery_cost_le P J r a b)
    exact h.trans (Nat.mul_le_mul_right _ hu)
  have hp := listAllQuery_cost_le (fun a => listAllQuery (eligiblePairQuery P J r a) unique.1)
    unique.1 (4*(C+1)) (fun a _ => hc a)
  have hp' : (listAllQuery (fun a => listAllQuery (eligiblePairQuery P J r a) unique.1) unique.1).2 ≤
      4*(4*(C+1)+1) := hp.trans (Nat.mul_le_mul_right _ hu)
  dsimp only [eligibleListQuery]
  dsimp only [unique,C] at hd hp' hu ⊢
  nlinarith

/-- Constructor proofs erase; the finite set is stored as the already deduplicated list. -/
noncomputable def candidateEventQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) : Option (Event P J r) × ℕ :=
  let q := eligibleListQuery P J r L
  if h : q.1.2 = true then
    (some ⟨q.1.1,(eligibleListQuery_correct P J hr L).mp h⟩,q.2+1)
  else (none,q.2+1)

theorem candidateEventQuery_some_iff (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) (e : Event P J r) :
    (candidateEventQuery P J hr L).1 = some e ↔ L.toFinset = e.val := by
  classical
  constructor
  · intro h
    simp only [candidateEventQuery] at h
    split_ifs at h with ht
    · have he := Option.some.inj h
      exact (eligibleListQuery_set P J r L).symm.trans (congrArg Subtype.val he)
  · intro h
    have hg : Eligible P J r (eligibleListQuery P J r L).1.1 := by
      rw [eligibleListQuery_set,h]
      exact e.property
    have ht := (eligibleListQuery_correct P J hr L).mpr hg
    simp only [candidateEventQuery,ht,if_pos]
    apply congrArg some
    apply Subtype.ext
    exact (eligibleListQuery_set P J r L).trans h

theorem candidateEventQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) (hL : L.length = 4) :
    (candidateEventQuery P J hr L).2 ≤ 100000*(Fintype.card (Triangle P)+1)^2+1 := by
  have h := eligibleListQuery_cost_le P J r L hL
  simp only [candidateEventQuery]
  split_ifs <;> omega

end QEC.Coding.BDL26RandomPerturbation
