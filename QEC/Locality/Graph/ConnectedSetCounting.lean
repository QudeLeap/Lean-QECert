import QEC.Locality.Graph.Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connected induced vertex-set counting

Project-derived internal finite counting closure for BDL26 v1, registered claim
`bdl26-witness-counting`, paper.tex:3658–3673. We count vertex sets, not choices
of edges. The proof uses exactly 2*m steps of an ordinary stuttering walk:
finite spanning-tree leaf removal inserts one round trip, and a singleton has
two root-idles. The full visited set recovers the induced vertex set. Counting
all such fixed-length walks directly avoids a variable-length coding shortcut.
No witness, decoder locality, minimum size or thermal conclusion is assumed.
-/
noncomputable section
namespace QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- One literal graph step or an idle at the current vertex. -/
def next (G : SimpleGraph V) (r : V) : Finset V := by
  classical
  exact insert r (Finset.univ.filter (G.Adj r))

private theorem mem_next (G : SimpleGraph V) (r w : V) :
    w ∈ next G r ↔ w = r ∨ G.Adj r w := by
  classical
  simp [next]

/-- ALL traces with exactly n transitions, including root-idle padding. -/
def traces (G : SimpleGraph V) (r : V) : Nat → Finset (List V)
  | 0 => {[r]}
  | n+1 => (next G r).biUnion fun w => (traces G w n).image (List.cons r)

private theorem mem_traces_succ (G : SimpleGraph V) (r : V) (n : Nat) (l : List V) :
    l ∈ traces G r (n+1) ↔
      ∃ w ∈ next G r, ∃ t ∈ traces G w n, r::t = l := by
  classical
  simp only [traces, Finset.mem_biUnion, Finset.mem_image]

private theorem prepend_trace (G : SimpleGraph V) {r w : V} {n : Nat} {l : List V}
    (hw : w ∈ next G r) (hl : l ∈ traces G w n) : r::l ∈ traces G r (n+1) :=
  (mem_traces_succ G r n _).mpr ⟨w,hw,l,hl,rfl⟩

/-- The representation really is fixed length, with the initial vertex included. -/
theorem traces_length (G : SimpleGraph V) (r : V) (n : Nat) (l : List V)
    (hl : l ∈ traces G r n) : l.length = n+1 := by
  induction n generalizing r l with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    simp [he]
  | succ n ih =>
    obtain ⟨w,hw,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
    simpa only [List.length_cons] using congrArg Nat.succ (ih w t ht)

private theorem root_mem_trace (G : SimpleGraph V) (r : V) (n : Nat) (l : List V)
    (hl : l ∈ traces G r n) : r ∈ l.toFinset := by
  cases n with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    simp [he]
  | succ n =>
    obtain ⟨w,hw,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
    simp

private theorem map_trace {W : Type v} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hf : ∀ a b, G.Adj a b → H.Adj (f a) (f b))
    (r : V) (n : Nat) (l : List V) (hl : l ∈ traces G r n) :
    l.map f ∈ traces H (f r) n := by
  induction n generalizing r l with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    simp [he,traces]
  | succ n ih =>
    obtain ⟨w,hw,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
    have hw' : f w ∈ next H (f r) := by
      rcases (mem_next G r w).mp hw with h | h
      · exact (mem_next H (f r) (f w)).mpr (Or.inl (congrArg f h))
      · exact (mem_next H (f r) (f w)).mpr (Or.inr (hf r w h))
    exact prepend_trace H hw' (ih w t ht)

/-- Insert a genuine edge-and-return at an actually visited vertex. -/
private theorem insert_round_trip (G : SimpleGraph V) (n : Nat) (r : V) (l : List V)
    (hl : l ∈ traces G r n) (w z : V) (hw : w ∈ l.toFinset) (hwz : G.Adj w z) :
    ∃ l' ∈ traces G r (n+2), l'.toFinset = insert z l.toFinset := by
  induction n generalizing r l with
  | zero =>
    have he : l = [r] := by simpa [traces] using hl
    subst l
    have hwr : w = r := by simpa using hw
    subst w
    refine ⟨[r,z,r], prepend_trace G ((mem_next G r z).mpr (.inr hwz))
      (prepend_trace G ((mem_next G z r).mpr (.inr hwz.symm)) (by simp [traces])), ?_⟩
    simp [Finset.insert_comm]
  | succ n ih =>
    by_cases hwr : w = r
    · subst w
      refine ⟨r::z::l, prepend_trace G ((mem_next G r z).mpr (.inr hwz))
        (prepend_trace G ((mem_next G z r).mpr (.inr hwz.symm)) hl), ?_⟩
      have hr := root_mem_trace G r (n+1) l hl
      simp only [List.toFinset_cons]
      rw [Finset.insert_comm r z, Finset.insert_eq_of_mem hr]
    · obtain ⟨a,ha,t,ht,rfl⟩ := (mem_traces_succ G r n l).mp hl
      have hwt : w ∈ t.toFinset := by
        have hi : w ∈ insert r t.toFinset := by simpa only [List.toFinset_cons] using hw
        rcases Finset.mem_insert.mp hi with h | h
        · exact False.elim (hwr h)
        · exact h
      obtain ⟨t',ht',he⟩ := ih a t ht hwt
      refine ⟨r::t', prepend_trace G ha ht', ?_⟩
      simp only [List.toFinset_cons, he]
      exact Finset.insert_comm r z t.toFinset

/-- A finite connected graph admits a complete fixed-budget trace at ANY root.
The proof constructs its own spanning tree and a removable non-root leaf. -/
private theorem cover_all_aux (N : Nat) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = N → G.Connected → ∀ r : V,
      ∃ l ∈ traces G r (2*Fintype.card V), l.toFinset = Finset.univ := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ _ G hN hc r
    classical
    by_cases hsub : Subsingleton V
    · letI := hsub
      have hu : (Finset.univ : Finset V) = {r} := by
        ext x
        simp [Subsingleton.elim x r]
      have hcard : Fintype.card V = 1 := by
        simpa only [Finset.card_univ, Finset.card_singleton] using congrArg Finset.card hu
      refine ⟨[r,r,r], ?_, ?_⟩
      · have h0 : [r] ∈ traces G r 0 := by simp [traces]
        have h1 := prepend_trace G ((mem_next G r r).mpr (.inl rfl)) h0
        have h2 := prepend_trace G ((mem_next G r r).mpr (.inl rfl)) h1
        simpa only [hcard, Nat.mul_one] using h2
      · ext x
        simp [Subsingleton.elim x r]
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
      obtain ⟨a,b,hab,ha,hb⟩ := hT.exists_ne_and_degree_eq_one
      have hleaf : ∃ z : V, z ≠ r ∧ T.degree z = 1 := by
        by_cases har : a = r
        · exact ⟨b,fun hbr => hab (har.trans hbr.symm),hb⟩
        · exact ⟨a,har,ha⟩
      obtain ⟨z,hzr,hz⟩ := hleaf
      let W : Type u := {x : V // x ≠ z}
      let H : SimpleGraph W := G.induce {z}ᶜ
      have hH : H.Connected := by
        exact (hT.connected.induce_compl_singleton_of_degree_eq_one hz).mono
          (by intro x y hxy; exact hTG hxy)
      have hlt : Fintype.card W < N := by
        rw [← hN]
        exact Fintype.card_subtype_lt (x:=z) (by simp)
      have hrz : r ≠ z := Ne.symm hzr
      obtain ⟨l,hl,hcover⟩ := ih (Fintype.card W) hlt H rfl hH ⟨r,hrz⟩
      have hm : l.map (Subtype.val : W → V) ∈ traces G r (2*Fintype.card W) :=
        map_trace H G Subtype.val (fun _ _ hxy => hxy) ⟨r,hrz⟩ _ l hl
      have hs : (l.map (Subtype.val : W → V)).toFinset = Finset.univ.erase z := by
        ext x
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_erase, Finset.mem_univ,
          and_true]
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact y.property
        · intro hx
          have hy : (⟨x,hx⟩ : W) ∈ l.toFinset := by rw [hcover]; exact Finset.mem_univ _
          exact ⟨⟨x,hx⟩,List.mem_toFinset.mp hy,rfl⟩
      obtain ⟨w,hzw,hwunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
      have hwz : w ≠ z := by
        intro he
        subst w
        obtain ⟨hirr⟩ := T.loopless
        exact hirr z hzw
      have hw : w ∈ (l.map (Subtype.val : W → V)).toFinset := by
        rw [hs]
        simp [hwz]
      obtain ⟨l',hl',hs'⟩ := insert_round_trip G _ r _ hm w z hw (hTG hzw).symm
      have hcard : Fintype.card W = Fintype.card V - 1 := by
        exact (Fintype.card_subtype_compl (fun x : V => x = z)).trans
          (by rw [Fintype.card_subtype_eq])
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
      have hlen : 2*Fintype.card W+2 = 2*Fintype.card V := by omega
      refine ⟨l',hlen ▸ hl',?_⟩
      rw [hs',hs,Finset.insert_erase (Finset.mem_univ z)]

/-- Connectivity derives the full visited-set representation, not a caller code. -/
theorem induced_set_trace (G : SimpleGraph V) (A : Finset V) (r : V)
    (hr : r ∈ A) (hc : (G.induce (A : Set V)).Connected) :
    ∃ l ∈ traces G r (2*A.card), l.toFinset = A := by
  classical
  obtain ⟨l,hl,hs⟩ := cover_all_aux (Fintype.card A) (G.induce (A : Set V)) rfl hc ⟨r,hr⟩
  refine ⟨l.map Subtype.val, ?_, ?_⟩
  · have hm := map_trace (G.induce (A : Set V)) G Subtype.val
      (fun _ _ hxy => hxy) ⟨r,hr⟩ _ l hl
    have hcard : Fintype.card (A : Set V) = A.card :=
      Fintype.card_of_finset' A (fun _ => Iff.rfl)
    rw [hcard] at hm
    exact hm
  · ext x
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact y.property
    · intro hx
      have hy : (⟨x,hx⟩ : A) ∈ l.toFinset := by rw [hs]; exact Finset.mem_univ _
      exact ⟨⟨x,hx⟩,List.mem_toFinset.mp hy,rfl⟩

private theorem next_card_le (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (r : V) :
    (next G r).card ≤ Delta+1 := by
  classical
  have hn : (Finset.univ.filter (G.Adj r)).card ≤ Delta := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hd r
  exact (Finset.card_insert_le r _).trans (Nat.add_le_add_right hn 1)

/-- Count the COMPLETE length-n walk family; no variable-length sum is used. -/
theorem traces_card_le (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (r : V) (n : Nat) :
    (traces G r n).card ≤ (Delta+1)^n := by
  classical
  induction n generalizing r with
  | zero => simp [traces]
  | succ n ih =>
    calc
      (traces G r (n+1)).card ≤ ∑ w ∈ next G r,
          ((traces G w n).image (List.cons r)).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ next G r, (Delta+1)^n := by
        apply Finset.sum_le_sum
        intro w hw
        exact Finset.card_image_le.trans (ih w)
      _ = (next G r).card * (Delta+1)^n := by simp
      _ ≤ (Delta+1)*(Delta+1)^n := Nat.mul_le_mul_right _ (next_card_le G Delta hd r)
      _ = (Delta+1)^(n+1) := by rw [pow_succ, Nat.mul_comm]

/-- The exact finite family of connected INDUCED m-vertex sets through r. -/
def rooted (G : SimpleGraph V) (r : V) (m : Nat) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun A =>
    r ∈ A ∧ A.card = m ∧ (G.induce (A : Set V)).Connected

theorem mem_rooted (G : SimpleGraph V) (r : V) (m : Nat) (A : Finset V) :
    A ∈ rooted G r m ↔ r ∈ A ∧ A.card = m ∧ (G.induce (A : Set V)).Connected := by
  classical
  simp [rooted]

/-- Universal rooted count with only the measured degree inequality supplied. -/
theorem rooted_card_le (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (r : V) (m : Nat) :
    (rooted G r m).card ≤ (Delta+1)^(2*m) := by
  classical
  have hsub : rooted G r m ⊆ (traces G r (2*m)).image List.toFinset := by
    intro A hA
    obtain ⟨hr,hm,hc⟩ := (mem_rooted G r m A).mp hA
    obtain ⟨l,hl,hs⟩ := induced_set_trace G A r hr hc
    exact Finset.mem_image.mpr ⟨l,hm ▸ hl,hs⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (traces_card_le G Delta hd r (2*m)))

/-- Anchors are literal vertex membership, and rooted families may overlap. -/
def anchored (G : SimpleGraph V) (R : Finset V) (m : Nat) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun A =>
    A.card = m ∧ (G.induce (A : Set V)).Connected ∧ (A ∩ R).Nonempty

theorem mem_anchored (G : SimpleGraph V) (R : Finset V) (m : Nat) (A : Finset V) :
    A ∈ anchored G R m ↔ A.card = m ∧
      (G.induce (A : Set V)).Connected ∧ (A ∩ R).Nonempty := by
  classical
  simp [anchored]

/-- Exact union identity, with no disjointness premise. -/
theorem anchored_eq_biUnion (G : SimpleGraph V) (R : Finset V) (m : Nat) :
    anchored G R m = R.biUnion (fun r => rooted G r m) := by
  classical
  ext A
  simp only [mem_anchored,Finset.mem_biUnion,mem_rooted]
  constructor
  · rintro ⟨hm,hc,r,hr⟩
    exact ⟨r,(Finset.mem_inter.mp hr).2,(Finset.mem_inter.mp hr).1,hm,hc⟩
  · rintro ⟨r,hrR,hrA,hm,hc⟩
    exact ⟨hm,hc,r,Finset.mem_inter.mpr ⟨hrA,hrR⟩⟩

/-- Universal anchored count, valid also for empty anchors and empty carriers. -/
theorem anchored_card_le (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (R : Finset V) (m : Nat) :
    (anchored G R m).card ≤ R.card * (Delta+1)^(2*m) := by
  classical
  rw [anchored_eq_biUnion]
  calc
    (R.biUnion (fun r => rooted G r m)).card ≤ ∑ r ∈ R, (rooted G r m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, (Delta+1)^(2*m) := by
      apply Finset.sum_le_sum
      intro r hr
      exact rooted_card_le G Delta hd r m
    _ = R.card * (Delta+1)^(2*m) := by simp

theorem rooted_zero (G : SimpleGraph V) (r : V) : rooted G r 0 = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro A hA
  obtain ⟨hr,hm,hc⟩ := (mem_rooted G r 0 A).mp hA
  have he : A = ∅ := Finset.card_eq_zero.mp hm
  simpa [he] using hr

/-- The singleton is connected for every graph; no edge premise is needed. -/
theorem rooted_one (G : SimpleGraph V) (r : V) : rooted G r 1 = {{r}} := by
  classical
  have hc : (G.induce (({r} : Finset V) : Set V)).Connected := by
    letI : Nonempty {x : V // x ∈ ({r} : Finset V)} := ⟨⟨r,by simp⟩⟩
    letI : Subsingleton {x : V // x ∈ ({r} : Finset V)} := ⟨by
      intro x y
      apply Subtype.ext
      exact (Finset.mem_singleton.mp x.property).trans (Finset.mem_singleton.mp y.property).symm⟩
    exact SimpleGraph.Connected.of_subsingleton
  ext A
  rw [mem_rooted,Finset.mem_singleton]
  constructor
  · rintro ⟨hr,hm,hconnected⟩
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hm
    rw [ha] at hr
    have hra : r = a := Finset.mem_singleton.mp hr
    simpa only [hra] using ha
  · intro he
    subst A
    exact ⟨by simp,by simp,hc⟩

/-- Degree zero includes every size, without a hidden positivity hypothesis. -/
theorem rooted_degree_zero (G : SimpleGraph V)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} = 0) (r : V) (m : Nat) :
    (rooted G r m).card ≤ 1 := by
  simpa using rooted_card_le G 0 (fun v => (hd v).le) r m

theorem anchored_empty (G : SimpleGraph V) (m : Nat) : anchored G ∅ m = ∅ := by
  classical
  simp [anchored_eq_biUnion]

theorem anchored_zero (G : SimpleGraph V) (R : Finset V) : anchored G R 0 = ∅ := by
  classical
  rw [anchored_eq_biUnion]
  apply Finset.eq_empty_of_forall_notMem
  intro A hA
  obtain ⟨r,hr,hroot⟩ := Finset.mem_biUnion.mp hA
  rw [rooted_zero] at hroot
  simpa using hroot

/-- A genuine degree-zero graph satisfies the same bound without division. -/
theorem anchored_degree_zero (G : SimpleGraph V)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} = 0) (R : Finset V) (m : Nat) :
    (anchored G R m).card ≤ R.card := by
  simpa using anchored_card_le G 0 (fun r => (hd r).le) R m

/-- No root is manufactured when the ambient type itself is empty. -/
theorem anchored_isEmpty [IsEmpty V] (G : SimpleGraph V) (R : Finset V) (m : Nat) :
    anchored G R m = ∅ := by
  have hR : R = ∅ := by
    ext x
    exact isEmptyElim x
  rw [hR]
  exact anchored_empty G m

end QEC.Locality.ConnectedSetCounting
