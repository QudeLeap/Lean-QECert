import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.CountedLists
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventEncoding
import Mathlib.Data.List.FinRange

/-! # Counted event rank keys and their actual lexicographic comparator -/
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

noncomputable def triangleInputList (P : TannerSquarePresentation) : List (Triangle P) :=
  List.ofFn (Fintype.equivFin (Triangle P)).symm

theorem triangleInputList_length (P : TannerSquarePresentation) :
    (triangleInputList P).length = Fintype.card (Triangle P) := List.length_ofFn

theorem triangleInputList_index (P : TannerSquarePresentation) (t : Triangle P) :
    (triangleInputList P).idxOf t = triangleKey P t := by
  have hn : (triangleInputList P).Nodup :=
    List.nodup_ofFn_ofInjective (Fintype.equivFin (Triangle P)).symm.injective
  let i : Fin (triangleInputList P).length :=
    ⟨(Fintype.equivFin (Triangle P) t).val,by
      rw [triangleInputList_length]; exact (Fintype.equivFin (Triangle P) t).isLt⟩
  have he : (triangleInputList P)[i.val] = t := by
    simp [triangleInputList,i]
  have h := hn.idxOf_getElem i i.isLt
  rw [he] at h
  exact h

def mapQuery {A B : Type*} (q : A → B × ℕ) : List A → List B × ℕ
  | [] => ([],0)
  | a::L => let qa := q a; let rest := mapQuery q L
            (qa.1::rest.1,qa.2+rest.2+1)

theorem mapQuery_value {A B : Type*} (q : A → B × ℕ) (L : List A) :
    (mapQuery q L).1 = L.map (fun a => (q a).1) := by
  induction L <;> simp_all [mapQuery]

theorem mapQuery_cost_le {A B : Type*} (q : A → B × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (mapQuery q L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [mapQuery]
  | cons a L ih =>
    have ha := hq a (by simp)
    have ht := ih (fun b hb => hq b (by simp [hb]))
    simp only [mapQuery,List.length_cons]
    nlinarith

def lexLEQuery : List ℕ → List ℕ → Bool × ℕ
  | [], _ => (true,1)
  | _::_, [] => (false,1)
  | a::L, b::M => if a < b then (true,1) else if b < a then (false,2) else
      let q := lexLEQuery L M
      (q.1,q.2+2)

theorem lexLEQuery_correct (L M : List ℕ) : (lexLEQuery L M).1 = true ↔ L ≤ M := by
  induction L generalizing M with
  | nil =>
    cases M with
    | nil => simp [lexLEQuery]
    | cons b M =>
      have h : ([] : List ℕ) < b::M := List.Lex.nil
      simp [lexLEQuery,h.le]
  | cons a L ih =>
    cases M with
    | nil =>
      have h : ([] : List ℕ) < a::L := List.Lex.nil
      have hn : ¬(a::L ≤ ([] : List ℕ)) := fun hx => (lt_irrefl _) (lt_of_lt_of_le h hx)
      simp [lexLEQuery,hn]
    | cons b M =>
      by_cases hab : a < b
      · have h : a::L < b::M := List.Lex.rel hab
        simp [lexLEQuery,hab,h.le]
      · by_cases hba : b < a
        · have h : b::M < a::L := List.Lex.rel hba
          have hn : ¬(a::L ≤ b::M) := fun hx => (lt_irrefl _) (lt_of_lt_of_le h hx)
          simp [lexLEQuery,hab,hba,hn]
        · have he : a = b := by omega
          subst b
          simp only [lexLEQuery,lt_self_iff_false,if_false,ih]
          rw [le_iff_lt_or_eq,le_iff_lt_or_eq]
          change (List.Lex (· < ·) L M ∨ L = M) ↔
            (List.Lex (· < ·) (a::L) (a::M) ∨ a::L = a::M)
          rw [List.lex_cons_iff,List.cons.injEq]
          simp

theorem lexLEQuery_cost_le (L M : List ℕ) : (lexLEQuery L M).2 ≤ 2*L.length+1 := by
  induction L generalizing M with
  | nil => simp [lexLEQuery]
  | cons a L ih =>
    cases M with
    | nil => simp [lexLEQuery]
    | cons b M =>
      have ht := ih M
      simp only [lexLEQuery,List.length_cons]
      split_ifs <;> omega

noncomputable def eventKeyQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) : List ℕ × ℕ :=
  let raw := mapQuery (fun t => indexQuery t (triangleInputList P)) e.val.toList
  let sorted := sortQuery (fun a b : ℕ => (decide (a ≤ b),1)) raw.1
  (sorted.1,raw.2+sorted.2)

-- The cost includes input rank lookup and the four-element key sort.
-- The following proofs identify the key and comparator used by the actual scan.


theorem eventKeyQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) :
    (eventKeyQuery P J radius e).1 = eventScanKey P J radius e := by
  let raw := e.val.toList.map (triangleKey P)
  have hn : raw.Nodup := e.val.nodup_toList.map (triangleKey_injective P)
  have he : raw.toFinset = e.val.image (triangleKey P) := by
    ext n
    simp [raw,List.mem_toFinset,List.mem_map,Finset.mem_image,Finset.mem_toList]
  have hperm : List.Perm ((e.val.image (triangleKey P)).sort (· ≤ ·)) raw := by
    rw [← he]
    exact (Finset.sort_perm_toList _ _).trans (List.toFinset_toList hn)
  have hsort : (e.val.image (triangleKey P)).sort (· ≤ ·) = raw.insertionSort (· ≤ ·) :=
    (hperm.trans (List.perm_insertionSort (· ≤ ·) raw).symm).eq_of_pairwise'
      (Finset.pairwise_sort _ _) (List.pairwise_insertionSort _ _)
  change (sortQuery (fun a b : ℕ => (decide (a ≤ b),1))
    (mapQuery (fun t => indexQuery t (triangleInputList P)) e.val.toList).1).1 = _
  rw [sortQuery_value _ (· ≤ ·) (by intro a b; simp)]
  simp only [mapQuery_value,indexQuery_value]
  have hi : (fun t => List.idxOf t (triangleInputList P)) = triangleKey P :=
    funext (triangleInputList_index P)
  rw [hi]
  exact hsort.symm

theorem eventKeyQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) :
    (eventKeyQuery P J radius e).2 ≤ 4*(Fintype.card (Triangle P)+1)+50 := by
  let raw := mapQuery (fun t => indexQuery t (triangleInputList P)) e.val.toList
  have hc : raw.2 ≤ 4*(Fintype.card (Triangle P)+1) := by
    have h := mapQuery_cost_le (fun t => indexQuery t (triangleInputList P))
      e.val.toList (Fintype.card (Triangle P)) (fun t _ => by
        simpa only [triangleInputList_length] using indexQuery_cost_le t (triangleInputList P))
    simpa only [Finset.length_toList,e.property.1] using h
  have hlen : raw.1.length = 4 := by
    rw [mapQuery_value,List.length_map,Finset.length_toList,e.property.1]
  have hs : (sortQuery (fun a b : ℕ => (decide (a ≤ b),1)) raw.1).2 ≤ 50 := by
    have h := sortQuery_cost_le (fun a b : ℕ => (decide (a ≤ b),1))
      (· ≤ ·) (by intro a b; simp) 1 (by intro a b; exact le_rfl) raw.1
    norm_num only [hlen] at h
    exact h
  change raw.2+(sortQuery (fun a b : ℕ => (decide (a ≤ b),1)) raw.1).2 ≤ _
  omega

noncomputable def eventCompareQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) : Bool × ℕ :=
  let E := eventKeyQuery P J radius e
  let F := eventKeyQuery P J radius f
  let q := lexLEQuery E.1 F.1
  (q.1,E.2+F.2+q.2)

theorem eventCompareQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) :
    (eventCompareQuery P J radius e f).1 = true ↔
      eventScanKey P J radius e ≤ eventScanKey P J radius f := by
  rw [eventCompareQuery,lexLEQuery_correct,eventKeyQuery_value,eventKeyQuery_value]

theorem eventCompareQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e f : Event P J radius) :
    (eventCompareQuery P J radius e f).2 ≤ 8*(Fintype.card (Triangle P)+1)+109 := by
  have he := eventKeyQuery_cost_le P J radius e
  have hf := eventKeyQuery_cost_le P J radius f
  have hl := lexLEQuery_cost_le (eventKeyQuery P J radius e).1 (eventKeyQuery P J radius f).1
  have hlen : (eventKeyQuery P J radius e).1.length = 4 := by
    rw [eventKeyQuery_value,eventScanKey_length]
  rw [hlen] at hl
  dsimp only [eventCompareQuery]
  omega

end QEC.Coding.BDL26RandomPerturbation
