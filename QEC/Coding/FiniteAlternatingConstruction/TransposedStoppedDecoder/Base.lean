import QEC.Coding.FiniteAlternatingConstruction.TransposedStoppedDecoder.LocalSteps
import QEC.Coding.FiniteAlternatingConstruction.CSSHamiltonian.Rows

/-!
# Literal transposed physical-C2 lookup

The table is the entire original executable physical error enumeration, cast
once to its original actual carrier. The first search uses a single owner
fibre of the materialized dual RX replacement. The second search uses the
same table and the same actual dual syndrome. No decoder correctness input
or independently chosen representative is supplied.
-/

noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical

/-- Physical C2 errors, retaining the existing executable coordinate order. -/
def dualBaseTable (S : OddScale) : List (Word BDL26Field (dualPresentation S 2).Q) :=
  (allWords (ExecutableQ S)).map (toActualError S)

/-- Completeness concerns the whole physical table, not a selected subdomain. -/
theorem mem_dualBaseTable (S : OddScale) (e : Word BDL26Field (dualPresentation S 2).Q) :
    e ∈ dualBaseTable S := by
  apply List.mem_map.mpr
  exact ⟨toExecutableError S e,mem_allWords _ _,toActualError_toExecutableError S e⟩

/-- The actual dual RX owner of a physical C2 coordinate. -/
def dualBaseOwner (S : OddScale) (q : (dualPresentation S 2).Q) :
    Vertex (transposePresentation (state S 1).presentation) :=
  rxCorrectionOwner (transposePresentation (state S 1).presentation) S
    (rzDualQ (state S 1).presentation S q)

/-- The approved owner-local test on actual physical error support. -/
def dualBaseLocal (S : OddScale) (e : Word BDL26Field (dualPresentation S 2).Q) : Bool :=
  decide (∃ center : Vertex (transposePresentation (state S 1).presentation),
    ∀ q, e q ≠ 0 → dualBaseOwner S q = center)

/-- The exact original local-first, whole-table-fallback lookup rule. -/
def dualBaseDecode (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z) :
    Word BDL26Field (dualPresentation S 2).Q :=
  lookup (dualBaseTable S) (tannerCoboundary1 (dualPresentation S 2))
    (dualBaseLocal S) 0 sigma

theorem dualBaseDecode_syndrome (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (h : sigma ∈ LinearMap.range (tannerCoboundary1 (dualPresentation S 2))) :
    tannerCoboundary1 (dualPresentation S 2) (dualBaseDecode S sigma) = sigma := by
  obtain ⟨e,he⟩ := h
  exact lookup_syndrome _ _ _ _ _ ⟨e,mem_dualBaseTable S e,he⟩

theorem dualBaseDecode_local (S : OddScale)
    (e : Word BDL26Field (dualPresentation S 2).Q) (h : dualBaseLocal S e = true) :
    dualBaseLocal S (dualBaseDecode S (tannerCoboundary1 (dualPresentation S 2) e)) = true :=
  lookup_local _ _ _ _ _ ⟨e,mem_dualBaseTable S e,h,rfl⟩

/-- Zero is the first word in the original recursive enumeration. -/
private theorem wordsOn_zero_head {A : Type} [DecidableEq A] (qs : List A) :
    ∃ tail, wordsOn qs = (0 : Word (ZMod 2) A) :: tail := by
  induction qs with
  | nil => exact ⟨[],rfl⟩
  | cons q qs ih =>
      obtain ⟨tail,ht⟩ := ih
      refine ⟨tail.map (fun e => Function.update e q 0) ++
        ((0 : Word (ZMod 2) A) :: tail).map (fun e => Function.update e q 1),?_⟩
      have hz : Function.update (0 : Word (ZMod 2) A) q 0 = 0 := by
        funext r
        by_cases h : r = q <;> simp [h]
      simp only [wordsOn,ht,List.map_cons,List.cons_append,hz]

/-- Casting the original table keeps its first zero entry and all later entries. -/
theorem dualBaseTable_zero_head (S : OddScale) :
    ∃ tail, dualBaseTable S = 0 :: tail := by
  obtain ⟨tail,ht⟩ := wordsOn_zero_head (coordinates (ExecutableQ S))
  refine ⟨tail.map (toActualError S),?_⟩
  have hz : toActualError S 0 = 0 := rfl
  change (wordsOn (coordinates (ExecutableQ S))).map (toActualError S) = _
  exact (congrArg (List.map (toActualError S)) ht).trans
    (congrArg (fun e => e :: tail.map (toActualError S)) hz)

@[simp] theorem dualBaseLocal_zero (S : OddScale) : dualBaseLocal S 0 = true := by
  simp only [dualBaseLocal,decide_eq_true_eq]
  exact ⟨Vertex.z (state S 1).selectedX,fun q h => False.elim (h rfl)⟩

/-- The base zero behavior follows from first-match lookup, not a choice axiom. -/
@[simp] theorem dualBaseDecode_zero (S : OddScale) : dualBaseDecode S 0 = 0 := by
  obtain ⟨tail,ht⟩ := dualBaseTable_zero_head S
  simp [dualBaseDecode,lookup,ht,search,dualBaseLocal_zero]

private theorem search_none_of_no_match {A : Type} (entries : List A) (accept : A → Bool)
    (h : ∀ e ∈ entries, accept e = false) : search accept entries = none := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
      have ha := h a (List.mem_cons_self)
      have hr : ∀ e ∈ rest, accept e = false := fun e he => h e (List.mem_cons_of_mem a he)
      simp [search,ha,ih hr]

/-- Off the exact represented image, both searches fail and the original zero default remains. -/
theorem dualBaseDecode_outside_range (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (h : sigma ∉ LinearMap.range (tannerCoboundary1 (dualPresentation S 2))) :
    dualBaseDecode S sigma = 0 := by
  have hn (e : Word BDL26Field (dualPresentation S 2).Q) :
      tannerCoboundary1 (dualPresentation S 2) e ≠ sigma := fun he => h ⟨e,he⟩
  have hf : search (fun e => decide (tannerCoboundary1 (dualPresentation S 2) e = sigma))
      (dualBaseTable S) = none :=
    search_none_of_no_match _ _ (fun e _ => by simp [hn e])
  have hl : search (fun e => dualBaseLocal S e &&
      decide (tannerCoboundary1 (dualPresentation S 2) e = sigma)) (dualBaseTable S) = none :=
    search_none_of_no_match _ _ (fun e _ => by simp [hn e])
  simp only [dualBaseDecode,lookup,hl,hf,Option.getD_none]

/-- The dual physical syndrome is exactly the existing actual X-check syndrome. -/
theorem dual_coboundary1_xSyndrome (S : OddScale) (n : Nat) :
    tannerCoboundary1 (dualPresentation S n) = BDL26CSSHamiltonian.xSyndrome S n :=
  (BDL26CSSHamiltonian.xSyndrome_transposed S n).symm

/-- Same-carrier physical right inverse, derived from the actual finite lookup. -/
theorem dualBaseDecode_xSyndrome (S : OddScale)
    (sigma : Word BDL26Field (BDL26CSSHamiltonian.XLabel S 2))
    (h : sigma ∈ LinearMap.range (BDL26CSSHamiltonian.xSyndrome S 2)) :
    BDL26CSSHamiltonian.xSyndrome S 2 (dualBaseDecode S sigma) = sigma := by
  rw [← dual_coboundary1_xSyndrome] at h ⊢
  exact dualBaseDecode_syndrome S sigma h

/-- The local predicate is transported physical support locality, not syndrome support. -/
theorem dualBaseLocal_materialized_iff (S : OddScale)
    (e : Word BDL26Field (dualPresentation S 2).Q) :
    dualBaseLocal S e = true ↔
      ∃ center : Vertex (transposePresentation (state S 1).presentation),
        ∀ q, wordEquiv (rzDualQ (state S 1).presentation S) e q ≠ 0 →
          rxCorrectionOwner (transposePresentation (state S 1).presentation) S q = center := by
  simp only [dualBaseLocal,decide_eq_true_eq]
  constructor
  · rintro ⟨center,h⟩
    refine ⟨center,fun q hq => ?_⟩
    simpa only [dualBaseOwner,Equiv.apply_symm_apply] using
      h ((rzDualQ (state S 1).presentation S).symm q) hq
  · rintro ⟨center,h⟩
    refine ⟨center,fun q hq => ?_⟩
    apply h (rzDualQ (state S 1).presentation S q)
    have hword := wordEquiv_apply (rzDualQ (state S 1).presentation S) e
      (rzDualQ (state S 1).presentation S q)
    have hinverse := congrArg e ((rzDualQ (state S 1).presentation S).symm_apply_apply q)
    exact fun hzero => hq ((hword.trans hinverse).symm.trans hzero)

/-- A successful first local search is used literally. -/
theorem dualBaseDecode_first_local (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (e : Word BDL26Field (dualPresentation S 2).Q)
    (h : search (fun e => dualBaseLocal S e &&
      decide (tannerCoboundary1 (dualPresentation S 2) e = sigma)) (dualBaseTable S) = some e) :
    dualBaseDecode S sigma = e := by
  simp only [dualBaseDecode,lookup,h]

/-- Failure of the local search retains the exact whole-table fallback. -/
theorem dualBaseDecode_fallback (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z)
    (h : search (fun e => dualBaseLocal S e &&
      decide (tannerCoboundary1 (dualPresentation S 2) e = sigma)) (dualBaseTable S) = none) :
    dualBaseDecode S sigma =
      (search (fun e => decide (tannerCoboundary1 (dualPresentation S 2) e = sigma))
        (dualBaseTable S)).getD 0 := by
  simp only [dualBaseDecode,lookup,h]

end QEC.Coding.BDL26TransposedStoppedDecoder
end
