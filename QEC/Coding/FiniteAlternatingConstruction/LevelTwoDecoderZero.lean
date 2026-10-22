import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.History

/-!
# Zero normalization of the actual physical C2 selector

The executable local-first search accepts its first enumerated word, zero.
All physical-C2 wrappers preserve this equation. No statement about an
arbitrary right inverse or about earlier correction-history entries is made.
-/
namespace QEC.Coding.BDL26LevelTwoDecoder

open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

/-- Binary enumeration starts with zero even when the list repeats coordinates. -/
theorem wordsOn_zero_first {α : Type} [DecidableEq α] (qs : List α) :
    ∃ tail, wordsOn qs = (0 : Word (ZMod 2) α) :: tail := by
  induction qs with
  | nil => exact ⟨[], rfl⟩
  | cons q qs ih =>
      obtain ⟨tail, htail⟩ := ih
      have hz : Function.update (0 : Word (ZMod 2) α) q 0 = 0 := by
        funext a
        by_cases h : a = q <;> simp [h]
      refine ⟨tail.map (fun e => Function.update e q 0) ++
        (wordsOn qs).map (fun e => Function.update e q 1), ?_⟩
      simp only [wordsOn, htail, List.map_cons, List.cons_append, hz]

/-- The actual complete error table begins with zero. -/
theorem allWords_zero_first (α : Type) [Fintype α] [Encodable α] [DecidableEq α] :
    ∃ tail, allWords α = (0 : Word (ZMod 2) α) :: tail :=
  wordsOn_zero_first (coordinates α)

/-- Search returns a passing head before inspecting its tail. -/
theorem search_head {α : Type} (accept : α → Bool) (a : α) (tail : List α)
    (ha : accept a = true) : search accept (a :: tail) = some a := by
  simp [search, ha]

/-- A local zero head is chosen by the first, local-only search. -/
theorem lookup_zero_of_zero_first {Error Syndrome : Type} [Zero Error]
    [Zero Syndrome] [DecidableEq Syndrome] (entries : List Error)
    (syndrome : Error → Syndrome) (isLocal : Error → Bool) (fallback : Error)
    (hfirst : ∃ tail, entries = 0 :: tail) (hlocal : isLocal 0 = true)
    (hsyndrome : syndrome 0 = 0) :
    lookup entries syndrome isLocal fallback 0 = 0 := by
  obtain ⟨tail, rfl⟩ := hfirst
  simp [lookup, search, hlocal, hsyndrome]

/-- Every finite incidence syndrome vanishes on zero. -/
theorem syndromeFromBits_zero {Q Z : Type} (F : Fintype Q)
    (incidence : Q → Z → Bool) : syndromeFromBits F incidence 0 = 0 := by
  funext z
  simp [syndromeFromBits]

/-- The literal RZ incidence computation vanishes on zero. -/
theorem rawSyndrome_zero (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale) :
    rawSyndrome P hasA S 0 = 0 := syndromeFromBits_zero _ _

/-- An actual owner witnesses the vacuous zero-support locality condition. -/
theorem rawLocal_zero (P : TannerSquarePresentation) (S : OddScale)
    (center : Vertex P) : rawLocal P S 0 = true := by
  apply decide_eq_true
  exact ⟨center, by intro q h; exact (h rfl).elim⟩

/-- Concrete first-level coordinate transported to the executable presentation. -/
def executableOwnerAtZero (S : OddScale) : Vertex (executableLevelOne S) :=
  Vertex.q (cast (congrArg (fun P : TannerSquarePresentation => P.Q)
    (executableLevelOne_eq S)).symm (levelOneQDefault S))

theorem executableLocal_zero (S : OddScale) : executableLocal S 0 = true :=
  rawLocal_zero _ S (executableOwnerAtZero S)

theorem executableSyndrome_zero (S : OddScale) : executableSyndrome S 0 = 0 :=
  rawSyndrome_zero _ _ S

/-- Actual executable selector normalization, with every lookup premise derived. -/
theorem executableDecode_zero (S : OddScale) : executableDecode S 0 = 0 := by
  apply lookup_zero_of_zero_first
  · exact allWords_zero_first _
  · exact executableLocal_zero S
  · exact executableSyndrome_zero S

theorem toExecutableSyndrome_zero (S : OddScale) : toExecutableSyndrome S 0 = 0 := rfl

theorem toActualError_zero (S : OddScale) : toActualError S 0 = 0 := rfl

/-- The existing actual physical-C2 cochain decoder, including both casts. -/
theorem decode_zero (S : OddScale) : decode S 0 = 0 := by
  unfold decode
  rw [toExecutableSyndrome_zero, executableDecode_zero, toActualError_zero]

/-- The existing F17 adapter stores exactly the same zero-normalized function. -/
theorem baseAdapter_decode_zero (S : OddScale) : (baseAdapter S).decode 0 = 0 :=
  decode_zero S

end QEC.Coding.BDL26LevelTwoDecoder

namespace QEC.Coding.BDL26OwnerIncidenceMasks

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge MultiscaleDecoder

/-- Suffix index zero is physical C2, at every total depth n+2. -/
theorem actualBaseDecode_zero (S : OddScale) (n : Nat) : actualBaseDecode S n 0 = 0 :=
  BDL26LevelTwoDecoder.decode_zero S

/-- The actual stopped-history base stores the physical-C2 selector unchanged. -/
theorem actualBase_decode_zero (S : OddScale) (n : Nat) :
    (actualBase S n).decode 0 = 0 := actualBaseDecode_zero S n

end QEC.Coding.BDL26OwnerIncidenceMasks
