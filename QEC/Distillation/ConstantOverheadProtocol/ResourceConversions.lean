import QEC.Distillation.Universality.AdaptiveIdealClifford

/-!
# Finite T/CCZ resource conversions

Computed inventories, primitive programs and exact batch accounting.
-/

noncomputable section

namespace QEC.Distillation.Why24ConstantOverhead

/-! ## Closed finite T/CCZ resource program -/

/-- The two resource species in WHY24's finite-rate conversion remark. -/
inductive Why24MagicResourceToken
  | t
  | ccz
  deriving DecidableEq, Repr

/-- A computed finite inventory; no claimed conversion result is stored. -/
structure Why24MagicInventory where
  tCount : Nat
  cczCount : Nat
  deriving DecidableEq, Repr

/-- The two source-certified finite stabilizer conversion primitives. -/
inductive Why24FiniteConversionPrimitive
  | fourTToCCZ
  | cczCatalyticT
  deriving DecidableEq, Repr

namespace Why24FiniteConversionPrimitive

/-- Literal resource debits of one primitive. -/
def inputLedger : Why24FiniteConversionPrimitive ->
    AdaptiveIdealClifford.ResourceLedger Why24MagicResourceToken
  | .fourTToCCZ => Multiset.replicate 4 .t
  | .cczCatalyticT => {.ccz, .t}

/-- Literal resource outputs of one primitive. -/
def outputLedger : Why24FiniteConversionPrimitive ->
    AdaptiveIdealClifford.ResourceLedger Why24MagicResourceToken
  | .fourTToCCZ => {.ccz}
  | .cczCatalyticT => Multiset.replicate 3 .t

/-- Apply one primitive only when its literal resources are available. -/
def apply : Why24FiniteConversionPrimitive -> Why24MagicInventory ->
    Option Why24MagicInventory
  | .fourTToCCZ, inventory =>
      if 4 <= inventory.tCount then
        some
          { tCount := inventory.tCount - 4
            cczCount := inventory.cczCount + 1 }
      else none
  | .cczCatalyticT, inventory =>
      if 1 <= inventory.tCount && 1 <= inventory.cczCount then
        some
          { tCount := inventory.tCount + 2
            cczCount := inventory.cczCount - 1 }
      else none

end Why24FiniteConversionPrimitive

/-- Evaluate a closed finite conversion program against its live inventory. -/
def why24RunConversionProgram : List Why24FiniteConversionPrimitive ->
    Why24MagicInventory -> Option Why24MagicInventory
  | [], inventory => some inventory
  | primitive :: program, inventory =>
      (primitive.apply inventory).bind (why24RunConversionProgram program)

/-- `batch` copies of the finite `4 T -> CCZ` primitive. -/
def why24FourTToCCZBatch (batch : Nat) :
    List Why24FiniteConversionPrimitive :=
  List.replicate batch .fourTToCCZ

/-- `batch` sequential catalytic `CCZ + T -> 3 T` primitives. -/
def why24CCZCatalyticTBatch (batch : Nat) :
    List Why24FiniteConversionPrimitive :=
  List.replicate batch .cczCatalyticT

private theorem why24FourTToCCZBatch_run_additionalCCZ
    (batch additionalCCZ : Nat) :
    why24RunConversionProgram (why24FourTToCCZBatch batch)
        { tCount := 4 * batch
          cczCount := additionalCCZ } =
      some
        { tCount := 0
          cczCount := additionalCCZ + batch } := by
  induction batch generalizing additionalCCZ with
  | zero => simp [why24FourTToCCZBatch, why24RunConversionProgram]
  | succ batch ih =>
      rw [show why24FourTToCCZBatch (Nat.succ batch) =
          .fourTToCCZ :: why24FourTToCCZBatch batch by
        simp [why24FourTToCCZBatch, List.replicate_succ]]
      rw [why24RunConversionProgram]
      have happly : Why24FiniteConversionPrimitive.apply .fourTToCCZ
          { tCount := 4 * Nat.succ batch
            cczCount := additionalCCZ } =
          some
            { tCount := 4 * batch
              cczCount := additionalCCZ + 1 } := by
        simp [Why24FiniteConversionPrimitive.apply, Nat.mul_succ]
      rw [happly, Option.bind_some, ih]
      congr 2
      omega

/-- A batch of `4B` T resources computes exactly `B` CCZ resources. -/
theorem why24FourTToCCZBatch_run (batch : Nat) :
    why24RunConversionProgram (why24FourTToCCZBatch batch)
        { tCount := 4 * batch
          cczCount := 0 } =
      some
        { tCount := 0
          cczCount := batch } := by
  simpa using why24FourTToCCZBatch_run_additionalCCZ batch 0

private theorem why24CCZCatalyticTBatch_run_from_seed
    (batch seed : Nat) (hseed : 0 < seed) :
    why24RunConversionProgram (why24CCZCatalyticTBatch batch)
        { tCount := seed
          cczCount := batch } =
      some
        { tCount := seed + 2 * batch
          cczCount := 0 } := by
  induction batch generalizing seed with
  | zero => simp [why24CCZCatalyticTBatch, why24RunConversionProgram]
  | succ batch ih =>
      rw [show why24CCZCatalyticTBatch (Nat.succ batch) =
          .cczCatalyticT :: why24CCZCatalyticTBatch batch by
        simp [why24CCZCatalyticTBatch, List.replicate_succ]]
      rw [why24RunConversionProgram]
      have happly : Why24FiniteConversionPrimitive.apply .cczCatalyticT
          { tCount := seed
            cczCount := Nat.succ batch } =
          some
            { tCount := seed + 2
              cczCount := batch } := by
        have hseedNe : seed ≠ 0 := Nat.ne_of_gt hseed
        simp [Why24FiniteConversionPrimitive.apply, hseedNe]
      rw [happly, Option.bind_some, ih (seed + 2) (by omega)]
      congr 2
      omega

/-- A single seed is returned: `B` CCZ resources produce `2B` fresh T
resources plus that one catalyst. -/
theorem why24CCZCatalyticTBatch_run (batch : Nat) :
    why24RunConversionProgram (why24CCZCatalyticTBatch batch)
        { tCount := 1
          cczCount := batch } =
      some
        { tCount := 2 * batch + 1
          cczCount := 0 } := by
  simpa [add_comm] using why24CCZCatalyticTBatch_run_from_seed batch 1 (by omega)

end QEC.Distillation.Why24ConstantOverhead
