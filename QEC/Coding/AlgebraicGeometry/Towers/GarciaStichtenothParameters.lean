/-
Copyright (c) 2026 The Lean-QEC authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EnjiXiong
-/
import Mathlib

/-!
# Fixed F1024 Garcia--Stichtenoth parameter arithmetic (#887)

WHY24 `main.tex:1976-2002` specializes the Garcia--Stichtenoth tower at
`l = 32`.  For levels `i = 2r + 3` and `i = 2r + 4`, respectively, its two
displayed genus branches normalize to the definitions below.  The selected
place count and divisor/code parameters are the exact floor expressions in
`main.tex:1945-1962` and `1979-2002`; division of natural numbers by the
positive denominator is that floor.

This module proves only the arithmetic layer of the fixed family.  It does
not postulate a tower, a place count, a divisor, a code, or any asymptotic
conclusion: the surrounding construction must later establish that these
expressions are the parameters of the actual Garcia--Stichtenoth levels.
-/

namespace QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters

/-- The WHY24/GS95 odd-index genus branch at level `i = 2r + 3`, with `l = 32`. -/
def oddGenus (r : ℕ) : ℕ :=
  33 * 32 ^ (2 * r + 2) - 34 * 32 ^ (r + 1) + 1

/-- The WHY24/GS95 even-index genus branch at level `i = 2r + 4`, with `l = 32`. -/
def evenGenus (r : ℕ) : ℕ :=
  33 * 32 ^ (2 * r + 3) - 561 * 32 ^ (r + 1) + 1

/-- WHY24's selected `n' = floor (123 g / 4)` rational-place budget. -/
def selectedPlaceCount (g : ℕ) : ℕ :=
  123 * g / 4

/-- WHY24's selected divisor degree `a = floor (9 g / 2)`. -/
def selectedDivisorDegree (g : ℕ) : ℕ :=
  9 * g / 2

/-- WHY24's selected encoded-logical count `k = floor (5 g / 4)`. -/
def selectedLogicalCount (g : ℕ) : ℕ :=
  5 * g / 4

/-- WHY24's candidate decoder radius `t = floor (g / 8)`. -/
def selectedDecodingRadius (g : ℕ) : ℕ :=
  g / 8

/-- WHY24's one-place auxiliary divisor degree `floor (9 g / 8)`. -/
def selectedAuxiliaryDegree (g : ℕ) : ℕ :=
  9 * g / 8

/-- The exact large-degree AG-code dimension expression `m = a + 1 - g`
used before the systematic puncture. -/
def selectedCodeDimension (g : ℕ) : ℕ :=
  selectedDivisorDegree g + 1 - g

/-- The source's lower bound for the punctured quantum-code distance,
`a - k - (2 g - 2)`.  The definition is written in `ℕ` because all selected
levels later prove this expression lies in the nontruncated range. -/
def selectedDistanceLowerBound (g : ℕ) : ℕ :=
  selectedDivisorDegree g - selectedLogicalCount g - 2 * g + 2

/-- The lower side of WHY24's physical-length sandwich after puncturing,
`floor (114 g / 4) - 3`. -/
def selectedPhysicalLengthLowerBound (g : ℕ) : ℕ :=
  114 * g / 4 - 3

/-- The upper side of WHY24's physical-length sandwich after puncturing,
`floor (118 g / 4) - 1`. -/
def selectedPhysicalLengthUpperBound (g : ℕ) : ℕ :=
  118 * g / 4 - 1

/-- The lower side of the size range for the surviving evaluation-place set
after the at-most-`g` zero-residue places are removed: `n' - 2 - g`. -/
def selectedEvaluationPlaceLowerBound (g : ℕ) : ℕ :=
  selectedPlaceCount g - 2 - g

/-- The upper side of the size range for the surviving evaluation-place set:
`n' - 2`. -/
def selectedEvaluationPlaceUpperBound (g : ℕ) : ℕ :=
  selectedPlaceCount g - 2

/-- The degree of the source-selected effective divisor `E`, namely
`n' - 4 + g - 7a`. -/
def selectedEDegree (g : ℕ) : ℕ :=
  selectedPlaceCount g - 4 + g - 7 * selectedDivisorDegree g

/-- The GS95/WHY24 rational-place lower bound at odd level `i = 2r + 3`,
before the zero-residue places are removed. -/
def oddPlaceLowerBound (r : ℕ) : ℕ :=
  1023 * 32 ^ (2 * r + 2) + 64

/-- The GS95/WHY24 rational-place lower bound at even level `i = 2r + 4`,
before the zero-residue places are removed. -/
def evenPlaceLowerBound (r : ℕ) : ℕ :=
  1023 * 32 ^ (2 * r + 3) + 64

/-- The first odd source level is the actual level `i = 3` genus value. -/
theorem oddGenus_zero : oddGenus 0 = 32705 := by
  norm_num [oddGenus]

/-- The first even source level is the actual level `i = 4` genus value. -/
theorem evenGenus_zero : evenGenus 0 = 1063393 := by
  norm_num [evenGenus]

/-- The `i = 3` selected rational-place budget is derived from the genus formula. -/
theorem selectedPlaceCount_oddGenus_zero : selectedPlaceCount (oddGenus 0) = 1005678 := by
  norm_num [selectedPlaceCount, oddGenus]

/-- The `i = 3` selected divisor degree is derived from the genus formula. -/
theorem selectedDivisorDegree_oddGenus_zero : selectedDivisorDegree (oddGenus 0) = 147172 := by
  norm_num [selectedDivisorDegree, oddGenus]

/-- The `i = 3` logical count is derived from the genus formula. -/
theorem selectedLogicalCount_oddGenus_zero : selectedLogicalCount (oddGenus 0) = 40881 := by
  norm_num [selectedLogicalCount, oddGenus]

/-- The `i = 3` candidate decoding radius is derived from the genus formula. -/
theorem selectedDecodingRadius_oddGenus_zero : selectedDecodingRadius (oddGenus 0) = 4088 := by
  norm_num [selectedDecodingRadius, oddGenus]

/-- The `i = 3` pre-puncture AG-code dimension is derived from its selected
divisor degree and closed genus formula. -/
theorem selectedCodeDimension_oddGenus_zero : selectedCodeDimension (oddGenus 0) = 114468 := by
  norm_num [selectedCodeDimension, selectedDivisorDegree, oddGenus]

/-- The `i = 3` source distance lower bound is derived arithmetically, not
stored as a distance claim about an unconstructed code. -/
theorem selectedDistanceLowerBound_oddGenus_zero :
    selectedDistanceLowerBound (oddGenus 0) = 40883 := by
  norm_num [selectedDistanceLowerBound, selectedDivisorDegree,
    selectedLogicalCount, oddGenus]

/-- The first odd GS level's source rational-place lower bound. -/
theorem oddPlaceLowerBound_zero : oddPlaceLowerBound 0 = 1047616 := by
  norm_num [oddPlaceLowerBound]

/-- The `i = 3` lower physical-length expression in WHY24's sandwich. -/
theorem selectedPhysicalLengthLowerBound_oddGenus_zero :
    selectedPhysicalLengthLowerBound (oddGenus 0) = 932089 := by
  norm_num [selectedPhysicalLengthLowerBound, oddGenus]

/-- The `i = 3` upper physical-length expression in WHY24's sandwich. -/
theorem selectedPhysicalLengthUpperBound_oddGenus_zero :
    selectedPhysicalLengthUpperBound (oddGenus 0) = 964796 := by
  norm_num [selectedPhysicalLengthUpperBound, oddGenus]

/-- The selected `E` divisor at `i = 3` has positive degree, as required by
the source construction. -/
theorem selectedEDegree_oddGenus_zero : selectedEDegree (oddGenus 0) = 8175 := by
  norm_num [selectedEDegree, selectedPlaceCount, selectedDivisorDegree, oddGenus]

/-- At `i = 3`, the source's residue-filter argument leaves at least this
many genuine evaluation places once its tower/place construction is supplied. -/
theorem selectedEvaluationPlaceLowerBound_oddGenus_zero :
    selectedEvaluationPlaceLowerBound (oddGenus 0) = 972971 := by
  norm_num [selectedEvaluationPlaceLowerBound, selectedPlaceCount, oddGenus]

/-- At `i = 3`, the source's residue-filter argument leaves no more than this
many genuine evaluation places. -/
theorem selectedEvaluationPlaceUpperBound_oddGenus_zero :
    selectedEvaluationPlaceUpperBound (oddGenus 0) = 1005676 := by
  norm_num [selectedEvaluationPlaceUpperBound, selectedPlaceCount, oddGenus]

/-- The exact `i = 3` lower evaluation-place budget exceeds the selected
divisor degree, which is the numerical part of evaluation injectivity. -/
theorem selectedDivisorDegree_lt_selectedEvaluationPlaceLowerBound_oddGenus_zero :
    selectedDivisorDegree (oddGenus 0) < selectedEvaluationPlaceLowerBound (oddGenus 0) := by
  norm_num [selectedDivisorDegree, selectedEvaluationPlaceLowerBound,
    selectedPlaceCount, oddGenus]

end QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
