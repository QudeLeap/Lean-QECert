import QEC.Coding.QuditQubitConversion.AppendixANF.Certificate

/-! Literal cubic target data for the WHY24 Appendix-A ANF certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

/-- The seventy cubic terms printed in the literal WHY24 Appendix-A list. -/
def cubicGateTriples : List (Fin 10 × Fin 10 × Fin 10) :=
  [(0, 1, 2), (0, 1, 4), (0, 1, 5), (0, 1, 7), (0, 1, 8),
   (0, 1, 9), (0, 2, 3), (0, 2, 4), (0, 2, 7), (0, 2, 8),
   (0, 3, 4), (0, 3, 5), (0, 3, 9), (0, 4, 9), (0, 5, 6),
   (0, 5, 8), (0, 6, 7), (0, 6, 8), (0, 6, 9), (0, 7, 9),
   (0, 8, 9),
   (1, 2, 3), (1, 2, 5), (1, 2, 6), (1, 2, 8), (1, 2, 9),
   (1, 3, 4), (1, 3, 5), (1, 3, 8), (1, 3, 9), (1, 4, 5),
   (1, 4, 6), (1, 6, 7), (1, 6, 9), (1, 7, 8), (1, 7, 9),
   (2, 3, 4), (2, 3, 6), (2, 3, 7), (2, 3, 9), (2, 4, 5),
   (2, 4, 6), (2, 4, 9), (2, 5, 6), (2, 5, 7), (2, 7, 8),
   (2, 8, 9),
   (3, 4, 5), (3, 4, 7), (3, 4, 8), (3, 5, 6), (3, 5, 7),
   (3, 6, 7), (3, 6, 8), (3, 8, 9),
   (4, 5, 6), (4, 5, 8), (4, 5, 9), (4, 6, 7), (4, 6, 8),
   (4, 7, 8), (4, 7, 9),
   (5, 6, 7), (5, 6, 9), (5, 7, 8), (5, 7, 9), (5, 8, 9),
   (6, 7, 8), (6, 8, 9), (7, 8, 9)]

/-- Normalized target coefficient of one increasing cubic monomial. -/
def cubicGateCoefficient (first second third : Fin 10) : ZMod 2 :=
  if (first, second, third) ∈ cubicGateTriples then 1 else 0

/-- Named cubic source coefficient used by separately compiled certificates. -/
def sourceTripleCoefficient (first second third : Fin 10) : ZMod 2 :=
  sourceCoefficient {first, second, third}

end QEC.Coding.Why24AppendixANF
