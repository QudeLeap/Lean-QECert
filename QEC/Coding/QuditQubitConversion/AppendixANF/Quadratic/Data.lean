import QEC.Coding.QuditQubitConversion.AppendixANF.Certificate

/-! Literal quadratic target data for the WHY24 Appendix-A ANF certificate. -/

noncomputable section

namespace QEC.Coding.Why24AppendixANF

/-- The twenty quadratic terms printed in the literal WHY24 Appendix-A list. -/
def quadraticGatePairs : List (Fin 10 × Fin 10) :=
  [(0, 1), (0, 4), (0, 6), (0, 9),
   (1, 2), (1, 5), (1, 7),
   (2, 3), (2, 6), (2, 8),
   (3, 4), (3, 7), (3, 9),
   (4, 5), (4, 8),
   (5, 6), (5, 9),
   (6, 7), (7, 8), (8, 9)]

/-- Normalized target coefficient of one increasing quadratic monomial. -/
def quadraticGateCoefficient (left right : Fin 10) : ZMod 2 :=
  if (left, right) ∈ quadraticGatePairs then 1 else 0

/-- Named pair-coefficient interface used to compose the independent closed
certificates without unfolding the tensor calculation during index cases. -/
def sourcePairCoefficient (left right : Fin 10) : ZMod 2 :=
  sourceCoefficient {left, right}

end QEC.Coding.Why24AppendixANF
