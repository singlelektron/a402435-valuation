module

public import MathMiner.Problems.A402435.EvenBranch
public import MathMiner.Problems.A402435.Mod16Recurrence
public import MathMiner.Problems.A402435.OddProof

namespace MathMiner.A402435

/-- The exact valuation at every positive even index. -/
public theorem valuation_even (j : ℕ) :
    padicValNat 2 (diagonal (2*j+2)) + correction (2*j+2) = (2*j+2)+1 :=
  even_branch_of_residue j ⟨diagonalK j, diagonalK_integral j⟩ rfl
    (reduce16_of_tanK psTan_recurrence diagonalK_recurrence diagonalK_zero j)

/-- Luschny's exact binary valuation formula for the weighted Entringer diagonal. -/
public theorem solution : Statement := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    simpa only [show n = 2*j+2 by omega] using valuation_even j
  · simpa only [show n = 2*k+1 by omega] using valuation_odd k

end MathMiner.A402435
