module

public import MathMiner.Problems.A402435.OddCoefficients
public import MathMiner.Problems.A402435.TangentSeries
public import MathMiner.Problems.A402435.TangentRecurrence
public import MathMiner.Problems.A402435.IntegralRecurrence

namespace MathMiner.A402435

open PowerSeries

/-- Normalized coefficients of the odd part of the diagonal generating series. -/
public noncomputable abbrev diagonalK := tanNormalized (oddPart psY)

public theorem diagonalK_zero : diagonalK 0 = 1 := by
  unfold diagonalK tanNormalized
  rw [coeff_oddPart_odd, coeff_psY]
  norm_num [yCoeff, show diagonal 2 = 1 by decide]

public theorem diagonalK_recurrence :
    TanKRecurrence (fun i => coeff (2*i+1) psTan) diagonalK :=
  tanKRecurrence_of_series _ _ coeff_psTan_even psTan_recurrence.1
    (series_odd_elimination _ _ _ _ _ psCos_derivative psSin_derivative
      psCos_sq_add_psSin_sq psCos_mul_psTan psCos_ne_zero
      psY_split_equation.1 psY_split_equation.2)

public theorem diagonalK_integral (j : ℕ) : diagonalK j ∈ oddDenom :=
  K_mem_oddDenom psTan_recurrence diagonalK_recurrence (diagonalK_zero ▸ oddDenom.one_mem) j

/-- The locked exact valuation formula at every positive odd index. -/
public theorem valuation_odd (m : ℕ) :
    padicValNat 2 (diagonal (2*m+1)) + correction (2*m+1) = (2*m+1)+1 :=
  odd_branch_of_series_coeffs _ _ psY_split_equation.1
    (fun j => by simp) (fun j => by simp)
    (fun j => by simpa [diagonalK, tanNormalized] using diagonalK_integral j) m

/-- At odd indices the valuation is the valuation of the preceding factorial. -/
public theorem valuation_odd_factorial (m : ℕ) :
    padicValNat 2 (diagonal (2*m+1)) = padicValNat 2 (2*m).factorial :=
  (odd_branch_iff_factorial m).mp (valuation_odd m)

end MathMiner.A402435
