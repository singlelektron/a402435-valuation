module

public import MathMiner.Problems.A402435.SeriesParity
public import MathMiner.Problems.A402435.TangentRecurrence
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace MathMiner.A402435

/-- The squared odd double factorial contributes a 2-adic unit to the diagonal. -/
public theorem odd_oddDoubleFactorial_sq (j : ℕ) : Odd ((2*j+1).doubleFactorial^2) := by
  apply Odd.pow
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, Nat.doubleFactorial_add_two]
    exact (show Odd (2*j+1+2) from ⟨j+1, by omega⟩).mul ih

/-- Restore the powers of two and the odd factors in the original even diagonal. -/
public theorem even_normalized_scale (j : ℕ) :
    tanNormalized (oddPart psY) j * ((2:ℚ)^(2*j) * (((2*j+1).doubleFactorial^2 : ℕ) : ℚ)) =
      diagonal (2*j+2) := by
  simp only [tanNormalized, coeff_oddPart_odd, coeff_psY, yCoeff, Nat.cast_pow,
    Nat.factorial_eq_mul_doubleFactorial (2*j), Nat.doubleFactorial_two_mul, Nat.cast_mul,
    Nat.cast_ofNat, show 2*j+1+1=2*j+2 by omega]
  rw [show (2:ℚ)^(2*j) = (2^j)^2 by rw [← pow_mul, Nat.mul_comm j 2]]
  have h₁ : ((2*j+1).doubleFactorial : ℚ) ≠ 0 := by positivity
  have h₂ : (j.factorial : ℚ) ≠ 0 := by positivity
  field_simp

end MathMiner.A402435
