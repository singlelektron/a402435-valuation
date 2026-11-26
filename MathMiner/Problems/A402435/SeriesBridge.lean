module

public import MathMiner.Problems.A402435.NormalizedNewton
public import MathMiner.Problems.A402435.SeriesElimination
public import MathMiner.Problems.A402435.SeriesTrig
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

open Finset PowerSeries

/-- The factorial-squared generating series of the shifted diagonal. -/
public noncomputable def psY : PowerSeries ℚ := PowerSeries.mk yCoeff

@[simp] public theorem coeff_psY (n : ℕ) : coeff n psY = yCoeff n := PowerSeries.coeff_mk ..

public theorem seriesL_coeff_eq (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (seriesL f) = ((n : ℚ)+1)^2 * coeff (n+1) f := by
  rw [seriesL, coeff_derivative, coeff_succ_X_mul, coeff_derivative]
  ring

private theorem coeff_mul_range (f g : PowerSeries ℚ) (r : ℕ) :
    coeff r (f*g) = ∑ j ∈ range (r+1), coeff j f * coeff (r-j) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Split a finite coefficient sum into adjacent even and odd indices. -/
public theorem sum_range_pairs (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range (2*m), f i = ∑ j ∈ range m, (f (2*j) + f (2*j+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih]
    ring

/-- The normalized Newton recurrence as one differential equation for the series. -/
public theorem psY_newton_equation : (1-psSin)*seriesL psY = psCos*psY := by
  have eqn : seriesL psY = psCos*psY + psSin*seriesL psY := by
    apply PowerSeries.ext
    intro r
    rw [seriesL_coeff_eq, coeff_psY, normalized_newton, map_add, coeff_mul_range,
      coeff_mul_range, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [psSin, psCos, PowerSeries.sin, PowerSeries.cos, coeff_mk,
      coeff_psY, seriesL_coeff_eq]
    by_cases hj : Even j <;> simp [hj, ← Nat.even_iff]
  linear_combination eqn

/-- Equivalent form suited to splitting the even and odd components. -/
public theorem psY_cos_equation : psCos * seriesL psY = (1+psSin)*psY := by
  apply mul_left_cancel₀ psCos_ne_zero
  linear_combination (1+psSin)*psY_newton_equation + seriesL psY*psCos_sq_add_psSin_sq

end MathMiner.A402435
