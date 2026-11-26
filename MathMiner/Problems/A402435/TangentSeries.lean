module

public import MathMiner.Problems.A402435.SeriesParity
public import MathMiner.Problems.A402435.TanRecurrence
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

namespace MathMiner.A402435

open PowerSeries Finset

/-- The ordinary tangent series, with formal cosine a unit. -/
@[expose] public noncomputable def psTan : PowerSeries ℚ := psCos⁻¹ * psSin

public theorem psCos_mul_psTan : psCos * psTan = psSin := by
  rw [psTan, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), one_mul]

public theorem psTan_derivative : derivative psTan = 1 + psTan ^ 2 := by
  have h := congrArg (derivative (R := ℚ)) psCos_mul_psTan
  simp only [Derivation.leibniz, smul_eq_mul, psCos_derivative, psSin_derivative] at h
  apply mul_left_cancel₀ psCos_ne_zero
  linear_combination h - psTan * psCos_mul_psTan

public theorem coeff_psTan_even (j : ℕ) : coeff (2*j) psTan = 0 := by
  have eqn := congrArg seriesReflect psCos_mul_psTan
  rw [map_mul, seriesReflect_psCos, seriesReflect_psSin] at eqn
  have hreflect : seriesReflect psTan = -psTan := by
    apply mul_left_cancel₀ psCos_ne_zero
    rw [eqn, mul_neg, psCos_mul_psTan]
  have e := congrArg (coeff (R := ℚ) (2*j)) hreflect
  change coeff (2*j) (rescale (-1 : ℚ) psTan) = coeff (2*j) (-psTan) at e
  rw [coeff_rescale, map_neg, (show Even (2*j) from ⟨j, by omega⟩).neg_one_pow, one_mul] at e
  linarith

/-- The odd coefficients of tangent obey an integral convolution divided by an odd integer. -/
public theorem psTan_recurrence :
    TangentRecurrence (fun i => coeff (2*i+1) psTan) := by
  constructor
  · have h := congrArg (coeff (R := ℚ) 0) psTan_derivative
    have z : constantCoeff psTan = 0 := by simpa [coeff_zero_eq_constantCoeff_apply] using coeff_psTan_even 0
    rw [coeff_derivative, map_add, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, map_one, map_pow, z] at h
    simpa using h
  · intro n
    have h := congrArg (coeff (R := ℚ) (2*(n+1))) psTan_derivative
    rw [coeff_derivative, map_add, coeff_one, ite_eq_right (by omega), zero_add, sq, coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, coeff_psTan_even, zero_mul,
      add_zero, sum_range_pairs] at h
    simp only [coeff_psTan_even, zero_mul, zero_add] at h
    convert h using 1
    · push_cast
      ring
    · apply sum_congr rfl
      intro k hk
      have := mem_range.mp hk
      rw [show 2*(n+1)-(2*k+1) = 2*(n-k)+1 by omega]

end MathMiner.A402435
