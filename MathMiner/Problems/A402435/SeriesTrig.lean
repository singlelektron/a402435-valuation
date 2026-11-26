module

public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

open PowerSeries

/-- Formal sine and cosine over the rationals. -/
public noncomputable abbrev psSin := PowerSeries.sin ℚ
public noncomputable abbrev psCos := PowerSeries.cos ℚ

@[simp] public theorem psSin_constantCoeff : constantCoeff psSin = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply, psSin, PowerSeries.sin]

@[simp] public theorem psCos_constantCoeff : constantCoeff psCos = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply, psCos, PowerSeries.cos]

public theorem psCos_ne_zero : psCos ≠ 0 := by
  intro h
  have := congrArg (constantCoeff (R := ℚ)) h
  simp at this

public theorem psSin_derivative : derivative psSin = psCos := by
  ext n
  rw [coeff_derivative]
  simp only [psSin, psCos, sin, cos, coeff_mk, Algebra.algebraMap_self_apply]
  by_cases he : Even n
  · simp only [Nat.even_add_one, he, not_true_eq_false, ite_false, ite_true]
    have hr : n%2 = 0 := Nat.even_iff.mp he
    rw [show (n+1)/2 = n/2 by omega, Nat.factorial_succ]
    push_cast
    field_simp
  · simp [he, Nat.even_add_one]

public theorem psCos_derivative : derivative psCos = -psSin := by
  ext n
  rw [coeff_derivative, map_neg]
  simp only [psSin, psCos, sin, cos, coeff_mk, Algebra.algebraMap_self_apply]
  by_cases he : Even n
  · simp [he, Nat.even_add_one]
  · simp only [Nat.even_add_one, he, not_false_eq_true, ite_true, ite_false]
    have hr : n%2 = 1 := by simpa [Nat.even_iff, Nat.mod_two_ne_zero] using he
    rw [show (n+1)/2 = n/2+1 by omega, pow_succ, Nat.factorial_succ]
    push_cast
    field_simp

public theorem psCos_sq_add_psSin_sq : psCos^2 + psSin^2 = 1 := by
  apply PowerSeries.derivative.ext
  · rw [map_add, derivative_pow, derivative_pow, psCos_derivative, psSin_derivative,
      derivative_one]
    norm_num
    ring
  · simp

end MathMiner.A402435
