module

public import MathMiner.Problems.A402435.Moments
public import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

open Finset Function
open scoped fwdDiff

/-- The last step of every row starting with row two adds a multiple of zero. -/
private theorem penultimate (r : ℕ) : row (r+2) (r+1) = diagonal (r+2) := by
  change _ = row (r+2) (r+1) + (r+1-1) * row (r+1) (r+1-(r+1))
  simp [row, nextEntry]

private def line (r k : ℕ) : ℤ := row (r+2) (k+1)

private theorem shift_two (r j : ℕ) (hj : j ≤ r) :
    (Δ_[1]^[j+2] (line (r+2))) 0 =
      (-((r : ℤ)+2) * (r+1)) * (Δ_[1]^[j] (line r)) 0 := by
  have pointwise (k : ℕ) (hk : k ≤ r) :
      (Δ_[1]^[2] (line (r+2))) k = (-((r : ℤ)+2) * (r+1)) * line r k := by
    have h := row_second_difference (n := r+2) (k := k) (by omega)
    rw [show r+2-1=r+1 by omega] at h
    have hz := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at hz
    change (row (r+4) (k+3) : ℤ) - row (r+4) (k+2) -
      ((row (r+4) (k+2) : ℤ) - row (r+4) (k+1)) = _ * (row (r+2) (k+1) : ℤ)
    linarith only [hz]
  rw [iterate_add_apply, fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkr : k ≤ r := by simp at hk; omega
  simp only [nsmul_eq_mul, mul_one, zero_add, zsmul_eq_mul]
  simp only [Nat.cast_id, Int.cast_id]
  rw [pointwise k hkr]
  ring

private theorem diff_at_start (r j : ℕ) (hj : j ≤ r) :
    (Δ_[1]^[j] (line r)) 0 = (-1 : ℤ)^(j/2) * r.descFactorial j *
      diagonal (r+1-2*(j/2)) := by
  induction j using Nat.strong_induction_on generalizing r with
  | ind j ih =>
    rcases j with _ | _ | j
    · simp [line, diagonal, row, nextEntry]
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      change (row (r+3) 2 : ℤ) - row (r+3) 1 = _
      have h : row (r+3) 2 = row (r+3) 1 + (r+1) * row (r+2) (r+1) := by
        change _ + (r+2-1) * row (r+2) (r+2-1) = _
        rw [show r+2-1 = r+1 by omega]
        rfl
      simp [h, penultimate]
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 2 ≤ r)
      rw [shift_two r j (by omega), ih j (by omega) r (by omega)]
      rw [show (j+2)/2=j/2+1 by omega, pow_succ,
        show r+2+1-2*(j/2+1)=r+1-2*(j/2) by omega,
        Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ]
      push_cast
      ring

/-- A signed recurrence on the original diagonal alone. Its coefficient is the
square of a binomial coefficient multiplied by the factorial of its lower index. -/
public theorem diagonal_newton_recurrence (r : ℕ) :
    (diagonal (r+2) : ℤ) = ∑ j ∈ range (r+1),
      (-1 : ℤ) ^ (j/2) * (r.choose j : ℤ)^2 * j.factorial *
        diagonal (r+1-2*(j/2)) := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) (line r) r 0
  simp only [nsmul_eq_mul, mul_one, zero_add] at h
  change (row (r+2) (r+1) : ℤ) = _ at h
  rw [penultimate] at h
  rw [h]
  apply sum_congr rfl
  intro j hj
  rw [diff_at_start r j (by simp at hj; omega), Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

end MathMiner.A402435
