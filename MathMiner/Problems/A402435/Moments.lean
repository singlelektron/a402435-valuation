module

public import MathMiner.Problems.A402435.Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

open Finset

private theorem row_prefix (n k : ℕ) : row (n + 1) (k + 1) =
    diagonal n + (n - 1) * ∑ i ∈ range k, row n (n - (i + 1)) := by
  induction k with
  | zero => simp [diagonal, row, nextEntry]
  | succ k ih =>
    change row (n + 1) (k + 1) + (n - 1) * row n (n - (k + 1)) = _
    rw [ih, sum_range_succ]
    ring

private theorem sum_reverse (n : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ range n, f (n - (j + 1))) = ∑ j ∈ range n, f j := by
  calc
    _ = ∑ j ∈ range n, f (n - 1 - j) := by
      apply sum_congr rfl
      intro j _
      congr 1; omega
    _ = _ := sum_range_reflect f n

private theorem diagonal_row_sum (n : ℕ) : diagonal (n + 1) =
    diagonal n + (n - 1) * ∑ i ∈ range n, row n i := by
  rw [← sum_reverse n (row n)]
  exact row_prefix n n

private theorem sum_of_prefix_sums (f : ℕ → ℕ) (r : ℕ) :
    (∑ j ∈ range r, ∑ i ∈ range j, f i) =
      ∑ t ∈ range r, (r - 1 - t) * f t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, ih, sum_range_succ, ← sum_add_distrib]
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    apply sum_congr rfl
    intro t ht
    have : r - t = r - 1 - t + 1 := by simp at ht; omega
    rw [this, add_mul, one_mul]

private theorem next_row_sum (n : ℕ) :
    (∑ j ∈ range (n + 1), row (n + 1) j) =
      n * diagonal n + (n - 1) * ∑ i ∈ range n, i * row n i := by
  rw [sum_range_succ']
  change (∑ k ∈ range n, row (n + 1) (k + 1)) + 0 = _
  simp_rw [row_prefix]
  rw [sum_add_distrib, ← mul_sum, sum_of_prefix_sums]
  simp only [sum_const, card_range, nsmul_eq_mul, add_zero]
  congr 2
  convert sum_range_reflect (fun i => i * row n i) n using 2 with t
  congr 2; omega

/-- Two row steps express the new diagonal in terms of the preceding diagonal
and a weighted sum of the preceding row. This identity holds at rows zero and one as well. -/
public theorem diagonal_two_step_moment (r : ℕ) :
    diagonal (r + 2) = (1 + r * r) * diagonal r + (r - 1) * ∑ i ∈ range r, (1 + r * i) * row r i := by
  rw [diagonal_row_sum (r + 1), next_row_sum, diagonal_row_sum r, Nat.add_sub_cancel]
  simp_rw [add_mul, one_mul, mul_assoc]
  rw [sum_add_distrib, ← mul_sum]
  ring

/-- The second difference within a row is determined by the row two levels below. -/
public theorem row_second_difference {n k : ℕ} (h : k + 2 ≤ n) :
    row (n+2) (k+3) + n*(n-1)*row n (k+1) + row (n+2) (k+1)
      = 2*row (n+2) (k+2) := by
  have step (t j : ℕ) : row (t+1) (j+2) =
      row (t+1) (j+1) + (t-1)*row t (t-(j+1)) := rfl
  have leftStep := step (n+1) (k+1)
  have rightStep := step (n+1) k
  have inner := step n (n-k-2)
  rw [show n-k-2+2=n-k by omega, show n-k-2+1=n-k-1 by omega,
      show n-(n-k-1)=k+1 by omega] at inner
  rw [show n+1-1=n by omega, show n+1-(k+1+1)=n-k-1 by omega] at leftStep
  rw [show n+1-1=n by omega, show n+1-(k+1)=n-k by omega, inner] at rightStep
  rw [leftStep, rightStep]
  ring

end MathMiner.A402435
