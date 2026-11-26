module

public import MathMiner.Problems.A402435.Newton
public import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

open Finset

/-- Ordinary generating-series coefficients of the shifted, factorial-normalized diagonal. -/
@[expose] public def yCoeff (n : ℕ) : ℚ := (diagonal (n+1) : ℚ) / (n.factorial : ℚ)^2

private theorem next_normalized (n : ℕ) :
    ((n : ℚ)+1)^2 * yCoeff (n+1) =
      (diagonal (n+2) : ℚ) / (n.factorial : ℚ)^2 := by
  simp only [yCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem weighted_term (r j : ℕ) (h : j ≤ r) (a : ℚ) :
    ((r.choose j : ℚ)^2 * j.factorial * a) / (r.factorial : ℚ)^2 =
      a / ((j.factorial : ℚ) * ((r-j).factorial : ℚ)^2) := by
  have hf : (r.choose j : ℚ) * j.factorial * (r-j).factorial = r.factorial :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have hd : (r.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have ht : ((r-j).factorial : ℚ) ≠ 0 := by exact_mod_cast (r-j).factorial_ne_zero
  rw [← hf]
  field_simp

/-- Normalized Newton recurrence, indexed by the order of the forward difference. -/
public theorem normalized_newton (r : ℕ) :
    ((r : ℚ)+1)^2 * yCoeff (r+1) = ∑ j ∈ range (r+1),
      ((-1 : ℚ)^(j/2) / j.factorial) *
        (if j%2 = 0 then yCoeff (r-j)
          else ((r-j : ℕ) + 1 : ℚ)^2 * yCoeff (r-j+1)) := by
  have h := congrArg (Int.cast : ℤ → ℚ) (diagonal_newton_recurrence r)
  push_cast at h
  rw [next_normalized, h, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by simpa using hj
  rw [← div_eq_mul_inv]
  rw [mul_assoc ((-1 : ℚ) ^ (j/2)), mul_assoc ((-1 : ℚ) ^ (j/2)), mul_div_assoc,
    weighted_term r j hjr]
  split
  · rename_i even
    rw [yCoeff, show r+1-2*(j/2)=r-j+1 by omega]
    ring
  · rename_i odd
    rw [next_normalized, show r+1-2*(j/2)=r-j+2 by omega]
    ring

private theorem split_range (f : ℕ → ℚ) (n : ℕ) :
    ∑ j ∈ range n, f j = (∑ k ∈ range ((n+1)/2), f (2*k)) +
      ∑ k ∈ range (n/2), f (2*k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases he : n%2 = 0
    · rw [show (n+1+1)/2=(n+1)/2+1 by omega, sum_range_succ,
        show (n+1)/2 = n/2 by omega, show 2*(n/2) = n by omega]
      ring
    · rw [show (n+1+1)/2=(n+1)/2 by omega,
        show n.succ/2 = n/2+1 by omega]
      rw [sum_range_succ (f := fun k => f (2*k+1)), show 2*(n/2)+1=n by omega]
      ring

/-- The even and odd forward differences give two separate coefficient sums. -/
public theorem normalized_newton_even_odd (r : ℕ) :
    ((r : ℚ)+1)^2 * yCoeff (r+1) =
      (∑ k ∈ range (r/2+1), ((-1 : ℚ)^k / (2*k).factorial) * yCoeff (r-2*k)) +
      ∑ k ∈ range ((r+1)/2), ((-1 : ℚ)^k / (2*k+1).factorial) *
        (r-2*k : ℕ)^2 * yCoeff (r-2*k) := by
  rw [normalized_newton, split_range, show (r+1+1)/2=r/2+1 by omega]
  congr 1
  · apply sum_congr rfl
    intro k _
    simp
  · apply sum_congr rfl
    intro k hk
    have h1 : (2*k+1)/2 = k := by omega
    have h2 : (2*k+1)%2 = 1 := by omega
    have h3 : r-(2*k+1)+1 = r-2*k := by simp at hk; omega
    simp only [h1, h2, Nat.one_ne_zero, ite_false, h3]
    rw [← Nat.cast_add_one, h3]
    ring

end MathMiner.A402435
