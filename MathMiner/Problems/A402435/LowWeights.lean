module

public import MathMiner.Problems.A402435.TanRecurrence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Lemmas

namespace MathMiner.A402435

/-- The descending factorial automatically suppresses absent low indices. -/
public theorem tanWeight_eq_zero_of_lt (t : ℕ → ℚ) {j i : ℕ} (h : j < i) :
    tanWeight t j i = 0 := by
  simp [tanWeight, Nat.descFactorial_eq_zero_iff_lt.mpr h]

/-- Extract the three low weights uniformly, including the initial rows where some
of these indices lie beyond the summation interval. -/
public theorem sum_Icc_split_three {R : Type*} [AddCommMonoid R] (f : ℕ → R) (j : ℕ)
    (hz : ∀ i, j < i → f i = 0) :
    ∑ i ∈ Finset.Icc 1 j, f i =
      f 1 + f 2 + f 3 + ∑ i ∈ Finset.Icc 4 j, f i := by
  have peel (a : ℕ) : ∑ i ∈ Finset.Icc a j, f i =
      f a + ∑ i ∈ Finset.Icc (a+1) j, f i := by
    by_cases h : a ≤ j
    · have he : Finset.Icc a j = insert a (Finset.Icc (a+1) j) := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [he, Finset.sum_insert (by simp)]
    · have h₁ : j < a := by omega
      simp [Finset.Icc_eq_empty_of_lt h₁, Finset.Icc_eq_empty_of_lt (show j < a+1 by omega),
        hz a h₁]
  rw [peel 1, peel 2, peel 3]
  simp only [add_assoc]

end MathMiner.A402435
