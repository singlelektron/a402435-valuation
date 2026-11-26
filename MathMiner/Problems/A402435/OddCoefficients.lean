module

public import MathMiner.Problems.A402435.SeriesBridge
public import MathMiner.Problems.A402435.OddUnit
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

open Finset PowerSeries
local notation "P" => PowerSeries ℚ

private theorem even_degree_product (f g : P) (m : ℕ) :
    coeff (2*m) (f*g) =
      (∑ j ∈ range (m+1), coeff (2*j) f * coeff (2*(m-j)) g) +
      ∑ j ∈ range m, coeff (2*j+1) f * coeff (2*(m-j-1)+1) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    sum_range_pairs, sum_add_distrib, sum_range_succ (n := m)]
  simp only [Nat.sub_self, mul_zero]
  have evenIdx (j : ℕ) : 2*m - 2*j = 2*(m-j) := by omega
  have oddTerms :
      (∑ j ∈ range m, coeff (2*j+1) f * coeff (2*m-(2*j+1)) g) =
      ∑ j ∈ range m, coeff (2*j+1) f * coeff (2*(m-j-1)+1) g := by
    apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    rw [show 2*m-(2*j+1) = 2*(m-j-1)+1 by omega]
  simp only [evenIdx, oddTerms]
  ring

private theorem factorial_weight (n k : ℕ) (hk : k ≤ n) :
    (n.factorial : ℚ) / (n-k).factorial = (n.choose k : ℚ) * k.factorial := by
  apply (div_eq_iff _).2
  · exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk).symm
  · exact_mod_cast (n-k).factorial_ne_zero

private theorem double_factorial_weight (j : ℕ) :
    ((2*j).factorial : ℚ) = ((2*j).choose j : ℚ) * (j.factorial : ℚ)^2 := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 2*j) (k := j) (by omega)
  rw [show 2*j-j=j by omega, mul_assoc, ← sq] at h
  exact_mod_cast h.symm

/-- Reconstruct the normalized even coefficient from the odd coefficients of a
formal solution, using the coefficient expansions of cosine and sine. -/
public theorem gaugeEvenCoeff_of_series (u v c s : P)
    (h : c * seriesL v = u + s*v)
    (hc : ∀ j, coeff (2*j) c = (-1 : ℚ)^j / (2*j).factorial)
    (hc' : ∀ j, coeff (2*j+1) c = 0)
    (hs : ∀ j, coeff (2*j+1) s = (-1 : ℚ)^j / (2*j+1).factorial)
    (hs' : ∀ j, coeff (2*j) s = 0)
    (m : ℕ) :
    ((2*m).factorial : ℚ) * coeff (2*m) u =
      gaugeEvenCoeff (fun j => (j.factorial : ℚ)^2 * coeff (2*j+1) v) m := by
  have hu : u = seriesL v*c-v*s := by rw [mul_comm (seriesL v), mul_comm v, h]; ring
  rw [hu, map_sub, even_degree_product, even_degree_product, gaugeEvenCoeff]
  simp only [hc, hc', hs, hs', mul_zero, sum_const_zero, add_zero, zero_add,
    seriesL_coeff_eq, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_sub, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hw := factorial_weight (2*m) (2*j) (by omega)
    rw [show 2*m-2*j=2*(m-j) by omega, double_factorial_weight j] at hw
    calc
      _ = (((2*m).factorial : ℚ)/(2*(m-j)).factorial) * ((-1 : ℚ)^(m-j) *
          (2*(j:ℚ)+1)^2 * coeff (2*j+1) v) := by ring
      _ = _ := by rw [hw]; ring
  · apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hw := factorial_weight (2*m) (2*j+1) (by omega)
    rw [show 2*m-(2*j+1)=2*(m-j-1)+1 by omega, Nat.factorial_succ (2*j), Nat.cast_mul,
      double_factorial_weight j] at hw
    push_cast at hw
    calc
      _ = (((2*m).factorial : ℚ)/(2*(m-j-1)+1).factorial) *
        ((-1 : ℚ)^(m-j-1) * coeff (2*j+1) v) := by ring
      _ = _ := by rw [hw]; ring

/-- After reconstructing the even part, odd denominators of the normalized odd
coefficients imply the exact valuation of the original odd-indexed diagonal. -/
public theorem odd_branch_of_series_coeffs (u v : P)
    (h : psCos * seriesL v = u + psSin*v)
    (hu : ∀ j, coeff (2*j) u = yCoeff (2*j))
    (hv : ∀ j, coeff (2*j+1) v = yCoeff (2*j+1))
    (hK : ∀ j : ℕ, (j.factorial : ℚ)^2 * yCoeff (2*j+1) ∈ oddDenom) (m : ℕ) :
    padicValNat 2 (diagonal (2*m+1)) + correction (2*m+1) = (2*m+1)+1 := by
  have hr := gaugeEvenCoeff_of_series u v psCos psSin h
    (fun j => by simp [psCos, cos]) (fun j => by simp [psCos, cos])
    (fun j => by simp [psSin, sin, Nat.add_div]) (fun j => by simp [psSin, sin]) m
  simp only [hu, hv] at hr
  apply odd_branch_of_gaugeEvenCoeff (fun j => (j.factorial : ℚ)^2 * yCoeff (2*j+1)) hK
  · norm_num [yCoeff, diagonal, row, nextEntry]
  · rw [← hr, yCoeff]
    have hn : ((2*m).factorial : ℚ) ≠ 0 := by exact_mod_cast (2*m).factorial_ne_zero
    field_simp

end MathMiner.A402435
