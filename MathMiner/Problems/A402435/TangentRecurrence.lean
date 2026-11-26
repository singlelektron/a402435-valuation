module

public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import MathMiner.Problems.A402435.TanRecurrence
public import MathMiner.Problems.A402435.SeriesBridge

/-! Extracting the odd coefficients of the fourth-order differential identity. -/

namespace MathMiner.A402435

open PowerSeries Finset

private lemma coeff_XD (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (X * derivative f) = n * coeff n f := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

private lemma odd_mul_coeff (T G : PowerSeries ℚ) (hT : ∀ i, coeff (2*i) T = 0) (j : ℕ) :
    coeff (2*j+1) (T*G) =
      ∑ i ∈ range (j+1), coeff (2*i+1) T * coeff (2*(j-i)) G := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, show (2*j+1).succ = 2*(j+1) by omega,
    sum_range_pairs]
  apply sum_congr rfl
  intro i hi
  have := mem_range.mp hi
  simp [hT, show 2*j+1-(2*i+1)=2*(j-i) by omega]

private lemma even_mul_coeff (T G : PowerSeries ℚ) (hT : ∀ i, coeff (2*i+1) T = 0) (j : ℕ) :
    coeff (2*j+1) (T*G) =
      ∑ i ∈ range (j+1), coeff (2*i) T * coeff (2*(j-i)+1) G := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    show (2*j+1).succ = 2*(j+1) by omega, sum_range_pairs]
  apply sum_congr rfl
  intro i hi
  have := mem_range.mp hi
  simp [hT, show 2*j+1-2*i=2*(j-i)+1 by omega]

private lemma separate_zero {f : ℕ → ℚ} (j : ℕ) :
    ∑ i ∈ range (j+1), f i = f 0 + ∑ i ∈ Icc 1 j, f i := by
  have he : range (j+1) = insert 0 (Icc 1 j) := by ext i; simp; omega
  rw [he, sum_insert (by simp)]

private lemma coeff_inner (v : PowerSeries ℚ) (m : ℕ) :
    coeff (2*m) (2*(X*derivative (seriesL v)) + 3*(seriesL v)) =
      tanPolynomial m * coeff (2*m+1) v := by
  simp [coeff_XD, seriesL_coeff_eq, tanPolynomial]
  ring

private lemma coeff_local (v : PowerSeries ℚ) (j : ℕ) :
    coeff (2*j+1) (X*seriesL v + 2*(X*derivative v) + 2*v) =
      ((2*(j:ℚ)+1)^2+4*j+4)*coeff (2*j+1) v := by
  simp [coeff_succ_X_mul, coeff_derivative, seriesL_coeff_eq]
  ring

/-- Square-factorial rescaling of the odd ordinary coefficients. -/
@[expose] public noncomputable def tanNormalized (v : PowerSeries ℚ) (j : ℕ) : ℚ :=
  (j.factorial:ℚ)^2 * coeff (2*j+1) v

/-- The fourth-order identity for the odd part gives the descending-factorial recurrence. -/
public theorem tanKRecurrence_of_series (v T : PowerSeries ℚ)
    (heven : ∀ i, coeff (2*i) T = 0) (hone : coeff 1 T = 1)
    (h : seriesL (seriesL v) = 2*X*T*derivative (seriesL v) + (X+3*T)*seriesL v +
      2*X*derivative v + (2-X*T)*v) :
    TanKRecurrence (fun i ↦ coeff (2*i+1) T) (tanNormalized v) := by
  intro j
  have he : seriesL (seriesL v) =
      (X*seriesL v + 2*(X*derivative v) + 2*v) +
      T * (2*(X*derivative (seriesL v)) + 3*seriesL v) - (X*T)*v := by rw [h]; ring
  have hXT (k : ℕ) : coeff (2*k+1) (X*T) = 0 := by rw [coeff_succ_X_mul, heven]
  have hc := congrArg (coeff (2*j+1)) he
  rw [map_sub, map_add, coeff_local, odd_mul_coeff T _ heven, even_mul_coeff _ _ hXT] at hc
  simp only [seriesL_coeff_eq, coeff_inner] at hc
  rw [separate_zero, separate_zero] at hc
  simp only [Nat.mul_zero, zero_add, Nat.sub_zero, hone, one_mul, coeff_zero_X_mul,
    zero_mul] at hc
  have hm (i : ℕ) (hi : i ∈ Icc 1 j) : coeff (2*i) (X*T) = coeff (2*(i-1)+1) T := by
    have := (mem_Icc.mp hi).1
    rw [show 2*i=(2*(i-1)+1)+1 by omega, coeff_succ_X_mul]
  have hf (i : ℕ) (hi : i ∈ Icc 1 j) :
      (j.factorial : ℚ)^2 = (j.descFactorial i : ℚ)^2 * ((j-i).factorial : ℚ)^2 := by
    have eq := Nat.factorial_mul_descFactorial (mem_Icc.mp hi).2
    exact_mod_cast (show j.factorial^2 = (j.descFactorial i)^2 * (j-i).factorial^2 by
      rw [← mul_pow, mul_comm, eq])
  have hs : (j.factorial:ℚ)^2 *
      ((∑ i ∈ Icc 1 j, coeff (2*i+1) T * (tanPolynomial (j-i) * coeff (2*(j-i)+1) v)) -
       ∑ i ∈ Icc 1 j, coeff (2*i) (X*T) * coeff (2*(j-i)+1) v) =
      4 * ∑ i ∈ Icc 1 j, tanWeight (fun k ↦ coeff (2*k+1) T) j i * tanNormalized v (j-i) := by
    rw [← sum_sub_distrib, mul_sum, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [hf i hi, hm i hi]
    unfold tanWeight tanNormalized
    ring
  unfold tanNormalized
  rw [Nat.factorial_succ]
  push_cast
  simp only [tanPolynomial, tanNormalized] at hs
  simp only [tanPolynomial] at hc
  push_cast at hc
  linear_combination (j.factorial:ℚ)^2/4 * hc + hs/4

end MathMiner.A402435
