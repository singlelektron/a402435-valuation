module

public import MathMiner.Problems.A402435.Statement
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

namespace MathMiner.A402435

private theorem row_step_dvd {d n : ℕ} (h : ∀ k, d ∣ row n k) :
    ∀ k, d ∣ row (n + 1) k
  | 0 => dvd_zero _
  | 1 => h n
  | j + 2 => Nat.dvd_add (row_step_dvd h (j + 1)) (dvd_mul_of_dvd_right (h _) _)

private theorem next_row_constant {q d n : ℕ} (hm : q ∣ (n - 1) * d)
    (h : ∀ k, d ∣ row n k) (j : ℕ) :
    row (n + 1) (j + 1) ≡ diagonal n [MOD q] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change row (n + 1) (j + 1) + (n - 1) * row n (n - (j + 1)) ≡ _ [MOD _]
    exact (Nat.add_modEq_left_iff.mpr (hm.trans (Nat.mul_dvd_mul_left _ (h _)))).trans ih

/-- Modulo any divisor of the row weight times a common row divisor, the next
positive row entries are constant and the following diagonal has a scalar recurrence. -/
public theorem diagonal_two_step_modEq {q d n : ℕ} (hm : q ∣ (n - 1) * d)
    (h : ∀ k, d ∣ row n k) :
    diagonal (n+2) ≡ (1+n*n) * diagonal n [MOD q] := by
  have hc := next_row_constant hm h
  have line (j : ℕ) (hj : j ≤ n) :
      row (n+2) (j+1) ≡ (1 + j*n) * diagonal n [MOD q] := by
    induction j with
    | zero =>
      change row (n+1) (n+1) ≡ (1+0*n) * diagonal n [MOD q]
      simpa only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] using hc n
    | succ j ih =>
      change row (n+2) (j+1) + (n+1-1) * row (n+1) (n+1-(j+1)) ≡ _ [MOD _]
      have hi := hc (n-j-1)
      rw [show n-j-1+1 = n+1-(j+1) by omega] at hi
      rw [Nat.add_sub_cancel]
      convert (ih (by omega)).add (hi.mul_left n) using 1; ring
  have hlast : diagonal (n+2) = row (n+2) (n+1) := by
    change row (n+2) (n+1) + (n+1-1) * row (n+1) (n+1-(n+1)) = _
    simp [row, nextEntry]
  rw [hlast]
  exact line n (by rfl)

/-- From a common divisor of an odd row, two further rows suffice to gain
a factor of two at the diagonal. -/
public theorem odd_row_diagonal_gain {d m : ℕ} (h : ∀ k, d ∣ row (2*m+1) k) :
    2*d ∣ diagonal (2*m+3) := by
  let n := 2*m+1
  have hn : 2 ∣ n-1 := ⟨m, by simp [n]⟩
  rw [← Nat.modEq_zero_iff_dvd]
  refine (diagonal_two_step_modEq (Nat.mul_dvd_mul_right hn d) h).trans
    (Nat.modEq_zero_iff_dvd.mpr ?_)
  exact Nat.mul_dvd_mul (show 2 ∣ 1 + n*n from ⟨2*m*m+2*m+1, by dsimp [n]; ring⟩) (h _)

/-- Three rows after an odd row, every entry has gained at least one binary factor. -/
public theorem odd_row_common_gain {d m : ℕ} (h : ∀ k, d ∣ row (2*m+1) k) :
    ∀ k, 2*d ∣ row (2*m+4) k := by
  intro k
  cases k with
  | zero => exact dvd_zero _
  | succ j =>
    rw [← Nat.modEq_zero_iff_dvd]
    exact (next_row_constant (Nat.mul_dvd_mul_right (show 2 ∣ (2*m+3)-1 from ⟨m+1, by omega⟩) d)
      (row_step_dvd (row_step_dvd h)) j).trans (odd_row_diagonal_gain h).modEq_zero_nat

/-- At row 4r and throughout all later rows, every entry is divisible by 2^r. -/
public theorem row_pow_two_dvd (r t k : ℕ) : 2^r ∣ row (4*r+t) k := by
  induction r generalizing t k with
  | zero => simp
  | succ r ih =>
    have hrow : ∀ k, 2^r ∣ row (2*(2*r)+1) k := by
      intro j
      simpa only [show 2*(2*r)=4*r by omega] using ih 1 j
    have gain := odd_row_common_gain hrow
    have hbase : ∀ j, 2^(r+1) ∣ row (4*(r+1)) j := by
      intro j
      simpa only [pow_succ', show 2*(2*r)+4=4*(r+1) by omega] using gain j
    induction t generalizing k with
    | zero => exact hbase k
    | succ t iht => exact row_step_dvd iht k

/-- Each positive column starts at the preceding diagonal and adds natural numbers. -/
private theorem diagonal_le_next (n j : ℕ) : diagonal n ≤ row (n+1) (j+1) := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    exact le_trans ih (Nat.le_add_right _ _)

public theorem diagonal_pos (n : ℕ) : 0 < diagonal n := by
  induction n with
  | zero => decide
  | succ n ih => exact lt_of_lt_of_le ih (diagonal_le_next n n)

/-- A linear lower bound for the valuation on the original unbounded diagonal. -/
public theorem diagonal_valuation_lower_bound (n : ℕ) : n / 4 ≤ padicValNat 2 (diagonal n) := by
  rw [Nat.padicValNat_def]
  apply (Nat.pow_dvd_iff_le_multiplicity (by decide : 2 ≠ 1) (diagonal_pos n).ne').mp
  simpa only [Nat.div_add_mod, diagonal] using row_pow_two_dvd (n/4) (n%4) n

end MathMiner.A402435
