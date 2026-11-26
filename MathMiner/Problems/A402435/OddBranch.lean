module

public import MathMiner.Problems.A402435.RowBounds
public import Mathlib.Data.Nat.Multiplicity

namespace MathMiner.A402435

private theorem valuation_odd_mul {a b : ℕ} (ha : Odd a) (hb : 0 < b) :
    padicValNat 2 (a * b) = padicValNat 2 b := by
  have ha' : 0 < a := by obtain ⟨k, rfl⟩ := ha; omega
  have hn : ¬2 ∣ a := by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
  simp only [Nat.padicValNat_def]
  rw [multiplicity_mul Nat.prime_two.prime
      (Nat.finiteMultiplicity_iff.mpr ⟨by decide, Nat.mul_pos ha' hb⟩),
    multiplicity_eq_zero_of_not_dvd hn, zero_add]

/-- Legendre's digit formula turns the odd clause into a factorial comparison. -/
public theorem odd_branch_iff_factorial (m : ℕ) :
    (padicValNat 2 (diagonal (2*m+1)) + correction (2*m+1) = (2*m+1)+1) ↔
      padicValNat 2 (diagonal (2*m+1)) = padicValNat 2 (2*m).factorial := by
  have leg := Nat.prime_two.sub_one_mul_multiplicity_factorial (n := 2*m+1)
  rw [← Nat.padicValNat_def, Nat.factorial_succ,
    valuation_odd_mul (show Odd (2*m+1) from ⟨m, rfl⟩) (Nat.factorial_pos _)] at leg
  have hd := Nat.sum_le_ofDigits (Nat.digits 2 (2*m+1)) (by decide : 1 ≤ 2)
  rw [Nat.ofDigits_digits] at hd
  simp only [correction, show 2*m+1 ≠ 0 by omega, ite_false,
    show (2*m+1) % 2 = 1 by omega, ite_true]
  omega

/-- For positive integers the odd parts supply integral cross-multipliers
exactly when the binary valuations agree. -/
private theorem valuation_eq_iff_odd_multipliers {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    padicValNat 2 x = padicValNat 2 y ↔ ∃ a b : ℕ, Odd a ∧ Odd b ∧ a*x = b*y := by
  constructor
  · intro h
    have hodd (z : ℕ) (hz : 0 < z) : Odd (z.divMaxPow 2) :=
      Nat.not_even_iff_odd.mp fun he => Nat.not_dvd_divMaxPow (by decide) hz.ne' he.two_dvd
    refine ⟨y.divMaxPow 2, x.divMaxPow 2, hodd y hy, hodd x hx, ?_⟩
    calc
      y.divMaxPow 2 * x = y.divMaxPow 2 * (x.divMaxPow 2 * 2^padicValNat 2 x) :=
        congrArg (y.divMaxPow 2 * ·) (Nat.divMaxPow_mul_pow_padicValNat 2 x).symm
      _ = x.divMaxPow 2 * (y.divMaxPow 2 * 2^padicValNat 2 y) := by rw [h, Nat.mul_left_comm]
      _ = x.divMaxPow 2 * y := by rw [Nat.divMaxPow_mul_pow_padicValNat]
  · rintro ⟨a, b, ha, hb, he⟩
    simpa only [valuation_odd_mul ha hx, valuation_odd_mul hb hy]
      using congrArg (padicValNat 2) he

/-- Cross-multiplication expresses the entire odd clause without valuations. -/
public theorem odd_branch_iff_odd_multipliers (m : ℕ) :
    (padicValNat 2 (diagonal (2*m+1)) + correction (2*m+1) = (2*m+1)+1) ↔
      ∃ a b : ℕ, Odd a ∧ Odd b ∧ a * diagonal (2*m+1) = b * (2*m).factorial :=
  (odd_branch_iff_factorial m).trans
    (valuation_eq_iff_odd_multipliers (diagonal_pos _) (Nat.factorial_pos _))

end MathMiner.A402435
