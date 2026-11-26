module

public import MathMiner.Problems.A402435.LowWeights
public import MathMiner.Problems.A402435.OddDenominator
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

namespace MathMiner.A402435

local syntax "in_odd_ring" : tactic
local macro_rules | `(tactic| in_odd_ring) => `(tactic|
  first | assumption | exact natCast_mem oddDenom _ | exact intCast_mem oddDenom _
        | exact oddDenom.one_mem | exact oddDenom.zero_mem
        | apply oddDenom.add_mem <;> in_odd_ring
        | apply oddDenom.sub_mem <;> in_odd_ring
        | apply oddDenom.mul_mem <;> in_odd_ring
        | apply oddDenom.pow_mem <;> in_odd_ring
        | exact ofNat_mem oddDenom _)

public theorem tangent_mem_oddDenom {t : ℕ → ℚ} (ht : TangentRecurrence t) (n : ℕ) :
    t n ∈ oddDenom := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rw [ht.1]; exact oddDenom.one_mem
    | succ n =>
      have eql := ht.2 n
      have hn : Odd (2*(n+1)+1) := ⟨n+1, rfl⟩
      have hsum := oddDenom.sum_mem (t := Finset.range (n+1))
        (f := fun k => t k * t (n-k)) (by
          intro k hk
          exact oddDenom.mul_mem (ih k (Finset.mem_range.mp hk)) (ih _ (by omega)))
      have hdiv := mem_oddDenom_div hsum hn
      convert hdiv using 1
      push_cast
      field_simp
      linarith only [eql]

private theorem first_tangent_coeffs {t : ℕ → ℚ} (ht : TangentRecurrence t) :
    t 1 = 1/3 ∧ t 2 = 2/15 ∧ t 3 = 17/315 := by
  have e₁ := ht.2 0
  have e₂ := ht.2 1
  have e₃ := ht.2 2
  norm_num [Finset.sum_range_succ, ht.1] at e₁ e₂ e₃
  refine ⟨by linarith, by linarith, ?_⟩
  have h₁ : t 1 = 1/3 := by linarith
  rw [h₁] at e₃
  linarith

public theorem weight_one {t : ℕ → ℚ} (ht : TangentRecurrence t) (j : ℕ) :
    tanWeight t j 1 =
      (j:ℚ)^2*(j-1:ℕ)*(4*((j-1:ℕ):ℚ)^2+7*(j-1:ℕ)+4)/3 := by
  simp only [tanWeight, Nat.descFactorial_one, first_tangent_coeffs ht |>.1, ht.1, tanPolynomial]
  ring

public theorem weight_two {t : ℕ → ℚ} (ht : TangentRecurrence t) (j : ℕ) :
    tanWeight t j 2 = (j.choose 2:ℚ)^2*(2*tanPolynomial (j-2)-5)/15 := by
  rw [tanWeight, Nat.descFactorial_eq_factorial_mul_choose]
  norm_num [Nat.factorial, (first_tangent_coeffs ht).2.1, (first_tangent_coeffs ht).1]
  ring

public theorem weight_three {t : ℕ → ℚ} (ht : TangentRecurrence t) (j : ℕ) :
    tanWeight t j 3 = (j.choose 3:ℚ)^2*(17*tanPolynomial (j-3)-42)/35 := by
  rw [tanWeight, Nat.descFactorial_eq_factorial_mul_choose]
  norm_num [Nat.factorial, (first_tangent_coeffs ht).2.2, (first_tangent_coeffs ht).2.1]
  ring

private theorem weight_mem {t : ℕ → ℚ} (ht : TangentRecurrence t) (j i : ℕ)
    (hi : 1 ≤ i) : tanWeight t j i ∈ oddDenom := by
  by_cases one : i = 1
  · subst i
    rw [weight_one ht]
    exact mem_oddDenom_div (by in_odd_ring) (by decide : Odd 3)
  · have hfac : 2 ∣ j.descFactorial i :=
      (show 2 ∣ (2:ℕ).factorial by decide).trans
        ((Nat.factorial_dvd_factorial (by omega : 2 ≤ i)).trans (Nat.factorial_dvd_descFactorial j i))
    obtain ⟨a,ha⟩ := hfac
    have h₁ := tangent_mem_oddDenom ht i
    have h₂ := tangent_mem_oddDenom ht (i-1)
    rw [tanWeight, ha, Nat.cast_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2*(a:ℚ))^2*(tanPolynomial (j-i)*t i-t (i-1))/4 =
        (a:ℚ)^2*(tanPolynomial (j-i)*t i-t (i-1)) by ring]
    unfold tanPolynomial
    in_odd_ring

/-- Above the third coefficient the factor from the descending factorial supplies
six binary factors before division by four. -/
public theorem weight_tail_mem {t : ℕ → ℚ} (ht : TangentRecurrence t) (j i : ℕ)
    (hi : 4 ≤ i) : tanWeight t j i / 16 ∈ oddDenom := by
  have hfac : 8 ∣ j.descFactorial i :=
    (show 8 ∣ (4:ℕ).factorial by decide).trans
      ((Nat.factorial_dvd_factorial hi).trans (Nat.factorial_dvd_descFactorial j i))
  obtain ⟨a,ha⟩ := hfac
  have h₁ := tangent_mem_oddDenom ht i
  have h₂ := tangent_mem_oddDenom ht (i-1)
  rw [tanWeight, ha, Nat.cast_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (8*(a:ℚ))^2*(tanPolynomial (j-i)*t i-t (i-1))/4/16 =
      (a:ℚ)^2*(tanPolynomial (j-i)*t i-t (i-1)) by ring]
  unfold tanPolynomial
  in_odd_ring

/-- The tangent-derived recurrence propagates integrality at two. -/
public theorem K_mem_oddDenom {t K : ℕ → ℚ} (ht : TangentRecurrence t)
    (hK : TanKRecurrence t K) (h₀ : K 0 ∈ oddDenom) (n : ℕ) : K n ∈ oddDenom := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact h₀
    | succ j =>
      have hsum := oddDenom.sum_mem (t := Finset.Icc 1 j)
        (f := fun i => tanWeight t j i * K (j-i)) (by
          intro i hi
          exact oddDenom.mul_mem (weight_mem ht _ _ (Finset.mem_Icc.mp hi).1) (ih _ (by omega)))
      have hj := ih j (by omega)
      have hlead : ((j:ℚ)+1)*((2*(j:ℚ)+1)^2+1)*K j ∈ oddDenom := by in_odd_ring
      have hodd : Odd ((2*j+3)^2) := (show Odd (2*j+3) from ⟨j+1,by omega⟩).pow
      have hdiv := mem_oddDenom_div (oddDenom.add_mem hlead hsum) hodd
      convert hdiv using 1
      push_cast
      field_simp
      linarith only [hK j]

/-- After clearing odd denominators, all terms above the third lie in sixteen
times the ring of rationals with odd denominator. -/
public theorem truncated_K_recurrence {t K : ℕ → ℚ} (ht : TangentRecurrence t)
    (hK : TanKRecurrence t K) (h₀ : K 0 ∈ oddDenom) (j : ℕ) :
    ∃ e : ℚ, e ∈ oddDenom ∧
      105*(2*(j:ℚ)+3)^2*K (j+1) =
        105*((j:ℚ)+1)*((2*(j:ℚ)+1)^2+1)*K j +
        35*(j:ℚ)^2*(j-1:ℕ)*(4*((j-1:ℕ):ℚ)^2+7*(j-1:ℕ)+4)*K (j-1) +
        7*(j.choose 2:ℚ)^2*(2*tanPolynomial (j-2)-5)*K (j-2) +
        3*(j.choose 3:ℚ)^2*(17*tanPolynomial (j-3)-42)*K (j-3) + 16*e := by
  let term (i : ℕ) := tanWeight t j i * K (j-i)
  have tail_mem : (∑ i ∈ Finset.Icc 4 j, tanWeight t j i / 16 * K (j-i)) ∈ oddDenom :=
    oddDenom.sum_mem fun i hi => oddDenom.mul_mem
      (weight_tail_mem ht j i (Finset.mem_Icc.mp hi).1) (K_mem_oddDenom ht hK h₀ _)
  refine ⟨105 * ∑ i ∈ Finset.Icc 4 j, tanWeight t j i / 16 * K (j-i),
    oddDenom.mul_mem (ofNat_mem oddDenom _) tail_mem, ?_⟩
  have split := sum_Icc_split_three term j (fun i hi => by
    simp [term, tanWeight_eq_zero_of_lt t hi])
  have tailEq : (∑ i ∈ Finset.Icc 4 j, term i) =
      16 * ∑ i ∈ Finset.Icc 4 j, tanWeight t j i / 16 * K (j-i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [term]; ring
  have step := hK j
  change _ = _ + ∑ i ∈ Finset.Icc 1 j, term i at step
  rw [split, tailEq] at step
  simp only [term, weight_one ht, weight_two ht, weight_three ht] at step
  linear_combination 105*step

end MathMiner.A402435
