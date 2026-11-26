module

public import MathMiner.Problems.A402435.OddDenominator
public import MathMiner.Problems.A402435.OddBranch
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.LinearCombination

namespace MathMiner.A402435

/-- The even exponential Taylor coefficient of the cosine/sine reconstruction,
written in terms of the normalized odd coefficients `K`. -/
@[expose] public def gaugeEvenCoeff {R : Type*} [CommRing R] (K : ℕ → R) (m : ℕ) : R :=
  (∑ j ∈ Finset.range (m + 1),
    (-1 : R)^(m-j) * ((2*m).choose (2*j) : R) * ((2*j).choose j : R) *
      (2*(j : R)+1)^2 * K j) -
  ∑ j ∈ Finset.range m,
    (-1 : R)^(m-j-1) * ((2*m).choose (2*j+1) : R) * (2*(j : R)+1) *
      ((2*j).choose j : R) * K j

/-- In the reconstruction, all terms except the constant cosine term are even.
This applies in particular over the ring of rationals with odd denominator. -/
public theorem odd_gaugeEvenCoeff {R : Type*} [CommRing R] (K : ℕ → R) (hK : K 0 = 1)
    (m : ℕ) : Odd (gaugeEvenCoeff K m) := by
  have central (j : ℕ) : Even (((2*(j+1)).choose (j+1) : ℕ) : R) :=
    (even_iff_two_dvd.mpr (Nat.two_dvd_centralBinom_succ j)).natCast
  unfold gaugeEvenCoeff
  rw [Finset.sum_range_succ']
  apply Odd.sub_even
  · apply Even.add_odd
    · apply even_iff_two_dvd.mpr
      apply Finset.dvd_sum
      intro j _
      exact ((((central j).mul_left _).mul_right _).mul_right _).two_dvd
    · simp [hK, (odd_one.neg : Odd (-1 : R)).pow]
  · apply even_iff_two_dvd.mpr
    apply Finset.dvd_sum
    intro j _
    cases j with
    | zero =>
      simp only [mul_zero, zero_add, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one,
        Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat, mul_one, hK]
      exact (((even_two.mul_right (m : R)).mul_left _)).two_dvd
    | succ j => exact (((central j).mul_left _).mul_right _).two_dvd

/-- An odd element of the odd-denominator subring equates natural numbers only via
odd cross-multipliers, even if the chosen integer representatives are negative. -/
private theorem odd_multipliers_of_ratio {x y : ℕ} {q : oddDenom}
    (hq : Odd q) (hxy : (x : ℚ) = (q : ℚ) * (y : ℚ)) :
    ∃ a b : ℕ, Odd a ∧ Odd b ∧ a*x = b*y := by
  obtain ⟨t, ht⟩ := hq
  obtain ⟨a, b, hb, hab⟩ := t.property
  have ht' : (q : ℚ) = 2 * (t : ℚ) + 1 := congrArg Subtype.val ht
  have heq : b * (x : ℤ) = (2*a+b) * (y : ℤ) := by
    have heq' : (b : ℚ) * x = (2*(a : ℚ)+b) * y := by
      linear_combination (b : ℚ)*hxy + (b : ℚ)*(y : ℚ)*ht' + 2*(y : ℚ)*hab
    exact_mod_cast heq'
  exact ⟨b.natAbs, (2*a+b).natAbs, hb.natAbs,
    ((even_two.mul_right a).add_odd hb).natAbs,
    by simpa [Int.natAbs_mul] using congrArg Int.natAbs heq⟩

/-- The rational coefficient identity and odd denominators for the auxiliary sequence
suffice to recover the locked odd-index clause. -/
public theorem odd_branch_of_gaugeEvenCoeff (K : ℕ → ℚ) (hK : ∀ j, K j ∈ oddDenom)
    (hzero : K 0 = 1) (m : ℕ)
    (hdiag : (diagonal (2*m+1) : ℚ) = gaugeEvenCoeff K m * (2*m).factorial) :
    padicValNat 2 (diagonal (2*m+1)) + correction (2*m+1) = (2*m+1)+1 := by
  let liftK (j : ℕ) : oddDenom := ⟨K j, hK j⟩
  apply (odd_branch_iff_odd_multipliers m).mpr
  apply odd_multipliers_of_ratio (odd_gaugeEvenCoeff liftK (Subtype.ext hzero) m)
  have two_coe : ((2 : oddDenom) : ℚ) = 2 := rfl
  simpa [gaugeEvenCoeff, liftK, two_coe] using hdiag

end MathMiner.A402435
