module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Rat.Defs

namespace MathMiner.A402435

@[expose] public def tanPolynomial (m : ℕ) : ℚ := (4*(m:ℚ)+3)*(2*(m:ℚ)+1)^2

@[expose] public def tanWeight (t : ℕ → ℚ) (j i : ℕ) : ℚ :=
  (j.descFactorial i : ℚ)^2 * (tanPolynomial (j-i) * t i - t (i-1)) / 4

@[expose] public def TangentRecurrence (t : ℕ → ℚ) : Prop :=
  t 0 = 1 ∧ ∀ n : ℕ, (2*((n:ℚ)+1)+1)*t (n+1) =
    ∑ k ∈ Finset.range (n+1), t k * t (n-k)

@[expose] public def TanKRecurrence (t K : ℕ → ℚ) : Prop :=
  ∀ j : ℕ, (2*(j:ℚ)+3)^2 * K (j+1) =
    ((j:ℚ)+1)*((2*(j:ℚ)+1)^2+1)*K j +
      ∑ i ∈ Finset.Icc 1 j, tanWeight t j i * K (j-i)

end MathMiner.A402435
