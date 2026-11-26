module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace MathMiner.A402435

/-- Rationals that can be written with an odd integer denominator. -/
@[expose] public def oddDenom : Subring ℚ where
  carrier := {q | ∃ a b : ℤ, Odd b ∧ q * (b : ℚ) = (a : ℚ)}
  zero_mem' := ⟨0, 1, odd_one, by norm_num⟩
  one_mem' := ⟨1, 1, odd_one, by norm_num⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*d+c*b,b*d,hb.mul hd,?_⟩
    push_cast
    linear_combination d*hx+b*hy
  mul_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*c,b*d,hb.mul hd,?_⟩
    push_cast
    rw [show x*y*((b:ℚ)*d) = (x*b)*(y*d) by ring, hx, hy]
  neg_mem' := by
    rintro x ⟨a,b,hb,hx⟩
    exact ⟨-a,b,hb,by push_cast; rw [neg_mul,hx]⟩

/-- Division by an odd natural number preserves this subring. -/
public theorem mem_oddDenom_div {x : ℚ} (hx : x ∈ oddDenom) {d : ℕ} (hd : Odd d) :
    x / (d : ℚ) ∈ oddDenom := by
  rw [div_eq_mul_inv]
  apply oddDenom.mul_mem hx
  have dne : (d : ℚ) ≠ 0 := by
    have : d ≠ 0 := by obtain ⟨k,h⟩ := hd; omega
    exact_mod_cast this
  exact ⟨1,(d:ℤ),by exact_mod_cast hd,by push_cast; rw [inv_mul_cancel₀ dne]⟩

end MathMiner.A402435
