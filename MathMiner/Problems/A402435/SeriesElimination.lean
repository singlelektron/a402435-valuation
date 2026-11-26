module

public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathMiner.A402435
open PowerSeries

local notation "P" => PowerSeries ℚ
local notation "D" => (PowerSeries.derivative : Derivation ℚ P P)

/-- The factorial-squared generating series differential operator. -/
@[expose] public noncomputable def seriesL (f : P) : P := D (X * D f)

private theorem seriesL_add (f g : P) : seriesL (f + g) = seriesL f + seriesL g := by
  simp only [seriesL, map_add, mul_add]

private theorem seriesL_sub (f g : P) : seriesL (f - g) = seriesL f - seriesL g := by
  simp only [seriesL, map_sub, mul_sub]

private theorem seriesL_mul (f g : P) :
    seriesL (f*g) = f*seriesL g + g*seriesL f + 2*X*(D f)*(D g) := by
  simp only [seriesL, Derivation.leibniz, smul_eq_mul, map_add, PowerSeries.derivative_X]
  ring

/-- Given reflection in the formal variable and the even and odd components
of a solution, taking the two components of the equation gives a coupled system. -/
public theorem split_series_equation (τ : P →+* P) (u v c s : P)
    (hX : τ X = -X) (hD : ∀ f, τ (D f) = -(D (τ f)))
    (hu : τ u = u) (hv : τ v = -v) (hc : τ c = c) (hs : τ s = -s)
    (h : c * seriesL (u+v) = (1+s)*(u+v)) :
    c * seriesL v = u+s*v ∧ c * seriesL u = v+s*u := by
  have hl (f : P) : τ (seriesL f) = -seriesL (τ f) := by
    simp only [seriesL, hD, map_mul, hX, neg_mul_neg]
  rw [seriesL_add] at h
  have hr := congrArg τ h
  have hlneg : seriesL (-v) = -seriesL v := by simp [seriesL]
  simp only [map_add, map_mul, map_one, hl, hu, hv, hc, hs, hlneg, neg_neg] at hr
  have two : (2:P) ≠ 0 := by
    intro htwo
    have e := congrArg (constantCoeff (R := ℚ)) htwo
    rw [show (2 : P) = 1+1 by ring, map_add, map_one, map_zero] at e
    norm_num at e
  constructor
  · apply mul_left_cancel₀ two
    linear_combination h + hr
  · apply mul_left_cancel₀ two
    linear_combination h - hr

/-- Eliminate the even component of the coupled system. The resulting
differential equation only involves the odd component and the tangent series. -/
public theorem series_odd_elimination (u v c s t : P)
    (hc : D c = -s) (hs : D s = c) (hcircle : c^2+s^2=1)
    (ht : c*t=s) (hc0 : c ≠ 0)
    (h₁ : c * seriesL v = u+s*v) (h₂ : c * seriesL u = v+s*u) :
    seriesL (seriesL v) = 2*X*t*(D (seriesL v)) + (X+3*t)*seriesL v +
      2*X*D v + (2-X*t)*v := by
  have he : u = c*seriesL v-s*v := by linear_combination -h₁
  have hcL : seriesL c = -s-X*c := by
    simp only [seriesL, hc, hs, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_X, map_neg]
    ring
  have hsL : seriesL s = c-X*s := by
    simp only [seriesL, hc, hs, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_X]
    ring
  have huL : seriesL u = c*v+s*seriesL v := by
    apply mul_left_cancel₀ hc0
    linear_combination h₂ + s * he - v * hcircle
  rw [he, seriesL_sub, seriesL_mul, seriesL_mul, hcL, hsL, hc, hs] at huL
  apply mul_left_cancel₀ hc0
  linear_combination huL + (2*X*D (seriesL v) + 3*seriesL v-X*v) * (Eq.symm ht)

end MathMiner.A402435
