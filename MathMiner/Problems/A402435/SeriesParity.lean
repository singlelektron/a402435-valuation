module

public import MathMiner.Problems.A402435.SeriesBridge
import Mathlib.Tactic.Ring

namespace MathMiner.A402435
open PowerSeries

local notation "P" => PowerSeries ℚ

/-- Reflection in the formal variable, sending X to -X. -/
public noncomputable abbrev seriesReflect : P →+* P := rescale (-1 : ℚ)

/-- Projection retaining exactly the even coefficients. -/
@[expose] public noncomputable def evenPart (f : P) : P :=
  PowerSeries.mk fun n => if Even n then coeff n f else 0

/-- Projection retaining exactly the odd coefficients. -/
@[expose] public noncomputable def oddPart (f : P) : P :=
  PowerSeries.mk fun n => if Even n then 0 else coeff n f

public theorem evenPart_add_oddPart (f : P) : evenPart f + oddPart f = f := by
  ext n
  by_cases he : Even n <;> simp [evenPart, oddPart, he]

@[simp] public theorem coeff_evenPart_even (f : P) (i : ℕ) :
    coeff (2*i) (evenPart f) = coeff (2*i) f := by
  simp [evenPart]

@[simp] public theorem coeff_oddPart_odd (f : P) (i : ℕ) :
    coeff (2*i+1) (oddPart f) = coeff (2*i+1) f := by
  simp [oddPart]

@[simp] public theorem coeff_evenPart_odd (f : P) (i : ℕ) :
    coeff (2*i+1) (evenPart f) = 0 := by simp [evenPart]

@[simp] public theorem coeff_oddPart_even (f : P) (i : ℕ) :
    coeff (2*i) (oddPart f) = 0 := by simp [oddPart]

public theorem seriesReflect_X : seriesReflect X = -X := rescale_neg_one_X

public theorem seriesReflect_derivative (f : P) :
    seriesReflect (derivative f) = -(derivative (seriesReflect f)) := by
  ext n
  simp only [seriesReflect, coeff_rescale, map_neg, coeff_derivative, pow_succ]
  ring

public theorem seriesReflect_evenPart (f : P) : seriesReflect (evenPart f) = evenPart f := by
  ext n
  by_cases he : Even n <;> simp [seriesReflect, evenPart, neg_one_pow_eq_ite, he]

public theorem seriesReflect_oddPart (f : P) : seriesReflect (oddPart f) = -oddPart f := by
  ext n
  by_cases he : Even n <;> simp [seriesReflect, oddPart, neg_one_pow_eq_ite, he]

public theorem seriesReflect_psCos : seriesReflect psCos = psCos := by
  ext n
  by_cases he : Even n <;> simp [seriesReflect, psCos, cos, neg_one_pow_eq_ite, he]

public theorem seriesReflect_psSin : seriesReflect psSin = -psSin := by
  ext n
  by_cases he : Even n <;> simp [seriesReflect, psSin, sin, neg_one_pow_eq_ite, he]

/-- Projecting the diagonal differential equation onto the two parities. -/
public theorem psY_split_equation :
    psCos * seriesL (oddPart psY) = evenPart psY + psSin * oddPart psY ∧
    psCos * seriesL (evenPart psY) = oddPart psY + psSin * evenPart psY := by
  apply split_series_equation seriesReflect _ _ _ _ seriesReflect_X seriesReflect_derivative
    (seriesReflect_evenPart _) (seriesReflect_oddPart _) seriesReflect_psCos seriesReflect_psSin
  simpa only [evenPart_add_oddPart] using psY_cos_equation

end MathMiner.A402435
