module

public import MathMiner.Problems.A402435.OddDenominator
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.PadicValNat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

public section

namespace MathMiner.A402435

private def Represents {R : Type*} [CommRing R] (q : ℚ) (x : R) : Prop :=
  ∀ a b : ℤ, Odd b → q * (b : ℚ) = a → x * (b : R) = a

private theorem exists_representative {R : Type*} [CommRing R]
    (hu : ∀ b : ℤ, Odd b → IsUnit (b : R)) (q : oddDenom) :
    ∃ x : R, Represents q.val x := by
  obtain ⟨a, b, hb, hab⟩ := q.property
  obtain ⟨u, hu'⟩ := hu b hb
  refine ⟨(a : R) * ↑u⁻¹, ?_⟩
  intro c d _ hcd
  have hc : a * d = c * b := by
    exact_mod_cast (show (a : ℚ) * d = (c : ℚ) * b by rw [← hab, ← hcd]; ring)
  apply (hu b hb).mul_right_cancel
  calc
    (a * ↑u⁻¹ * (d : R)) * b = a * d * (↑u⁻¹ * (b : R)) := by ring
    _ = a * d := by rw [← hu', u.inv_mul, mul_one]
    _ = c * b := by simpa only [Int.cast_mul] using congrArg (Int.cast : ℤ → R) hc

private noncomputable def representative {R : Type*} [CommRing R]
    (hu : ∀ b : ℤ, Odd b → IsUnit (b : R)) (q : oddDenom) : R :=
  (exists_representative hu q).choose

private theorem representative_spec {R : Type*} [CommRing R]
    (hu : ∀ b : ℤ, Odd b → IsUnit (b : R)) (q : oddDenom) :
    Represents q.val (representative hu q) :=
  (exists_representative hu q).choose_spec

/-- Map an odd-denominator rational to a ring in which all odd integers are units. -/
noncomputable def oddDenomLift {R : Type*} [CommRing R]
    (hu : ∀ b : ℤ, Odd b → IsUnit (b : R)) : oddDenom →+* R where
  toFun := representative hu
  map_zero' := by simpa using representative_spec hu 0 0 1 (by decide) (by simp)
  map_one' := by simpa using representative_spec hu 1 1 1 (by decide) (by simp)
  map_add' x y := by
    obtain ⟨a, b, hb, hab⟩ := x.property
    obtain ⟨c, d, hd, hcd⟩ := y.property
    have hxy : ((x + y : oddDenom) : ℚ) * (↑(b * d) : ℚ) = ↑(a * d + c * b) := by
      push_cast
      change ((x : ℚ) + y) * _ = _
      rw [← hab, ← hcd]
      ring
    apply (hu (b * d) (hb.mul hd)).mul_right_cancel
    rw [representative_spec hu (x + y) _ _ (hb.mul hd) hxy]
    push_cast
    rw [← representative_spec hu x a b hb hab, ← representative_spec hu y c d hd hcd]
    ring
  map_mul' x y := by
    obtain ⟨a, b, hb, hab⟩ := x.property
    obtain ⟨c, d, hd, hcd⟩ := y.property
    have hxy : ((x * y : oddDenom) : ℚ) * (↑(b * d) : ℚ) = ↑(a * c) := by
      push_cast
      change ((x : ℚ) * y) * _ = _
      rw [← hab, ← hcd]
      ring
    apply (hu (b * d) (hb.mul hd)).mul_right_cancel
    rw [representative_spec hu (x * y) _ _ (hb.mul hd) hxy]
    push_cast
    rw [← representative_spec hu x a b hb hab, ← representative_spec hu y c d hd hcd]
    ring

theorem oddDenomLift_spec {R : Type*} [CommRing R]
    (hu : ∀ b : ℤ, Odd b → IsUnit (b : R)) (q : oddDenom)
    (a b : ℤ) (hb : Odd b) (h : (q : ℚ) * b = a) :
    oddDenomLift hu q * (b : R) = a :=
  representative_spec hu q a b hb h

theorem odd_isUnit_mod16 (b : ℤ) (hb : Odd b) : IsUnit (b : ZMod 16) := by
  obtain ⟨t, rfl⟩ := hb
  have h : ∀ s : ZMod 16, (2 * s + 1) * (2 * s + 1) ^ 3 = 1 := by decide
  push_cast
  exact isUnit_iff_exists_inv.mpr ⟨_, h t⟩

/-- Reduction of an odd-denominator rational modulo 16. -/
noncomputable def reduce16 : oddDenom →+* ZMod 16 := oddDenomLift odd_isUnit_mod16

/-- Reduction of an odd-denominator rational modulo 2. -/
noncomputable def reduce2 : oddDenom →+* ZMod 2 :=
  (ZMod.castHom (show 2 ∣ 16 by decide) (ZMod 2)).comp reduce16

theorem reduce16_spec (q : oddDenom) (a b : ℤ) (hb : Odd b)
    (h : (q : ℚ) * b = a) : reduce16 q * (b : ZMod 16) = a :=
  oddDenomLift_spec _ q a b hb h

theorem reduce2_spec (q : oddDenom) (a b : ℤ) (hb : Odd b)
    (h : (q : ℚ) * b = a) : reduce2 q * (b : ZMod 2) = a := by
  simpa [reduce2] using congrArg (ZMod.castHom (show 2 ∣ 16 by decide) (ZMod 2))
    (reduce16_spec q a b hb h)

/-- A local rational is odd modulo 2 exactly when it has odd numerator
and odd denominator. -/
theorem reduce2_eq_one_iff (q : oddDenom) :
    reduce2 q = 1 ↔ ∃ a b : ℤ, Odd a ∧ Odd b ∧ (q : ℚ) * b = a := by
  constructor
  · intro h
    obtain ⟨a, b, hb, hab⟩ := q.property
    have he := reduce2_spec q a b hb hab
    rw [h, hb.intCast_zmod_two, one_mul] at he
    exact ⟨a, b, ZMod.intCast_eq_one_iff_odd.mp he.symm, hb, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    simpa [ha.intCast_zmod_two, hb.intCast_zmod_two] using
      reduce2_spec q a b hb hab

private theorem valuation_natCast_mod16 (n : ℕ) (hn : (n : ZMod 16) ≠ 0) :
    padicValNat 2 n = padicValNat 2 (n : ZMod 16).val := by
  let r := (n : ZMod 16)
  let v := padicValNat 2 r.val
  have htest : ∀ s : ZMod 16, s ≠ 0 →
      2 ^ (padicValNat 2 s.val + 1) ∣ (16 : ℕ) ∧
      2 ^ (padicValNat 2 s.val) ∣ s.val ∧ ¬ 2 ^ (padicValNat 2 s.val + 1) ∣ s.val := by decide +kernel
  obtain ⟨hd, hlo, hhi⟩ := htest r hn
  have hm : n ≡ r.val [MOD 16] := by
    simp [r, Nat.ModEq, ZMod.val_natCast]
  rw [Nat.padicValNat_def]
  apply multiplicity_eq_of_dvd_of_not_dvd
  · exact (hm.dvd_iff ((pow_dvd_pow 2 (Nat.le_succ v)).trans hd)).mpr hlo
  · exact fun h => hhi ((hm.dvd_iff hd).mp h)

/-- Recover the exact valuation of an integer after stripping a known power of two
and an odd factor from its expression as a scaled local rational. -/
theorem padicValNat_of_reduce16 (q : oddDenom) (k t d : ℕ) (ht : Odd t)
    (h : (q : ℚ) * (2 ^ k * (t : ℚ)) = d) (hr : reduce16 q ≠ 0) :
    padicValNat 2 d = k + padicValNat 2 (reduce16 q).val := by
  obtain ⟨a, b, hb, hab⟩ := q.property
  have hi : (d : ℤ) * b = 2 ^ k * (a * (t : ℤ)) := by
    exact_mod_cast (show (d : ℚ) * b = 2 ^ k * ((a : ℚ) * t) by rw [← h, ← hab]; ring)
  have hn : d * b.natAbs = 2 ^ k * (a.natAbs * t) := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs hi
  have hd : 2 ^ k ∣ d :=
    (hb.natAbs.coprime_two_left.pow_left k).dvd_of_dvd_mul_right ⟨_, hn⟩
  obtain ⟨s, rfl⟩ := hd
  have hs : (q : ℚ) * t = s := by
    apply mul_left_cancel₀ (show (2 : ℚ) ^ k ≠ 0 by positivity)
    push_cast at h
    linear_combination h
  have he : reduce16 q * (t : ZMod 16) = (s : ZMod 16) := by
    simpa using reduce16_spec q (s : ℤ) (t : ℤ) (by exact_mod_cast ht) (by simpa using hs)
  obtain ⟨u, hu⟩ := ht
  have hfinite : ∀ r u : ZMod 16, r ≠ 0 →
      r * (2 * u + 1) ≠ 0 ∧ padicValNat 2 (r * (2 * u + 1)).val = padicValNat 2 r.val := by decide +kernel
  rw [hu] at he
  push_cast at he
  obtain ⟨hsnz, hv⟩ := hfinite (reduce16 q) u hr
  rw [he] at hsnz hv
  have hspos : s ≠ 0 := by intro hs; simp [hs] at hsnz
  calc
    padicValNat 2 (2 ^ k * s) = padicValNat 2 s + k := by
      simp only [Nat.padicValNat_def, multiplicity_base_pow_mul (by decide : 1 < 2) hspos]
    _ = _ := by rw [valuation_natCast_mod16 s hsnz, hv, Nat.add_comm]

end MathMiner.A402435
