module

public import MathMiner.Problems.A402435.ModularCertificate
public import MathMiner.Problems.A402435.Reduction
public import MathMiner.Problems.A402435.IntegralRecurrence
import Mathlib.Tactic

namespace MathMiner.A402435

private def clearedRhs {R : Type*} [CommRing R] (K : ℕ → R) (j : ℕ) : R :=
  let x : R := j
  let m : R := (j-1 : ℕ)
  let Q (i : ℕ) : R := (4*(i:R)+3)*(2*(i:R)+1)^2
  105*(x+1)*((2*x+1)^2+1)*K j +
  35*x^2*m*(4*m^2+7*m+4)*K (j-1) +
  7*(j.choose 2 : R)^2*(2*Q (j-2)-5)*K (j-2) +
  3*(j.choose 3 : R)^2*(17*Q (j-3)-42)*K (j-3)

private theorem map_clearedRhs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (K : ℕ → R) (j : ℕ) :
    φ (clearedRhs K j) = clearedRhs (fun i => φ (K i)) j := by
  simp [clearedRhs, map_ofNat]

/-- The residual term in the rational truncation vanishes when mapped to ZMod 16. -/
private theorem reduce_truncated_step (K : ℕ → oddDenom) (j : ℕ)
    (he : ∃ e : ℚ, e ∈ oddDenom ∧
      105*(2*(j:ℚ)+3)^2*(K (j+1) : ℚ) =
        clearedRhs (fun k => (K k : ℚ)) j + 16*e) :
    Mod16Step (fun i => reduce16 (K i)) j := by
  obtain ⟨e, he, eq⟩ := he
  have hsub : 105*(2*(j:oddDenom)+3)^2*K (j+1) =
      clearedRhs K j + 16*(⟨e, he⟩ : oddDenom) := by
    apply Subtype.ext
    erw [Subring.coe_add, Subring.coe_mul]
    have hR := map_clearedRhs oddDenom.subtype K j
    change ((clearedRhs K j : oddDenom) : ℚ) = _ at hR
    rw [hR]
    exact eq
  have h := congrArg reduce16 hsub
  have h16 : (16 : ZMod 16) = 0 := by decide
  simpa only [map_add, map_sub, map_one, map_mul, map_pow, map_ofNat, map_natCast, map_clearedRhs,
    h16, zero_mul, add_zero, Mod16Step, weightPolynomial, clearedRhs] using h

/-- The rational tangent-derived recurrence descends to the finite recurrence. -/
public theorem mod16Recurrence_of_tanK {t K : ℕ → ℚ} (ht : TangentRecurrence t)
    (hK : TanKRecurrence t K) (h₀ : K 0 ∈ oddDenom) :
    Mod16Recurrence (fun j => reduce16 ⟨K j, K_mem_oddDenom ht hK h₀ j⟩) := by
  intro j
  apply reduce_truncated_step
  exact truncated_K_recurrence ht hK h₀ j

/-- Every normalized solution beginning at one has the certified residue at each index. -/
public theorem reduce16_of_tanK {t K : ℕ → ℚ} (ht : TangentRecurrence t)
    (hK : TanKRecurrence t K) (h₀ : K 0 = 1) (j : ℕ) :
    reduce16 ⟨K j, K_mem_oddDenom ht hK (h₀ ▸ oddDenom.one_mem) j⟩ = evenResidue j := by
  apply mod16Recurrence_certificate (mod16Recurrence_of_tanK ht hK (h₀ ▸ oddDenom.one_mem)) _ j
  have hn : (⟨K 0, K_mem_oddDenom ht hK (h₀ ▸ oddDenom.one_mem) 0⟩ : oddDenom) = 1 :=
    Subtype.ext h₀
  rw [hn, map_one]

end MathMiner.A402435
