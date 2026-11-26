module

public import MathMiner.Problems.A402435.Statement
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

@[expose] public section

namespace MathMiner.A402435

/-- The polynomial occurring in the tangent coefficient recurrence. -/
def weightPolynomial (x : ZMod 16) : ZMod 16 := (4*x+3)*(2*x+1)^2

/-- The four surviving terms after multiplying the tangent recurrence by 105. -/
def Mod16Step (K : ℕ → ZMod 16) (j : ℕ) : Prop :=
  let x : ZMod 16 := j
  let m : ZMod 16 := (j - 1 : ℕ)
  105*(2*x+3)^2*K (j+1) =
    105*(x+1)*((2*x+1)^2+1)*K j +
    35*x^2*m*(4*m^2+7*m+4)*K (j-1) +
    7*(j.choose 2 : ZMod 16)^2*(2*weightPolynomial (j-2 : ℕ)-5)*K (j-2) +
    3*(j.choose 3 : ZMod 16)^2*(17*weightPolynomial (j-3 : ℕ)-42)*K (j-3)

def Mod16Recurrence (K : ℕ → ZMod 16) : Prop := ∀ j, Mod16Step K j

/-- Residues of the normalized even diagonal, indexed from zero. -/
def evenResidue (j : ℕ) : ZMod 16 :=
  match j % 16 with
  | 0 => 1 | 1 => 2 | 2 => 8 | 3 => 7
  | 4 => 9 | 5 => 10 | 6 => 12 | 7 => 7
  | 8 => 9 | 9 => 2 | 10 => 8 | 11 => 7
  | 12 => 9 | 13 => 10 | 14 => 12 | _ => 15

private theorem residue_shift (n : ℕ) : evenResidue (n+32) = evenResidue n := by
  unfold evenResidue
  rw [show (n+32)%16 = n%16 by omega]

private theorem cast_shift (n : ℕ) : ((n+32 : ℕ) : ZMod 16) = (n : ZMod 16) := by
  push_cast
  have h : (32 : ZMod 16) = 0 := by decide
  rw [h, add_zero]

private theorem choose_shift (n : ℕ) :
    ((n+32).choose 2 : ZMod 16) = (n.choose 2 : ZMod 16) ∧
    ((n+32).choose 3 : ZMod 16) = (n.choose 3 : ZMod 16) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n.succ+32 = (n+32).succ by omega]
    constructor
    · rw [Nat.choose_succ_succ (n+32) 1, Nat.choose_succ_succ n 1, Nat.cast_add,
        Nat.cast_add, Nat.choose_one_right, Nat.choose_one_right, cast_shift, ih.1]
    · rw [Nat.choose_succ_succ (n+32) 2, Nat.choose_succ_succ n 2, Nat.cast_add,
        Nat.cast_add, ih.1, ih.2]

private theorem step_shift {n : ℕ} (hn : 3 ≤ n) :
    Mod16Step evenResidue (n+32) ↔ Mod16Step evenResidue n := by
  unfold Mod16Step
  rw [show n+32+1 = (n+1)+32 by omega,
    show n+32-1 = (n-1)+32 by omega, show n+32-2 = (n-2)+32 by omega,
    show n+32-3 = (n-3)+32 by omega]
  simp only [cast_shift, choose_shift, residue_shift]

private theorem initial_steps : ∀ j : Fin 35, Mod16Step evenResidue j := by
  unfold Mod16Step
  decide

/-- Kernel-checked periodic certificate for all indices. -/
theorem evenResidue_recurrence : Mod16Recurrence evenResidue := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n < 35
    · exact initial_steps ⟨n, hn⟩
    · have he : n - 32 + 32 = n := by omega
      apply he ▸ (step_shift (n := n-32) (by omega)).2
      exact ih (n-32) (by omega)

private theorem coef_involution : ∀ x : ZMod 16, (105*(2*x+3)^2)^2 = 1 := by decide

/-- The recurrence and its initial value uniquely determine every residue. -/
theorem mod16Recurrence_certificate {K : ℕ → ZMod 16} (h : Mod16Recurrence K)
    (h₀ : K 0 = 1) (j : ℕ) : K j = evenResidue j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    cases j with
    | zero => exact h₀
    | succ k =>
      have hK := h k
      have hR := evenResidue_recurrence k
      unfold Mod16Step at hK hR
      dsimp only at hK hR
      rw [ih k (by omega), ih (k-1) (by omega), ih (k-2) (by omega), ih (k-3) (by omega)] at hK
      have he := congrArg (fun z : ZMod 16 => (105*(2*(k:ZMod 16)+3)^2)*z) (hK.trans hR.symm)
      simpa only [← mul_assoc, ← sq, coef_involution, one_mul] using he

end MathMiner.A402435
