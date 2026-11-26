module

public import MathMiner.Problems.A402435.EvenScaling
public import MathMiner.Problems.A402435.ModularCertificate
public import MathMiner.Problems.A402435.Reduction
import Mathlib.Tactic

namespace MathMiner.A402435

/-- The residue row encodes the correction at every positive even index. -/
public theorem evenResidue_valuation (j : ℕ) :
    evenResidue j ≠ 0 ∧ padicValNat 2 (evenResidue j).val + correction (2*j+2) = 3 := by
  have tab : ∀ i : Fin 16, evenResidue i ≠ 0 ∧
      padicValNat 2 (evenResidue i).val + correction (2*(i:ℕ)+2) = 3 := by decide +kernel
  have hr : evenResidue j = evenResidue (j%16) := by simp [evenResidue]
  have hc : correction (2*j+2) = correction (2*(j%16)+2) := by
    simp only [correction, show 2*j+2 ≠ 0 by omega, show 2*(j%16)+2 ≠ 0 by omega,
      show (2*j+2)%2 ≠ 1 by omega, show (2*(j%16)+2)%2 ≠ 1 by omega, ite_false,
      show (2*j+2)%16 = (2*(j%16)+2)%16 by omega]
  rw [hr, hc]
  exact tab ⟨j%16, Nat.mod_lt _ (by decide)⟩

/-- The modular valuation of the scaled even diagonal gives the locked formula. -/
public theorem even_branch_of_scaled_residue (j t : ℕ) (q : oddDenom) (ht : Odd t)
    (h : (q : ℚ) * (2^(2*j) * (t : ℚ)) = diagonal (2*j+2))
    (hr : reduce16 q = evenResidue j) :
    padicValNat 2 (diagonal (2*j+2)) + correction (2*j+2) = (2*j+2)+1 := by
  obtain ⟨hn, hc⟩ := evenResidue_valuation j
  have hv := padicValNat_of_reduce16 q (2*j) t _ ht h (hr ▸ hn)
  rw [hr] at hv
  omega

/-- The residue certificate for the normalized coefficient proves the even branch. -/
public theorem even_branch_of_residue (j : ℕ) (q : oddDenom)
    (hq : (q : ℚ) = tanNormalized (oddPart psY) j) (hr : reduce16 q = evenResidue j) :
    padicValNat 2 (diagonal (2*j+2)) + correction (2*j+2) = (2*j+2)+1 := by
  apply even_branch_of_scaled_residue j _ q (odd_oddDoubleFactorial_sq j) _ hr
  rw [hq]
  exact even_normalized_scale j

end MathMiner.A402435
