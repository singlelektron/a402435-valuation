module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.PadicValNat

@[expose] public section

namespace MathMiner.A402435

/-- Entries of row n+1 of the weighted Entringer triangle, given row n.
Only column indices up to n+1 participate in the diagonal recurrence. -/
def nextEntry (n : ℕ) (previous : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => previous n
  | j + 2 => nextEntry n previous (j + 1) + (n - 1) * previous (n - (j + 1))

def row : ℕ → ℕ → ℕ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => nextEntry n (row n)

/-- OEIS A386381, the diagonal of A386363. -/
def diagonal (n : ℕ) := row n n

/-- Luschny's A402435, including its tabulated term at zero. -/
def correction (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n % 2 = 1 then 1 + (Nat.digits 2 n).sum
  else match n % 16 with
    | 0 | 2 | 8 | 10 => 3
    | 4 | 12 => 2
    | 6 => 0
    | _ => 1

/-- The exact valuation conjecture. Addition avoids truncated subtraction. -/
def Statement : Prop :=
  ∀ n : ℕ, 1 ≤ n → padicValNat 2 (diagonal n) + correction n = n + 1

end MathMiner.A402435
