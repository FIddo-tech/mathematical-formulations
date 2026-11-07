import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# Sum of the First n Natural Numbers
Formula: ∑_{i=0}^{n} i = n * (n + 1) / 2

Implemented via the non-divisive form: 2 * (∑_{i=0}^{n} i) = n * (n + 1)
to avoid natural number truncation during integer division.
-/

/-- Recursive definition of arithmetic sum from 0 to n -/
def sumFirstN : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumFirstN n

theorem sumFirstN_two_mul (n : ℕ) : 2 * sumFirstN n = n * (n + 1) := by
  induction' n with n ih
  · -- Base case: n = 0
    -- Compute sumFirstN 0 = 0 directly
    rfl
  · -- Inductive step: n + 1
    -- Definition unfolds sumFirstN (n + 1) to (n + 1) + sumFirstN n
    dsimp [sumFirstN]
    
    -- Rookie note / scratchpad trial:
    -- In early attempts, typing `rw [ih]` directly fails because the multiplication
    -- is not yet factored: `2 * ((n + 1) + sumFirstN n)` has nested addition.
    -- First distribute the multiplication:
    rw [Nat.mul_add]
    
    -- Substitute the induction hypothesis into `2 * sumFirstN n`
    rw [ih]
    
    -- Finish the algebraic goal: 2 * (n + 1) + n * (n + 1) = (n + 1) * (n + 1 + 1)
    ring