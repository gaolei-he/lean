import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
open Nat
open Finset
open BigOperators
theorem interact_temp {n : ℕ} : (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = if n = 0 then 1 else 0  := by 
  lean_repl sorry
