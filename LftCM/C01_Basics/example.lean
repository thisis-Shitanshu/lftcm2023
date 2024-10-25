import Mathlib
open Real

-- Example 1
example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw [add_mul b 1 a, one_mul a, add_comm a (a * b), mul_comm a b]

-- Example 2
example (x y : ℕ) : x * y + x = x * (y + 1) := by
  conv_rhs => rw [mul_add, mul_comm x 1, one_mul]
