import LftCM.Common
import Mathlib.Data.Real.Basic

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

/-

1. Commutative Law of Multiplication (mul_comm): a × b = b × a

  The commutative law for multiplication states that
  for any two numbers 𝑎 and 𝑏,
  the order in which you multiply them does not matter.

2. Associative Law of Multiplication (mul_assoc): (a × b) × c = a × (b × c)

  The associative law for multiplication states that
  when multiplying three or more numbers,
  the way in which the numbers are grouped does not affect the result.

-/

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_comm a c]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  ring

/-
In Lean, when we are asked to prove an equality
without providing any arguments,
we can use tactics that don't require specifying particular lemmas or
theorems. The ring tactic is perfect for this situation.
It automatically proves equalities involving ring operations
(addition and multiplication) by normalizing both sides
and checking for equality.
-/

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_left_comm]

/-
mul_left_comm perfectly matches your goal,
allowing Lean to rewrite the left-hand side to the right-hand side directly.

-/

-- Using facts from the local context.
example
  (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example
  (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d := by
    sorry -- Can't solve


example
  (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) :
  c = 0 := by
    rw [hyp]
    rw [mul_comm]
    rw [hyp']
    simp

/-
1. Using simp:
  A powerful tactic for simplifying goals using
  a vast library of simplification lemmas.

2. Using ring:
  Ideal for equalities involving ring operations;
  it can handle more complex algebraic expressions.

3. Understanding sub_self:
  Knowing basic lemmas like sub_self can help conclude proofs
  when you have expressions like x - x = 0.
  Here: exact sub_self (a * b)

4. Finishing with rfl:
  When the goal simplifies to 0 = 0 or any x = x,
  rfl can conclude the proof.
  Here:
    rw [sub_self (a * b)] -- Now ⊢ 0 = 0
    rfl
-/

example
  (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) := by
    rw [h', ← mul_assoc, h, mul_assoc]

section

  variable (a b c d e f : ℝ)

  example
    (h : a * b = c * d) (h' : e = f) :
    a * (b * e) = c * (d * f) := by
      rw [h', ← mul_assoc, h, mul_assoc]

end

section
  variable (a b c : ℝ)

  #check a
  #check a + b
  #check (a : ℝ)
  #check mul_comm a b
  #check (mul_comm a b : a * b = b * a)
  #check mul_assoc c a b
  #check mul_comm a
  #check mul_comm

end

/-
  calc: The calc block shows each step explicitly,
  which can make the proof more readable.
  calc Mode: Allows you to chain equalities in a clear and structured way.
-/

section
  variable (a b : ℝ)

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [mul_add, add_mul, add_mul]
    rw [← add_assoc, add_assoc (a * a)]
    rw [mul_comm b a, ← two_mul]

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
        rw [mul_add, add_mul, add_mul]
      _ = a * a + (b * a + a * b) + b * b := by
        rw [← add_assoc, add_assoc (a * a)]
      _ = a * a + 2 * (a * b) + b * b := by
        rw [mul_comm b a, ← two_mul]

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
        rw [mul_add, add_mul, add_mul]
      _ = a * a + (b * a + a * b) + b * b := by
        rw [← add_assoc, add_assoc (a * a)]
      _ = a * a + 2 * (a * b) + b * b := by
        rw [mul_comm b a, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
  variable (a b c d : ℝ)

  example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
    calc
      (a + b) * (c + d) = (a + b) * c + (a + b) * d := by
        rw [mul_add]
      _ = a * c + b * c + (a * d + b * d) := by
        rw [add_mul, add_mul]
      _ = a * c + a * d + b * c + b * d := by
        rw [←add_assoc, add_assoc (a * c), add_comm (b * c), ←add_assoc]

  example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
    calc
      (a + b) * (a - b) = (a + b) * a - (a + b) * b := by
        rw [mul_sub]
      _ = a * a + a * b - a * b - b * b := by
        rw [add_mul, add_mul, ←sub_sub, mul_comm a b]
      _ = a * a - b * b := by
        rw [add_sub_cancel]
      _ = a ^ 2 - b ^ 2 := by
        rw [pow_two, pow_two]

  #check pow_two a
  #check mul_sub a b c
  #check add_mul a b c
  #check add_sub a b c
  #check sub_sub a b c
  #check add_zero a

end

-- Examples.
/-
  We're trying to prove that c = ... given the hypotheses c = ... and b = ...
  We achieve this by substituting b into the equation,
  rewriting terms using commutative and associative properties,
  and simplifying the result.
-/

section
  variable (a b c d : ℝ)

  example
    (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
    c = 2 * a * d := by
      rw [hyp'] at hyp          -- Substitute b = a * d into hyp
      rw [mul_comm d a] at hyp  -- Rewrite d * a as a * d in hyp
      rw [← two_mul (a * d)] at hyp  -- Combine like terms: a * d + a * d = 2 * (a * d)
      rw [← mul_assoc 2 a d] at hyp  -- Rearrange: 2 * (a * d) = (2 * a) * d
      exact hyp                 -- Conclude the proof

  example : c * b * a = b * (a * c) := by
    rw [mul_comm c b, mul_assoc, mul_comm c a]

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b) = (a + b) * a + (a + b) * b := by
        rw [mul_add]
      _ = a * a + b * a + (a * b + b * b) := by
        rw [add_mul, add_mul]
      _ = a * a + 2 * (a * b) + b * b := by
        rw [←add_assoc, mul_comm b a, add_assoc (a * a), ← two_mul]

  example : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
    calc
      (a + b) * (a - b) = (a + b) * a - (a + b) * b := by
        rw [mul_sub]
      _ = a * a + b * a - ( a * b + b * b) := by
        rw [add_mul, add_mul]
      _ = a * a + a * b - a * b - b * b := by
        rw [←sub_sub, mul_comm b a]
      _ = a ^ 2 - b ^ 2 := by
        rw [add_sub_cancel, pow_two, pow_two]

/-
  example
    (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
    c = 2 * a * d := by
      rw [hyp'] at hyp          -- Substitute b = a * d into hyp
      rw [mul_comm d a] at hyp  -- Rewrite d * a as a * d in hyp
      rw [← two_mul (a * d)] at hyp  -- Combine like terms: a * d + a * d = 2 * (a * d)
      rw [← mul_assoc 2 a d] at hyp  -- Rearrange: 2 * (a * d) = (2 * a) * d
      exact hyp                 -- Conclude the proof
-/

  example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d := by
    rw [hyp'] at hyp
    rw [mul_comm d a] at hyp
    rw [← two_mul] at hyp
    rw [← mul_assoc 2 a d] at hyp
    exact hyp

end

example
  (a b c : ℕ) (h : a + b = c) :
  (a + b) * (a + b) = a * c + b * c := by
    nth_rw 2 [h]
    rw [add_mul]
