import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import LftCM.Common

open Nat

-- These are pieces of data.
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f

-- These are propositions, of type `Prop`.
#check 2 + 2 = 4

/-
Difference Between Expressions and Propositions:
- Expressions like 2 + 2 evaluate to a value of a certain type (e.g., ℕ).
- Propositions like 2 + 2 = 4 are statements that can be true or false
  and are of type Prop.
-/

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

-- This is the famous Fermat's Last Theorem for natural numbers.
#check FermatLastTheorem

-- These are proofs of propositions.
theorem easy : 2 + 3 = 5 :=
  rfl

/-
rfl : a = a is the unique constructor of the equality type.
This is the same as Eq.refl except that it takes a implicitly
instead of explicitly.
This is a more powerful theorem than it may appear at first,
because although the statement of the theorem is a = a,
lean will allow anything that is definitionally equal to that type.
So, for instance, 2 + 2 = 4 is proven in lean by rfl,
because both sides are the same up to definitional equality.
-/

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard

-- Here are some proofs.
/-
These examples all prove the same mathematical statement:
  For all natural numbers 𝑚 and 𝑛, if 𝑛 is even, then 𝑚 × 𝑛 is even.
-/

-- Proof 1: Direct Function Definition with Pattern Matching
example :
  ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, (hk : n = k + k)⟩ ↦
    have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
    show ∃ l, m * n = l + l from ⟨_, hmn⟩

/-
  `fun` (Function Definition) Defines an anonymous function.
  Used to construct proofs directly by specifying how inputs map to outputs.
-/

/-
  `Pattern Matching (⟨k, hk⟩)` Extracts components from a proof.
  In Even n, we get a witness k and an equation hk stating that n = k + k.
-/

/-
  `have` Introduces a new fact or equation.
  Helps break down complex proofs into smaller, manageable pieces.
-/

/-
  `rw (Rewrite)` Rewrites expressions using known equalities.
  Example: Rewriting n as k + k using hk.
-/

/-
  `show` Explicitly states what needs to be proven.
  Helps Lean understand the goal we're trying to reach.
-/

-- Proof 2: Concise Function Definition
example :
  ∀ m n : Nat, Even n → Even (m * n) :=
    fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩


-- Proof 3: Tactic Mode with Explanations
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n=2*k.
  -- rintro is a tactic that introduces variables and patterns.
  rintro m n ⟨k, hk⟩
  -- We need to prove m*n is twice a natural number.
  -- Let's show it's twice m*k.
  -- We claim that 𝑚 × 𝑛 = ( 𝑚 × 𝑘 ) + ( 𝑚 × 𝑘 ).
  use m * k
  -- Substitute for n,
  rw [hk]
  -- and now it's obvious.
  -- ring is a tactic that simplifies algebraic expressions involving addition and multiplication.
  ring

/-
  `rintro` Combines intro and cases.
  Introduces variables and patterns in tactic mode.
-/

/-
  `use` Provides a witness for an existential statement.
  In Even (m * n), we need to find an l such that m * n = l + l.
-/

/-
  `ring` Simplifies expressions in rings (structures with addition and multiplication).
  Automates algebraic manipulations.
-/

-- Proof 4: Concise Tactic Mode
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring


-- Proof 5: Using simp with Parity Simplifications
/-
- intros Introduces all variables and hypotheses into the context.
- simp is a powerful tactic that simplifies expressions using known rewrite rules.
- [*] tells simp to use all hypotheses and previously proved facts.
- parity_simps is a collection of lemmas about even and odd numbers.

We let Lean automatically simplify and solve the proof.
Lean uses all available information about parity to conclude that 𝑚 × 𝑛 is even.
This method requires minimal input and relies on Lean's automation.
-/

/-
  `intros` Introduces all variables and hypotheses at once.
-/

/-
  `simp` Simplifies expressions using a set of rewrite rules.
  Can use specific lemmas or all available information.
-/

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
