module

public import Mathlib

@[expose] public section

open scoped BigOperators

noncomputable section
namespace Szarek

/-- The expectation for independent, uniform signs on the finite Boolean cube. -/
def rademacherMean {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  (∑ ε : Fin n → Bool, |∑ i : Fin n, a i * (if ε i then 1 else -1)|) / (2 : ℝ) ^ n

/-- Coordinates are numbered from zero in Lean. -/
def orderedUnit {n : ℕ} (a : Fin n → ℝ) : Prop :=
  Antitone a ∧ (∀ i, 0 ≤ a i) ∧ ∑ i, (a i) ^ 2 = 1

/-- Euclidean distance to (e₁ + e₂)/√2, not the sup norm on a function space. -/
def extremizerDistance {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (a i - if i.val < 2 then 1 / Real.sqrt 2 else 0) ^ 2)

/-- Haagerup's function, used only at positive arguments in the paper. -/
def haagerupF (s : ℝ) : ℝ :=
  (2 / Real.sqrt (Real.pi * s)) * (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2))

/-- Theorem 1: the greatest stability coefficient and the four-coordinate equality case.
`IsGreatest S c` means both `c ∈ S` and every member of `S` is at most `c`. -/
theorem theorem1 :
    IsGreatest {c : ℝ | ∀ (n : ℕ) (a : Fin (n + 2) → ℝ), orderedUnit a →
      1 / Real.sqrt 2 + c * extremizerDistance a ≤ rademacherMean a}
      ((2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8) ∧
    (∀ n : ℕ, 4 ≤ n →
      let a : Fin n → ℝ := fun i => if i.val < 4 then 1 / 2 else 0
      rademacherMean a = 1 / Real.sqrt 2 +
        ((2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8) * extremizerDistance a) := by
  sorry

/-- Theorem 2: both bounds and equality for every padded even-coordinate vector.
The dimension `n + 2` ranges over exactly the integers at least two. -/
theorem theorem2 :
    (∀ (n : ℕ) (a : Fin (n + 2) → ℝ), orderedUnit a → a 0 + a 1 ≤ 1 →
      haagerupF (4 / (a 0 + a 1) ^ 2) ≤ rademacherMean a ∧
      (3 : ℝ) / 4 + (1 - (a 0 + a 1) ^ 2) / 24 ≤
        haagerupF (4 / (a 0 + a 1) ^ 2)) ∧
    (∀ (n m : ℕ), 2 ≤ m → 2 * m ≤ n →
      let a : Fin n → ℝ :=
        fun i => if i.val < 2 * m then 1 / Real.sqrt (2 * (m : ℝ)) else 0
      rademacherMean a = haagerupF (2 * (m : ℝ))) := by
  sorry

end Szarek
