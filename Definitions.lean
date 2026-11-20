module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

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

def topTwo {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 2), a i

/-- Euclidean distance to (e₁ + e₂)/√2, not the sup norm on a function space. -/
def extremizerDistance {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (a i - if i.val < 2 then 1 / Real.sqrt 2 else 0) ^ 2)

/-- The exact constant from Theorem 1. The exponent is a real exponent. -/
def bestConstant : ℝ := (2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8

/-- Haagerup's function, used only at positive arguments in the paper. -/
def haagerupF (s : ℝ) : ℝ :=
  (2 / Real.sqrt (Real.pi * s)) * (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2))

def fourEqual (n : ℕ) : Fin n → ℝ := fun i => if i.val < 4 then 1 / 2 else 0

def evenEqual (n m : ℕ) : Fin n → ℝ :=
  fun i => if i.val < 2 * m then 1 / Real.sqrt (2 * (m : ℝ)) else 0

/-- An admissible dimension-independent stability coefficient. -/
def validConstant (c : ℝ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : Fin n → ℝ, orderedUnit a →
    1 / Real.sqrt 2 + c * extremizerDistance a ≤ rademacherMean a

end Szarek
