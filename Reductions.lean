module

public import Geometry
public import StabilityAlgebra
public import Algebra

@[expose] public section

namespace Szarek

/-- A conditional reduction, not the universal lower bound of Theorem 1. -/
theorem stability_of_polynomial_lower_bound {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : orderedUnit a) (ht : topTwo a ≤ 1)
    (hlower : (3 : ℝ) / 4 + (1 - topTwo a ^ 2) / 24 ≤ rademacherMean a) :
    1 / Real.sqrt 2 + bestConstant * extremizerDistance a ≤ rademacherMean a := by
  rw [extremizerDistance_identity hn ha]
  exact (stability_scalar_small (topTwo a) (topTwo_pos hn ha).le ht).trans hlower

/-- Conditional on the analytic estimate (7), which is not proved here. -/
theorem second_inequality_of_scalar_bound
    (hF : ∀ s : ℝ, 4 ≤ s → (19 : ℝ) / 24 - 1 / (6 * s) ≤ haagerupF s)
    {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ} (ha : orderedUnit a) (ht : topTwo a ≤ 1) :
    (3 : ℝ) / 4 + (1 - topTwo a ^ 2) / 24 ≤ haagerupF (4 / topTwo a ^ 2) :=
  SzarekAlgebra.second_bound_of_scalar_estimate haagerupF hF _ (topTwo_pos hn ha) ht

end Szarek
