import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SzarekAlgebra

/-- Substitution in the scalar estimate (7). This is conditional on that estimate;
it does not establish the analytic bound for Haagerup's function. -/
theorem second_bound_of_scalar_estimate (F : ℝ → ℝ)
    (hF : ∀ s : ℝ, 4 ≤ s → (19 : ℝ) / 24 - 1 / (6 * s) ≤ F s)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (3 : ℝ) / 4 + (1 - t ^ 2) / 24 ≤ F (4 / t ^ 2) := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have ht2_le : t ^ 2 ≤ 1 := by nlinarith
  have hs : 4 ≤ 4 / t ^ 2 := (le_div_iff₀ ht2).2 (by nlinarith)
  have heq : (19 : ℝ) / 24 - 1 / (6 * (4 / t ^ 2)) =
      3 / 4 + (1 - t ^ 2) / 24 := by
    field_simp [ne_of_gt ht]
    ring
  rw [← heq]
  exact hF _ hs

end SzarekAlgebra
