import HaagerupLaplace

noncomputable section
namespace Szarek

lemma haagerupF_deriv_pos {s : ℝ} (hs : 0 < s) : 0 < deriv haagerupF s := by
  have hp : 0 < deriv haagerupF s / haagerupF s := by
    rw [← deriv_log_haagerupF_eq hs, deriv_log_haagerupF_laplace hs]
    exact mul_pos (by norm_num) (laplace_tanh_pos hs)
  exact (div_pos_iff_of_pos_right (haagerupF_pos hs)).mp hp

lemma haagerupF_monotone : MonotoneOn haagerupF (Set.Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0) continuousOn_haagerupF
  · intro s hs
    exact (differentiableAt_haagerupF (interior_subset hs)).differentiableWithinAt
  · intro s hs
    exact (haagerupF_deriv_pos (interior_subset hs)).le

/-- Paper equation (7), with no analytic hypotheses. -/
lemma haagerupF_scalar_lower {s : ℝ} (hs : 4 ≤ s) :
    19 / 24 - 1 / (6 * s) ≤ haagerupF s := by
  apply scalar_bound_of_log_derivative_lower ?_ s hs
  intro t ht
  have ht0 : 0 < t := by linarith
  rw [← deriv_log_haagerupF_eq ht0, deriv_log_haagerupF_laplace ht0]
  exact laplace_tanh_lower ht0

#print axioms Szarek.haagerupF_scalar_lower
#print axioms Szarek.haagerupF_monotone
end Szarek
