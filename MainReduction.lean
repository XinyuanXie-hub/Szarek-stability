import TheoremTwoReduction
import WeightedSigns
import KhintchineReduction
import HaagerupEndpoint
import HaagerupScalar
import EvenEquality
import PaddedSharpness

open MeasureTheory Set
open scoped BigOperators
namespace Szarek

/-- Final assembly of both main claims; the two remaining analytic dependencies
are exposed as hypotheses, never as axioms or as changes to the frozen targets. -/
theorem main_bounds_of_analytic_inputs
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t : ℝ in Ioi 0, poweredCosKernel s t) = haagerupF s)
    (hsmall : ∀ (n : ℕ) (a : Fin (n + 2) → ℝ), orderedUnit a →
      0 < a 1 → a 0 ^ 2 + 3 * a 1 ^ 2 ≤ 1 →
      Real.sqrt (2 / Real.pi) *
        (1 - (7 : ℝ) / 20 * (a 1 ^ 2 / Real.sqrt (1 - a 0 ^ 2))) ≤ rademacherMean a) :
    validConstant bestConstant ∧
    (∀ (n : ℕ), 2 ≤ n → ∀ a : Fin n → ℝ, orderedUnit a → topTwo a ≤ 1 →
      haagerupF (4 / topTwo a ^ 2) ≤ rademacherMean a ∧
      (3 : ℝ) / 4 + (1 - topTwo a ^ 2) / 24 ≤ haagerupF (4 / topTwo a ^ 2)) := by
  have hmean (n : ℕ) (a : Fin n → ℝ) (ha : orderedUnit a) :=
    haagerup_fourth_moment_of_integral heval a ha.2.1 ha.2.2
  have hchord (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      haagerupF (4 / t ^ 2) ≤ (1 - t ^ 2) * Real.sqrt (2 / Real.pi) + (3 : ℝ) / 4 * t ^ 2 := by
    exact haagerupF_chord (sq_pos_of_pos ht) (by nlinarith)
  have hbounds := theorem2_bounds_of_analytic_estimates hmean haagerupF_monotone
    hchord hsmall (fun _ hs => haagerupF_scalar_lower hs)
  refine ⟨?_, hbounds⟩
  intro n hn a ha
  by_cases ht : topTwo a ≤ 1
  · have hb := hbounds n hn a ha ht
    exact stability_of_polynomial_lower_bound hn ha ht (hb.2.trans hb.1)
  · exact stability_large_of_khintchine
      (khintchine_of_haagerup (weighted_haagerup_all_signs_of_integral heval) haagerupF_monotone)
      hn ha (le_of_not_ge ht)

end Szarek
