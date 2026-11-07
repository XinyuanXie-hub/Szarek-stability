import HaagerupLogDerivative
import HaagerupAnalysis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace Szarek

noncomputable def expDifference (s : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(s + 2 * k) * t) - Real.exp (-(s + 2 * k + 1) * t)

lemma expDifference_nonneg (s : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ expDifference s k t := by
  unfold expDifference
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith

lemma expDifference_integrable {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn (expDifference s k) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity) : -(s + 2 * (k : ℝ)) < 0) 0).sub
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity) : -(s + 2 * (k : ℝ) + 1) < 0) 0)

lemma integral_expDifference {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, expDifference s k t) =
      1 / (s + 2 * k) - 1 / (s + 2 * k + 1) := by
  unfold expDifference
  rw [integral_sub
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity) : -(s + 2 * (k : ℝ)) < 0) 0)
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity) : -(s + 2 * (k : ℝ) + 1) < 0) 0),
    integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0,
    integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity)) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]

lemma expDifference_geometric (s t : ℝ) (k : ℕ) :
    expDifference s k t =
      Real.exp (-s * t) * (1 - Real.exp (-t)) * (Real.exp (-2 * t)) ^ k := by
  rw [← Real.exp_nat_mul]
  unfold expDifference
  rw [show -(s + 2 * (k : ℝ)) * t = -s * t + (k : ℝ) * (-2 * t) by ring,
    show -(s + 2 * (k : ℝ) + 1) * t = (-s * t + (k : ℝ) * (-2 * t)) + -t by ring,
    Real.exp_add, Real.exp_add, Real.exp_add]
  ring

lemma tsum_expDifference (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∑' k : ℕ, expDifference s k t = Real.exp (-s * t) / (1 + Real.exp (-t)) := by
  have hnorm : ‖Real.exp (-2 * t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have heq : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [show -2 * t = -t + -t by ring, Real.exp_add]
    ring
  have hne : 1 - Real.exp (-t) ≠ 0 := ne_of_gt (by
    have h : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith)
  have hden : 1 + Real.exp (-t) ≠ 0 := by positivity
  have hpowne : 1 - Real.exp (-t) ^ 2 ≠ 0 := by
    rw [← heq]
    apply ne_of_gt
    have hh := le_abs_self (Real.exp (-2 * t))
    rw [Real.norm_eq_abs] at hnorm
    linarith
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left
    (Real.exp (-s * t) * (1 - Real.exp (-t)))
  simp_rw [← expDifference_geometric] at h
  rw [h.tsum_eq, heq]
  field_simp [hpowne]
  ring

lemma haagerup_series_eq_integral {s : ℝ} (hs : 0 < s) :
    (∑' k : ℕ, (1 / (s + 2 * k) - 1 / (s + 2 * k + 1))) =
      ∫ t : ℝ in Ioi 0, Real.exp (-s * t) / (1 + Real.exp (-t)) := by
  have hnorm (k : ℕ) : (∫ t : ℝ in Ioi 0, ‖expDifference s k t‖) =
      1 / (s + 2 * k) - 1 / (s + 2 * k + 1) := by
    rw [← integral_expDifference hs k]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact Real.norm_of_nonneg (expDifference_nonneg s k (le_of_lt ht))
  have hsum : Summable (fun k : ℕ => ∫ t : ℝ in Ioi 0, ‖expDifference s k t‖) := by
    simp_rw [hnorm]
    exact (hasSum_haagerup_reciprocal hs).summable
  have hi := integral_tsum_of_summable_integral_norm (expDifference_integrable hs) hsum
  simp_rw [integral_expDifference hs] at hi
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact tsum_expDifference s ht

lemma tanh_half_exp (t : ℝ) :
    Real.tanh (t / 2) = (1 - Real.exp (-t)) / (1 + Real.exp (-t)) := by
  have hpos : 0 < Real.exp (t / 2) := Real.exp_pos _
  have hneg : Real.exp (-t) = (Real.exp (t / 2))⁻¹ ^ 2 := by
    rw [show -t = -(t / 2) + -(t / 2) by ring, Real.exp_add, Real.exp_neg]
    ring
  rw [Real.tanh_eq, Real.exp_neg, hneg]
  field_simp

/-- The Laplace-transform version of equation (15). -/
theorem deriv_log_haagerupF_laplace {s : ℝ} (hs : 0 < s) :
    deriv (fun s => Real.log (haagerupF s)) s =
      (1 / 2 : ℝ) * ∫ t : ℝ in Ioi 0, Real.exp (-s * t) * Real.tanh (t / 2) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have htanh := integrableOn_exp_tanh hs
  have heq (t : ℝ) : Real.exp (-s * t) / (1 + Real.exp (-t)) =
      (Real.exp (-s * t) + Real.exp (-s * t) * Real.tanh (t / 2)) / 2 := by
    rw [tanh_half_exp]
    field_simp
    ring
  rw [deriv_log_haagerupF_series hs, haagerup_series_eq_integral hs]
  simp_rw [heq]
  rw [integral_div, integral_add hexp htanh, integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

end Szarek
