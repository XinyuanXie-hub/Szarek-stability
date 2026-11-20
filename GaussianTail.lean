module

public import GaussianComparison
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
namespace Szarek

lemma integrable_gaussian_first_moment :
    Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) := by
  convert integrable_mul_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num) using 1
  funext x
  congr 1
  congr 1
  ring

lemma integral_gaussian_first_moment_Ioi (R : ℝ) :
    (∫ x in Ioi R, x * Real.exp (-(x ^ 2) / 2)) = Real.exp (-(R ^ 2) / 2) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => -Real.exp (-(x ^ 2) / 2))
      (x * Real.exp (-(x ^ 2) / 2)) x := by
    intro x
    convert (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp.neg) using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq, Pi.neg_apply]
      ring
  have ht : Tendsto (fun x : ℝ => -Real.exp (-(x ^ 2) / 2)) atTop (𝓝 (0 : ℝ)) := by
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop_of_neg (by norm_num : (-1 / 2 : ℝ) < 0))
    have he : (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
        (fun x : ℝ => Real.exp ((-1 / 2) * x ^ 2)) := by funext x; congr 1; ring
    have ht0 : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) atTop (𝓝 (0 : ℝ)) := by
      rw [he]
      exact h
    simpa using ht0.neg
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    integrable_gaussian_first_moment.integrableOn ht

lemma gaussian_tail_pointwise {R x : ℝ} (hR : 0 < R) (hx : R ≤ x) :
    Real.exp (-(x ^ 2) / 2) / x ^ 2 ≤
      (x * Real.exp (-(x ^ 2) / 2)) / R ^ 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le hR hx
  have hcube : R ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hR.le hx 3
  apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (pow_pos hR 3)).mpr
  have h := mul_le_mul_of_nonneg_left hcube (Real.exp_pos (-(x ^ 2) / 2)).le
  nlinarith only [h]

lemma integrable_gaussian_tail {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / x ^ 2) (Ioi R) := by
  apply (integrable_gaussian_first_moment.div_const (R ^ 3)).integrableOn.mono'
  · exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) / x ^ 2)).aestronglyMeasurable
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards [] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact gaussian_tail_pointwise hR hx.le

/-- Gaussian part of the oscillatory-tail error in Lemma 3. -/
theorem integral_gaussian_tail_le {R : ℝ} (hR : 0 < R) :
    (∫ x in Ioi R, Real.exp (-(x ^ 2) / 2) / x ^ 2) ≤
      Real.exp (-(R ^ 2) / 2) / R ^ 3 := by
  calc
    _ ≤ ∫ x in Ioi R, (x * Real.exp (-(x ^ 2) / 2)) / R ^ 3 := by
      apply integral_mono_ae (integrable_gaussian_tail hR)
        (integrable_gaussian_first_moment.div_const _).integrableOn
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      exact Filter.Eventually.of_forall (fun x hx => gaussian_tail_pointwise hR hx.le)
    _ = _ := by rw [integral_div, integral_gaussian_first_moment_Ioi]

lemma gaussian_cosine_total_margin :
    Real.sqrt (Real.pi / 2) - Real.pi / 4 - (1 : ℝ) / 2 < -(1 / 49) := by
  have hp := Real.pi_gt_three
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
  have hs0 := Real.sqrt_nonneg (Real.pi / 2)
  have hA : 0 < Real.pi / 4 + 1 / 2 - (1 : ℝ) / 49 := by linarith
  have hsq : Real.pi / 2 < (Real.pi / 4 + 1 / 2 - (1 : ℝ) / 49) ^ 2 := by
    nlinarith [sq_nonneg (Real.pi - 3)]
  nlinarith

theorem integral_gaussian_tail_cutoff_lt :
    (∫ x in Ioi (3 * Real.pi / 2), Real.exp (-(x ^ 2) / 2) / x ^ 2) < (1 : ℝ) / 49 := by
  have hR : (4 : ℝ) < 3 * Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hR0 : 0 < 3 * Real.pi / 2 := by positivity
  have hc : (49 : ℝ) < (3 * Real.pi / 2) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hR.le 3
    norm_num at h
    linarith
  have he : Real.exp (-((3 * Real.pi / 2) ^ 2) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg (3 * Real.pi / 2)]
  calc
    _ ≤ _ := integral_gaussian_tail_le hR0
    _ ≤ 1 / (3 * Real.pi / 2) ^ 3 := div_le_div_of_nonneg_right he (by positivity)
    _ < 1 / 49 := by
      apply (div_lt_div_iff₀ (by positivity : 0 < (3 * Real.pi / 2) ^ 3) (by norm_num : (0 : ℝ) < 49)).mpr
      simpa using hc

#print axioms Szarek.integral_gaussian_tail_le
#print axioms Szarek.integral_gaussian_tail_cutoff_lt
end Szarek
