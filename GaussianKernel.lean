module

public import FourierIdentity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Szarek

def gaussianKernel (t : ℝ) : ℝ := (1 - Real.exp (-(t ^ 2) / 2)) / t ^ 2

lemma gaussianKernel_nonneg (t : ℝ) : 0 ≤ gaussianKernel t := by
  apply div_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])

lemma gaussianKernel_le_cauchy (t : ℝ) : gaussianKernel t ≤ (3 / 2) / (1 + t ^ 2) := by
  by_cases ht : t = 0
  · subst t
    norm_num [gaussianKernel]
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hsmall : gaussianKernel t ≤ 1 / 2 := by
    apply (div_le_iff₀ ht2).mpr
    have h := Real.add_one_le_exp (-(t ^ 2) / 2)
    linarith
  have hlarge : 1 - Real.exp (-(t ^ 2) / 2) ≤ 1 := by linarith [Real.exp_pos (-(t ^ 2) / 2)]
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  calc
    _ = gaussianKernel t + (1 - Real.exp (-(t ^ 2) / 2)) := by
      unfold gaussianKernel
      field_simp
    _ ≤ _ := by linarith

lemma integrable_gaussianKernel : Integrable gaussianKernel := by
  apply (integrable_inv_one_add_sq.const_mul (3 / 2 : ℝ)).mono'
  · unfold gaussianKernel
    exact (by fun_prop : Measurable (fun t : ℝ => (1 - Real.exp (-(t ^ 2) / 2)) / t ^ 2)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianKernel_nonneg t)]
    simpa only [div_eq_mul_inv] using gaussianKernel_le_cauchy t

lemma gaussian_exp_deriv (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
      (-t * Real.exp (-(t ^ 2) / 2)) t := by
  have hd : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
    convert! (((hasDerivAt_id t).pow 2).neg.div_const 2) using 1; simp; ring
  convert! hd.exp using 1; ring

lemma gaussian_quotient_continuous :
    ContinuousAt (fun t : ℝ => (1 - Real.exp (-(t ^ 2) / 2)) / t) 0 := by
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t ^ 2) / 2)) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) 1).sub (gaussian_exp_deriv 0) using 1; simp
  convert! hd.continuousAt_div using 1
  ext t
  by_cases ht : t = 0
  · subst t
    simp
  · simp [ht]

lemma gaussian_quotient_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (1 - Real.exp (-(t ^ 2) / 2)) / t)
      (Real.exp (-(t ^ 2) / 2) - gaussianKernel t) t := by
  have hd : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(u ^ 2) / 2))
      (t * Real.exp (-(t ^ 2) / 2)) t := by
    convert! (hasDerivAt_const t 1).sub (gaussian_exp_deriv t) using 1; ring
  convert! hd.div (hasDerivAt_id t) (ne_of_gt ht) using 1
  unfold gaussianKernel
  simp only [id_eq]
  field_simp [ne_of_gt ht]

lemma gaussian_quotient_atTop :
    Tendsto (fun t : ℝ => (1 - Real.exp (-(t ^ 2) / 2)) / t) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_const_nhds.div_atTop tendsto_id :
    Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply div_nonneg _ ht.le
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply div_le_div_of_nonneg_right _ ht.le
    linarith [Real.exp_pos (-(t ^ 2) / 2)]

lemma integral_gaussianKernel :
    (∫ t in Ioi (0 : ℝ), gaussianKernel t) = Real.sqrt (Real.pi / 2) := by
  have hg : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) := by
    convert! integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext t
    congr 1
    ring
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto
    gaussian_quotient_continuous.continuousWithinAt
    (fun t ht => gaussian_quotient_deriv ht)
    (hg.sub integrable_gaussianKernel).integrableOn gaussian_quotient_atTop
  rw [integral_sub hg.integrableOn integrable_gaussianKernel.integrableOn] at hf
  simp only [zero_pow (by omega : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, sub_self, div_zero] at hf
  have he : (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2) / 2)) = Real.sqrt (Real.pi / 2) := by
    have h := integral_gaussian_Ioi (1 / 2 : ℝ)
    have hs : Real.sqrt (Real.pi / (1 / 2)) / 2 = Real.sqrt (Real.pi / 2) := by
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi / (1 / 2) by positivity)
      have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
      nlinarith [Real.sqrt_nonneg (Real.pi / (1 / 2)), Real.sqrt_nonneg (Real.pi / 2)]
    rw [hs] at h
    convert! h using 1
    congr 1
    ext t
    congr 1
    ring
  linarith

end Szarek
