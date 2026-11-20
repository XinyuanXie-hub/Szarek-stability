module

public import ScalarFourier
public import GaussianKernel
public import GaussianTail

@[expose] public section

open MeasureTheory Set
namespace Szarek

noncomputable def absoluteCosKernel (t : ℝ) : ℝ := (1 - |Real.cos t|) / t ^ 2
noncomputable def positiveCosKernel (t : ℝ) : ℝ := (1 - max (Real.cos t) 0) / t ^ 2
noncomputable def cosineGaussianDifference (t : ℝ) : ℝ :=
  (max (Real.cos t) 0 - Real.exp (-(t ^ 2) / 2)) / t ^ 2

lemma absoluteCosKernel_nonneg (t : ℝ) : 0 ≤ absoluteCosKernel t :=
  div_nonneg (sub_nonneg.mpr (Real.abs_cos_le_one _)) (sq_nonneg _)

lemma integrable_absoluteCosKernel : Integrable absoluteCosKernel := by
  apply (integrable_fourierKernel 1).mono'
  · exact (by unfold absoluteCosKernel; fun_prop : Measurable absoluteCosKernel).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (absoluteCosKernel_nonneg t)]
    unfold absoluteCosKernel fourierKernel
    simp only [mul_one]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith [le_abs_self (Real.cos t)]

lemma positiveCosKernel_eq (t : ℝ) :
    positiveCosKernel t = (fourierKernel 1 t + absoluteCosKernel t) / 2 := by
  unfold positiveCosKernel fourierKernel absoluteCosKernel
  simp only [mul_one]
  by_cases h : 0 ≤ Real.cos t
  · rw [max_eq_left h, abs_of_nonneg h]
    ring
  · rw [max_eq_right (le_of_not_ge h), abs_of_neg (lt_of_not_ge h)]
    ring

lemma integrable_positiveCosKernel : Integrable positiveCosKernel := by
  have he : positiveCosKernel = fun t => (fourierKernel 1 t + absoluteCosKernel t) / 2 :=
    funext positiveCosKernel_eq
  rw [he]
  exact ((integrable_fourierKernel 1).add integrable_absoluteCosKernel).div_const 2

lemma cosineGaussianDifference_eq (t : ℝ) :
    cosineGaussianDifference t = gaussianKernel t - positiveCosKernel t := by
  unfold cosineGaussianDifference gaussianKernel positiveCosKernel
  ring

lemma integrable_cosineGaussianDifference : Integrable cosineGaussianDifference := by
  have he : cosineGaussianDifference = fun t => gaussianKernel t - positiveCosKernel t :=
    funext cosineGaussianDifference_eq
  rw [he]
  exact integrable_gaussianKernel.sub integrable_positiveCosKernel

/-- The only input here is the periodic absolute-cosine kernel evaluation at s=1. -/
lemma integral_cosineGaussianDifference_of_absoluteCos
    (habs : (∫ t in Ioi (0 : ℝ), absoluteCosKernel t) = 1) :
    (∫ t in Ioi (0 : ℝ), cosineGaussianDifference t) =
      Real.sqrt (Real.pi / 2) - Real.pi / 4 - (1 : ℝ) / 2 := by
  have he : cosineGaussianDifference = fun t => gaussianKernel t -
      (fourierKernel 1 t + absoluteCosKernel t) / 2 := by
    funext t
    rw [cosineGaussianDifference_eq, positiveCosKernel_eq]
  rw [he, integral_sub]
  · rw [integral_gaussianKernel, integral_div, integral_add]
    · rw [integral_fourierKernel, habs]
      norm_num
      ring
    · exact (integrable_fourierKernel 1).integrableOn
    · exact integrable_absoluteCosKernel.integrableOn
  · exact integrable_gaussianKernel.integrableOn
  · exact (((integrable_fourierKernel 1).add integrable_absoluteCosKernel).div_const 2).integrableOn

/-- The weighted form of equation (18), conditional only on the exact periodic kernel integral. -/
theorem weighted_cosine_gaussian_negative_of_absoluteCos (L : ℝ) (hL : 0 ≤ L)
    (habs : (∫ t in Ioi (0 : ℝ), absoluteCosKernel t) = 1) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-L * t ^ 2) * cosineGaussianDifference t) < 0 := by
  have hcut := gaussian_weight_cutoff_bound cosineGaussianDifference
    (fun t => Real.exp (-(t ^ 2) / 2) / t ^ 2) (3 * Real.pi / 2) L
    (by positivity) hL integrable_cosineGaussianDifference.integrableOn
    (integrable_gaussian_tail (by positivity))
    (fun t ht htR => div_nonpos_of_nonpos_of_nonneg
      (positive_cos_sub_gaussian_nonpos ht.le htR) (sq_nonneg _))
    (fun t _ => div_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (fun t _ => by
      unfold cosineGaussianDifference
      rw [← add_div]
      simp only [sub_add_cancel]
      exact div_nonneg (le_max_right _ _) (sq_nonneg _))
  rw [integral_cosineGaussianDifference_of_absoluteCos habs] at hcut
  have hsum : Real.sqrt (Real.pi / 2) - Real.pi / 4 - (1 : ℝ) / 2 +
      (∫ t in Ioi (3 * Real.pi / 2), Real.exp (-(t ^ 2) / 2) / t ^ 2) < 0 := by
    linarith [gaussian_cosine_total_margin, integral_gaussian_tail_cutoff_lt]
  exact hcut.trans_lt (mul_neg_of_pos_of_neg (Real.exp_pos _) hsum)

#print axioms Szarek.weighted_cosine_gaussian_negative_of_absoluteCos
end Szarek
