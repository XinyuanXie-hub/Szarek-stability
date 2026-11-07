import CosineDifference

open MeasureTheory Set
namespace Szarek

noncomputable def gaussianComparisonKernel (x t : ℝ) : ℝ :=
  (1 - max (Real.cos (x * t)) 0 * Real.exp (-((1 - x ^ 2) * t ^ 2) / 2)) / t ^ 2

lemma gaussianComparisonKernel_identity {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    gaussianComparisonKernel x t = gaussianKernel t - x ^ 2 *
      (Real.exp (-((1 - x ^ 2) / (2 * x ^ 2)) * (x * t) ^ 2) *
        cosineGaussianDifference (x * t)) := by
  by_cases ht : t = 0
  · subst t
    simp [gaussianComparisonKernel, gaussianKernel, cosineGaussianDifference]
  have hexp : Real.exp (-((1 - x ^ 2) / (2 * x ^ 2)) * (x * t) ^ 2) =
      Real.exp (-((1 - x ^ 2) * t ^ 2) / 2) := by
    congr 1
    field_simp
  rw [hexp]
  have heprod : Real.exp (-((1 - x ^ 2) * t ^ 2) / 2) *
      Real.exp (-((x * t) ^ 2) / 2) = Real.exp (-(t ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gaussianComparisonKernel gaussianKernel cosineGaussianDifference
  field_simp
  ring_nf at heprod ⊢
  nlinarith only [heprod]

/-- Paper Lemma 3 reduced to the s=1 periodic absolute-cosine kernel evaluation. -/
theorem gaussian_comparison_of_absoluteCos (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (habs : (∫ t in Ioi (0 : ℝ), absoluteCosKernel t) = 1) :
    Real.sqrt (Real.pi / 2) ≤ ∫ t in Ioi (0 : ℝ), gaussianComparisonKernel x t := by
  by_cases hx0 : x = 0
  · subst x
    simpa [gaussianComparisonKernel, gaussianKernel] using integral_gaussianKernel.ge
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  let L : ℝ := (1 - x ^ 2) / (2 * x ^ 2)
  have hL : 0 ≤ L := by
    apply div_nonneg _ (by positivity)
    nlinarith
  let g : ℝ → ℝ := fun t => Real.exp (-L * t ^ 2) * cosineGaussianDifference t
  have hg : Integrable g := by
    apply integrable_cosineGaussianDifference.bdd_mul
    · exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-L * t ^ 2))).aestronglyMeasurable
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [mul_nonneg hL (sq_nonneg t)]
  have hgi : Integrable (fun t => g (x * t)) := hg.comp_mul_left' hx0
  have hform : gaussianComparisonKernel x = fun t => gaussianKernel t - x ^ 2 * g (x * t) := by
    funext t
    exact gaussianComparisonKernel_identity hx0 t
  rw [hform, integral_sub integrable_gaussianKernel.integrableOn
      (hgi.const_mul _).integrableOn, integral_const_mul, integral_gaussianKernel]
  have hneg : (∫ t in Ioi (0 : ℝ), g (x * t)) < 0 := by
    rw [integral_comp_mul_left_Ioi g 0 hxp, mul_zero, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hxp)
      (weighted_cosine_gaussian_negative_of_absoluteCos L hL habs)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hneg.le]

lemma gaussian_normalization : (2 / Real.pi) * Real.sqrt (Real.pi / 2) =
    Real.sqrt (2 / Real.pi) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- Exactly inequality (17), with its sole remaining periodic integral premise explicit. -/
theorem lemma3_of_absoluteCos (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (habs : (∫ t in Ioi (0 : ℝ), absoluteCosKernel t) = 1) :
    Real.sqrt (2 / Real.pi) ≤ (2 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), gaussianComparisonKernel x t := by
  rw [← gaussian_normalization]
  exact mul_le_mul_of_nonneg_left (gaussian_comparison_of_absoluteCos x hx hx1 habs)
    (by positivity)

lemma integrable_gaussianComparisonKernel (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Integrable (gaussianComparisonKernel x) := by
  by_cases hx0 : x = 0
  · subst x
    convert integrable_gaussianKernel using 1
    funext t
    simp [gaussianComparisonKernel, gaussianKernel]
  let L : ℝ := (1 - x ^ 2) / (2 * x ^ 2)
  have hL : 0 ≤ L := by
    apply div_nonneg _ (by positivity)
    nlinarith
  let g : ℝ → ℝ := fun t => Real.exp (-L * t ^ 2) * cosineGaussianDifference t
  have hg : Integrable g := by
    apply integrable_cosineGaussianDifference.bdd_mul
    · exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-L * t ^ 2))).aestronglyMeasurable
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [mul_nonneg hL (sq_nonneg t)]
  have hgi : Integrable (fun t => g (x * t)) := hg.comp_mul_left' hx0
  have hform : gaussianComparisonKernel x = fun t => gaussianKernel t - x ^ 2 * g (x * t) := by
    funext t
    exact gaussianComparisonKernel_identity hx0 t
  rw [hform]
  exact integrable_gaussianKernel.sub (hgi.const_mul _)

#print axioms Szarek.gaussian_comparison_of_absoluteCos
#print axioms Szarek.lemma3_of_absoluteCos
#print axioms Szarek.integrable_gaussianComparisonKernel
end Szarek
