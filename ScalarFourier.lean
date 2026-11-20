module

public import FourierIdentity
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open scoped BigOperators
open MeasureTheory Set
noncomputable section
namespace Szarek

lemma integral_laplace_cos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-s*t) * Real.cos (t*x)) = s / (s^2+x^2) := by
  let z : ℂ := -s + x * Complex.I
  have hz : z.re < 0 := by simp [z, hs]
  have hi := integrableOn_exp_mul_complex_Ioi hz 0
  have he := integral_exp_mul_complex_Ioi hz 0
  have hfun : (fun t : ℝ => Real.exp (-s*t) * Real.cos (t*x)) =
      fun t : ℝ => (Complex.exp (z*t)).re := by
    funext t
    simp [Complex.exp_re, z, mul_comm]
  rw [hfun]
  change (∫ t in Ioi (0 : ℝ), RCLike.re (Complex.exp (z*t))) = _
  rw [integral_re hi, he]
  simp [z, Complex.div_re, Complex.normSq, pow_two]

lemma integrable_laplace_cos {s : ℝ} (hs : 0 < s) (x : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-s*t) * Real.cos (t*x)) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_complex_Ioi
    (a := -(s : ℂ) + x * Complex.I) (by simp [hs]) 0).re
  convert hi using 1
  funext t
  simp [Complex.exp_re, mul_comm]

lemma integral_linear_laplace {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), s * Real.exp (-(t*s))) = 1 / t^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ht
  norm_num [Real.Gamma_two, Real.rpow_two] at h
  simpa [div_pow] using h

lemma integrable_linear_laplace {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-(t*s))) (Ioi 0) := by
  by_contra h
  have hi := integral_linear_laplace ht
  rw [integral_undef h] at hi
  have : (1 : ℝ) / t^2 ≠ 0 := by positivity
  exact this hi.symm

def laplaceFourierKernel (x t s : ℝ) : ℝ :=
  s * Real.exp (-(t*s)) * (1 - Real.cos (t*x))

lemma laplaceFourierKernel_nonneg (x t s : ℝ) (hs : 0 ≤ s) :
    0 ≤ laplaceFourierKernel x t s := by
  unfold laplaceFourierKernel
  exact mul_nonneg (mul_nonneg hs (Real.exp_pos _).le)
    (sub_nonneg.mpr (Real.cos_le_one _))

lemma integral_laplaceFourierKernel_s {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ s in Ioi (0 : ℝ), laplaceFourierKernel x t s) = fourierKernel x t := by
  unfold laplaceFourierKernel fourierKernel
  rw [integral_mul_const, integral_linear_laplace ht]
  ring

lemma integrable_laplaceFourierKernel_s {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IntegrableOn (laplaceFourierKernel x t) (Ioi 0) :=
  (integrable_linear_laplace ht).mul_const _

lemma integral_laplaceFourierKernel_t {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), laplaceFourierKernel x t s) = x^2 / (s^2+x^2) := by
  have he := integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0
  have hc := integrable_laplace_cos hs x
  have hfun : (fun t => laplaceFourierKernel x t s) =
      fun t => s * (Real.exp (-s*t) - Real.exp (-s*t) * Real.cos (t*x)) := by
    funext t
    unfold laplaceFourierKernel
    rw [mul_comm t s, neg_mul]
    ring
  rw [hfun, integral_const_mul, integral_sub he hc,
    integral_exp_mul_Ioi (neg_neg_of_pos hs), integral_laplace_cos hs]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  have hden : s^2+x^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

lemma integrable_laplaceFourierKernel (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => laplaceFourierKernel x p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : Continuous (fun p : ℝ × ℝ => laplaceFourierKernel x p.1 p.2) := by
    unfold laplaceFourierKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact integrable_laplaceFourierKernel_s ht x
  · apply (integrable_fourierKernel x).integrableOn.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [← integral_laplaceFourierKernel_s ht x]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (laplaceFourierKernel_nonneg x t s hs.le)]

lemma integral_scaled_cauchy (x : ℝ) :
    (∫ s in Ioi (0 : ℝ), x^2 / (s^2+x^2)) = Real.pi * |x| / 2 := by
  by_cases hx : x = 0
  · subst x
    simp
  have hp : 0 < |x| := abs_pos.mpr hx
  have h := integral_comp_mul_left_Ioi'
    (fun s : ℝ => x^2 / (s^2+x^2)) 0 hp
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h]
  have hfun : (fun u : ℝ => x^2 / ((|x| * u)^2+x^2)) =
      fun u => (1+u^2)⁻¹ := by
    funext u
    rw [mul_pow, sq_abs]
    have hden : x^2*u^2+x^2 ≠ 0 := ne_of_gt (by positivity)
    have hden' : 1+u^2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  rw [hfun, integral_Ioi_inv_one_add_sq]
  simp only [Real.arctan_zero, sub_zero]
  ring

/-- The scalar Fourier integral is evaluated by a positive Laplace double
integral, followed by Fubini and the Cauchy integral. -/
theorem integral_fourierKernel (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), fourierKernel x t) = Real.pi * |x| / 2 := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), laplaceFourierKernel x t s := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact (integral_laplaceFourierKernel_s ht x).symm
    _ = ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), laplaceFourierKernel x t s :=
      integral_integral_swap (integrable_laplaceFourierKernel x)
    _ = ∫ s in Ioi (0 : ℝ), x^2 / (s^2+x^2) := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact integral_laplaceFourierKernel_t hs x
    _ = _ := integral_scaled_cauchy x

theorem abs_eq_fourier_integral (x : ℝ) :
    |x| = (2 / Real.pi) * ∫ t in Ioi (0 : ℝ), fourierKernel x t := by
  rw [integral_fourierKernel]
  field_simp

/-- Equation (11) of the paper, with no analytic premises. -/
theorem rademacher_fourier {n : ℕ} (a : Fin n → ℝ) :
    rademacherMean a = (2 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), (1 - ∏ i, Real.cos (t * a i)) / t^2 :=
  rademacher_fourier_of_scalar abs_eq_fourier_integral a

#print axioms Szarek.abs_eq_fourier_integral
#print axioms Szarek.rademacher_fourier
end Szarek
