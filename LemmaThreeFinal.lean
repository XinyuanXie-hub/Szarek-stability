import LemmaThree
import WeightedHaagerup
import HaagerupEvaluation

open MeasureTheory Set
namespace Szarek

lemma haagerupF_one : haagerupF 1 = 2 / Real.pi := by
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsq := Real.sq_sqrt Real.pi_pos.le
  unfold haagerupF
  norm_num [Real.Gamma_one_half_eq]
  field_simp
  nlinarith only [hsq]

lemma integral_absoluteCosKernel_of_poweredCos_integral
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t in Ioi (0 : ℝ), poweredCosKernel s t) = haagerupF s) :
    (∫ t in Ioi (0 : ℝ), absoluteCosKernel t) = 1 := by
  have h := heval 1 (by norm_num)
  have he : poweredCosKernel 1 = absoluteCosKernel := by
    funext t
    simp [poweredCosKernel, absoluteCosKernel]
  rw [he, haagerupF_one] at h
  norm_num only [Real.sqrt_one, mul_one] at h
  apply mul_left_cancel₀ (show (2 : ℝ) / Real.pi ≠ 0 by positivity)
  simpa only [mul_one] using h

/-- Lemma 3, with only the shared Fourier/Gamma kernel evaluation as a premise. -/
theorem lemma3_of_poweredCos_integral
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t in Ioi (0 : ℝ), poweredCosKernel s t) = haagerupF s)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (2 / Real.pi) ≤ (2 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), gaussianComparisonKernel x t :=
  lemma3_of_absoluteCos x hx hx1 (integral_absoluteCosKernel_of_poweredCos_integral heval)

lemma integral_absoluteCosKernel :
    (∫ t in Ioi (0 : ℝ), absoluteCosKernel t) = 1 :=
  integral_absoluteCosKernel_of_poweredCos_integral (fun _ hs => haagerup_integral_eval hs)

/-- Paper Lemma 3, with all analytic inputs proved. -/
theorem lemma3 (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (2 / Real.pi) ≤ (2 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), gaussianComparisonKernel x t :=
  lemma3_of_absoluteCos x hx hx1 integral_absoluteCosKernel

/-- Equation (18), including the endpoint L=0. -/
theorem weighted_cosine_gaussian_negative (L : ℝ) (hL : 0 ≤ L) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-L * t ^ 2) * cosineGaussianDifference t) < 0 :=
  weighted_cosine_gaussian_negative_of_absoluteCos L hL integral_absoluteCosKernel

#print axioms Szarek.lemma3
#print axioms Szarek.weighted_cosine_gaussian_negative
#print axioms Szarek.haagerupF_one
#print axioms Szarek.lemma3_of_poweredCos_integral
end Szarek
