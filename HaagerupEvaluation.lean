module

public import HaagerupIntegral
public import EvenPeriodization
public import PoweredCosIntegrability
public import LocalCosineIntegral
public import CosineBeta

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace Szarek

lemma abs_cos_int_period (n : ℤ) (t : ℝ) :
    |Real.cos ((n : ℝ)*Real.pi+t)| = |Real.cos t| := by
  rw [add_comm, Real.cos_add_int_mul_pi, abs_mul]
  simp

lemma poweredCosKernel_even (s : ℝ) : Function.Even (poweredCosKernel s) := by
  intro t
  simp [poweredCosKernel]

lemma poweredCosKernel_periodization (s : ℝ) {t : ℝ}
    (ht : t ∈ Ioo 0 (Real.pi/2)) :
    (∑' n : ℤ, poweredCosKernel s ((n : ℝ)*Real.pi+t)) =
      (1 - Real.cos t ^ s) / Real.sin t^2 := by
  have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
  simp_rw [poweredCosKernel, abs_cos_int_period, abs_of_nonneg hc]
  calc
    _ = (1 - Real.cos t ^ s) * (∑' n : ℤ, 1/(t+(n : ℝ)*Real.pi)^2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [add_comm ((n : ℝ)*Real.pi) t]
      ring
    _ = _ := by rw [scaled_reciprocal_square_int_sum ht]; ring

/-- The periodic folding identity in equation (12), before integration by parts. -/
theorem poweredCosKernel_folding {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), poweredCosKernel s t) =
      ∫ t in Ioo (0 : ℝ) (Real.pi/2), (1 - Real.cos t ^ s) / Real.sin t^2 := by
  rw [integral_periodization_even_int Real.pi_pos (integrable_poweredCosKernel hs)
    (poweredCosKernel_even s)]
  rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ Real.pi/2),
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact poweredCosKernel_periodization s ht

/-- Haagerup's exact integral evaluation, equation (13), with all analytic
steps proved: periodization, local integration by parts, and the beta integral. -/
theorem haagerup_integral_eval {s : ℝ} (hs : 0 < s) :
    (2 / (Real.pi * Real.sqrt s)) * (∫ t in Ioi (0 : ℝ), poweredCosKernel s t) =
      haagerupF s := by
  rw [poweredCosKernel_folding hs, local_cosine_integral_identity hs,
    haagerupF_cosine_integral hs]
  have hsq := Real.sq_sqrt hs.le
  have hp : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hc : (2 / (Real.pi * Real.sqrt s)) * s = 2 * Real.sqrt s / Real.pi := by
    field_simp
    nlinarith only [hsq]
  rw [← mul_assoc, hc]

/-- Haagerup's weighted inequality, the first bound in equation (6). -/
theorem weighted_haagerup {n : ℕ} (a : Fin n → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∑ i, a i ^ 2 = 1) :
    (∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2)) ≤ rademacherMean a :=
  weighted_haagerup_of_integral (fun _ hs => haagerup_integral_eval hs) a ha0 ha

/-- The complete fourth-moment consequence of Haagerup's inequality. -/
theorem haagerup_fourth_moment {n : ℕ} (a : Fin n → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : ∑ i, a i ^ 2 = 1) :
    haagerupF (1 / ∑ i, a i ^ 4) ≤ rademacherMean a :=
  haagerup_fourth_moment_of_integral (fun _ hs => haagerup_integral_eval hs) a ha0 ha

#print axioms Szarek.haagerup_integral_eval
#print axioms Szarek.weighted_haagerup
#print axioms Szarek.haagerup_fourth_moment
#print axioms Szarek.poweredCosKernel_folding
end Szarek
