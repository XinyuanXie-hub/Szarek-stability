module

public import Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

@[expose] public section

open Set MeasureTheory
open scoped Interval
namespace Szarek

lemma real_beta_integral {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ (u - 1) * (1 - x) ^ (v - 1)) =
      Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h := Complex.betaIntegral_eq_Gamma_mul_div (u : ℂ) (v : ℂ) (by simpa using hu) (by simpa using hv)
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  push_cast
  rw [← h]
  unfold Complex.betaIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp
  rw [Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (by linarith [hx.2] : 0 ≤ 1 - x)]
  push_cast
  rfl

lemma sine_square_substitution (s : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), 2 * Real.cos t ^ s) =
      ∫ u : ℝ in (0 : ℝ)..1, u ^ (-(1 : ℝ)/2) * (1-u) ^ ((s-1)/2) := by
  let g : ℝ → ℝ := fun u => u ^ (-(1 : ℝ)/2) * (1-u)^((s-1)/2)
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := fun t => Real.sin t ^ 2)
    (f' := fun t => 2 * Real.sin t * Real.cos t) (g := g)
    (by fun_prop)
    (by
      intro x hx
      convert (Real.hasDerivAt_sin x).pow 2 using 1
      simp)
    (by
      intro x hx
      simp only [min_eq_left (by positivity : (0:ℝ) ≤ Real.pi/2),
        max_eq_right (by positivity : (0:ℝ) ≤ Real.pi/2)] at hx
      have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
      have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
      positivity)
  simp only [Real.sin_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), Real.sin_pi_div_two, one_pow] at h
  rw [← h]
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  dsimp [g]
  have hid : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hid, ← Real.rpow_natCast_mul hs.le, ← Real.rpow_natCast_mul hc.le]
  norm_num
  rw [Real.rpow_neg_one]
  have hp : Real.cos t ^ (s-1) * Real.cos t = Real.cos t ^ s := by
    rw [← Real.rpow_add_one hc.ne']
    congr 1
    ring
  rw [← hp]
  field_simp [hs.ne']

lemma cosine_rpow_integral {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), Real.cos t ^ s) =
      Real.sqrt Real.pi * Real.Gamma ((s+1)/2) / (2 * Real.Gamma ((s+2)/2)) := by
  have h := sine_square_substitution s
  rw [intervalIntegral.integral_const_mul] at h
  have hb := real_beta_integral (u := (1:ℝ)/2) (v := (s+1)/2) (by norm_num) (by linarith)
  have he : (s + 1) / 2 - 1 = (s - 1) / 2 := by ring
  norm_num only [show (1:ℝ)/2 - 1 = -1/2 by ring, he] at hb
  simp only [neg_div] at h
  rw [hb, Real.Gamma_one_half_eq] at h
  have ha : (1:ℝ)/2 + (s+1)/2 = (s+2)/2 := by ring
  rw [ha] at h
  rw [mul_comm (2:ℝ), ← div_div]
  linarith

lemma cosine_rpow_intervalIntegrable {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun t : ℝ => Real.cos t ^ s) volume 0 (Real.pi / 2) :=
  ((Real.continuous_rpow_const hs).comp Real.continuous_cos).intervalIntegrable _ _

lemma haagerupF_cosine_integral {s : ℝ} (hs : 0 < s) :
    haagerupF s = (2 * Real.sqrt s / Real.pi) *
      (∫ t : ℝ in (0 : ℝ)..(Real.pi / 2), Real.cos t ^ s) := by
  have hg : Real.Gamma ((s+2)/2) = (s/2)*Real.Gamma (s/2) := by
    convert Real.Gamma_add_one (s := s/2) (by positivity) using 1
    congr 1
    ring
  have hgs : Real.Gamma (s/2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hsp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hss : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  rw [cosine_rpow_integral hs, hg, haagerupF, Real.sqrt_mul Real.pi_pos.le]
  field_simp [hgs, hsp, hss, hs.ne']
  nlinarith [Real.sq_sqrt hs.le, Real.sq_sqrt Real.pi_pos.le]

#print axioms haagerupF_cosine_integral
end Szarek
