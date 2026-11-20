module

public import HaagerupAnalysis
public import HaagerupLaplace
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology
noncomputable section
namespace Szarek

lemma gamma_midpoint_sq_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Real.Gamma ((x + y) / 2)) ^ 2 ≤ Real.Gamma x * Real.Gamma y := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  rw [show 1 / 2 * x + 1 / 2 * y = (x + y) / 2 by ring,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have hsq := mul_self_le_mul_self (Real.Gamma_pos_of_pos (show 0 < (x + y) / 2 by positivity)).le h
  have hsx := Real.sq_sqrt (Real.Gamma_pos_of_pos hx).le
  have hsy := Real.sq_sqrt (Real.Gamma_pos_of_pos hy).le
  have he : (Real.sqrt (Real.Gamma x) * Real.sqrt (Real.Gamma y)) *
      (Real.sqrt (Real.Gamma x) * Real.sqrt (Real.Gamma y)) = Real.Gamma x * Real.Gamma y := by
    calc
      _ = (Real.sqrt (Real.Gamma x)) ^ 2 * (Real.sqrt (Real.Gamma y)) ^ 2 := by ring
      _ = _ := by rw [hsx, hsy]
  simpa only [he, ← sq] using hsq

lemma gamma_ratio_sq_bounds {s : ℝ} (hs : 0 < s) :
    s ^ 2 / (2 * (s + 1)) ≤ (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2)) ^ 2 ∧
    (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2)) ^ 2 ≤ s / 2 := by
  have hG : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hH : 0 < Real.Gamma ((s + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hu := gamma_midpoint_sq_le (show 0 < s / 2 by positivity)
    (show 0 < s / 2 + 1 by positivity)
  rw [show (s / 2 + (s / 2 + 1)) / 2 = (s + 1) / 2 by ring,
    Real.Gamma_add_one (by positivity : s / 2 ≠ 0)] at hu
  have hl := gamma_midpoint_sq_le (show 0 < (s + 1) / 2 by positivity)
    (show 0 < (s + 1) / 2 + 1 by positivity)
  rw [show ((s + 1) / 2 + ((s + 1) / 2 + 1)) / 2 = s / 2 + 1 by ring,
    Real.Gamma_add_one (by positivity : s / 2 ≠ 0),
    Real.Gamma_add_one (by positivity : (s + 1) / 2 ≠ 0)] at hl
  constructor
  · rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  · rw [div_pow]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith

lemma haagerupF_sq_formula {s : ℝ} (hs : 0 < s) :
    (haagerupF s) ^ 2 = 4 / (Real.pi * s) *
      (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2)) ^ 2 := by
  unfold haagerupF
  rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]
  norm_num

lemma haagerupF_sq_bounds {s : ℝ} (hs : 0 < s) :
    (2 / Real.pi) * (s / (s + 1)) ≤ (haagerupF s) ^ 2 ∧
      (haagerupF s) ^ 2 ≤ 2 / Real.pi := by
  obtain ⟨hl, hu⟩ := gamma_ratio_sq_bounds hs
  rw [haagerupF_sq_formula hs]
  have hp : 0 ≤ 4 / (Real.pi * s) := by positivity
  constructor
  · convert mul_le_mul_of_nonneg_left hl hp using 1; field_simp; ring
  · convert mul_le_mul_of_nonneg_left hu hp using 1; field_simp; ring

lemma tendsto_haagerupF_sq :
    Tendsto (fun s : ℝ => (haagerupF s) ^ 2) atTop (𝓝 (2 / Real.pi)) := by
  have hratio : Tendsto (fun s : ℝ => s / (s + 1)) atTop (𝓝 1) := by
    have hplus : Tendsto (fun s : ℝ => s + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_id
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hplus)
    have he : (fun s : ℝ => s / (s + 1)) =ᶠ[atTop] (fun s => 1 - (s + 1)⁻¹) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      field_simp
      ring
    exact (tendsto_congr' he).mpr (by simpa using h)
  have hl : Tendsto (fun s : ℝ => (2 / Real.pi) * (s / (s + 1))) atTop
      (𝓝 (2 / Real.pi)) := by simpa using hratio.const_mul (2 / Real.pi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs using (haagerupF_sq_bounds hs).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs using (haagerupF_sq_bounds hs).2

lemma tendsto_haagerupF : Tendsto haagerupF atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have h := (Real.continuous_sqrt.tendsto (2 / Real.pi)).comp tendsto_haagerupF_sq
  have he : haagerupF =ᶠ[atTop] (fun s : ℝ => Real.sqrt ((haagerupF s) ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [Real.sqrt_sq (haagerupF_pos hs).le]
  exact (tendsto_congr' he).mpr h

lemma tanh_half_ge_exp (t : ℝ) : 1 - Real.exp (-t / 2) ≤ Real.tanh (t / 2) := by
  rw [tanh_half_exp]
  have he : Real.exp (-t) = (Real.exp (-t / 2)) ^ 2 := by
    rw [show -t = -t / 2 + -t / 2 by ring, Real.exp_add]
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  have h := mul_nonneg (Real.exp_pos (-t / 2)).le (sq_nonneg (1 - Real.exp (-t / 2)))
  nlinarith

lemma deriv_log_haagerupF_kershaw {s : ℝ} (hs : 0 < s) :
    (1 / s - 1 / (s + 1 / 2)) / 2 ≤ deriv (fun s => Real.log (haagerupF s)) s := by
  have hi₁ := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have hi₂ := integrableOn_exp_mul_Ioi
    (neg_lt_zero.mpr (show 0 < s + 1 / 2 by linarith)) 0
  have he (t : ℝ) : Real.exp (-s * t) - Real.exp (-(s + 1 / 2) * t) =
      Real.exp (-s * t) * (1 - Real.exp (-t / 2)) := by
    rw [show -(s + 1 / 2) * t = -s * t + -t / 2 by ring, Real.exp_add]
    ring
  have hmono := setIntegral_mono_on (hi₁.sub hi₂) (integrableOn_exp_tanh hs)
    measurableSet_Ioi (fun t ht => by
      simp only [Pi.sub_apply]
      rw [he]
      exact mul_le_mul_of_nonneg_left (tanh_half_ge_exp t) (Real.exp_pos _).le)
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub hi₁ hi₂,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0,
    integral_exp_mul_Ioi (neg_lt_zero.mpr (show 0 < s + 1 / 2 by linarith)) 0] at hmono
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hmono
  rw [deriv_log_haagerupF_laplace hs]
  linarith

def kershawLog (s : ℝ) : ℝ :=
  Real.log (haagerupF s) - (Real.log s - Real.log (s + 1 / 2)) / 2

lemma hasDerivAt_kershawLog {s : ℝ} (hs : 0 < s) :
    HasDerivAt kershawLog
      (deriv (fun s => Real.log (haagerupF s)) s - (1 / s - 1 / (s + 1 / 2)) / 2) s := by
  have hlog := ((differentiableAt_haagerupF hs).log (haagerupF_pos hs).ne').hasDerivAt
  have hright := ((Real.hasDerivAt_log hs.ne').sub
    (((hasDerivAt_id s).add_const (1 / 2 : ℝ)).log (by positivity : s + 1 / 2 ≠ 0))).div_const 2
  convert hlog.sub hright using 1
  · funext x
    simp [kershawLog]
  · simp [one_div]

lemma monotoneOn_kershawLog : MonotoneOn kershawLog (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · intro s hs
    exact (hasDerivAt_kershawLog hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (hasDerivAt_kershawLog (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hasDerivAt_kershawLog (interior_subset hs)).deriv]
    exact sub_nonneg.mpr (deriv_log_haagerupF_kershaw (interior_subset hs))

lemma tendsto_kershawLog : Tendsto kershawLog atTop
    (𝓝 (Real.log (Real.sqrt (2 / Real.pi)))) := by
  have hc : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hlog := (Real.continuousAt_log hc.ne').tendsto.comp tendsto_haagerupF
  have hdiff := ((Real.tendsto_log_comp_add_sub_log (1 / 2 : ℝ)).neg).div_const 2
  change Tendsto (fun s => Real.log (haagerupF s) - (Real.log s - Real.log (s + 1 / 2)) / 2)
    atTop (𝓝 (Real.log (Real.sqrt (2 / Real.pi))))
  simpa only [Function.comp_apply, neg_sub, neg_zero, zero_div, sub_zero] using hlog.sub hdiff

lemma haagerupF_kershaw {s : ℝ} (hs : 0 < s) :
    haagerupF s ≤ Real.sqrt (2 / Real.pi) * Real.sqrt (s / (s + 1 / 2)) := by
  have hbound : kershawLog s ≤ Real.log (Real.sqrt (2 / Real.pi)) := by
    apply ge_of_tendsto tendsto_kershawLog
    filter_upwards [eventually_ge_atTop s] with t ht
    exact monotoneOn_kershawLog hs (lt_of_lt_of_le hs ht) ht
  have hC : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hR : 0 < Real.sqrt (s / (s + 1 / 2)) := by positivity
  apply (Real.log_le_log_iff (haagerupF_pos hs) (mul_pos hC hR)).mp
  rw [Real.log_mul hC.ne' hR.ne', Real.log_sqrt (x := s / (s + 1 / 2)) (by positivity),
    Real.log_div hs.ne' (by positivity : s + 1 / 2 ≠ 0)]
  unfold kershawLog at hbound
  linarith

#print axioms Szarek.haagerupF_kershaw
#print axioms Szarek.deriv_log_haagerupF_kershaw
#print axioms Szarek.tendsto_haagerupF
#print axioms Szarek.haagerupF_sq_bounds
end Szarek
