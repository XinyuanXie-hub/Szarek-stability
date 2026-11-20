module

public import HaagerupLaplace
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace Szarek

lemma integrableOn_rescaled_tanh (u : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.tanh (u * t / 2)) (Ioi 0) := by
  have hcont : Continuous Real.tanh :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_tanh t).continuousAt)
  refine (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)).mono' (by fun_prop) ?_
  filter_upwards [] with t
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_one, neg_one_mul] using
    mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one (u * t / 2)).le (Real.exp_pos (-t)).le

lemma inverse_log_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => Real.log (haagerupF (1 / x)))
      (-(1 / 2 : ℝ) * ∫ t : ℝ in Ioi 0, Real.exp (-t) * Real.tanh (u * t / 2) / u) u := by
  have hui : 0 < u⁻¹ := inv_pos.mpr hu
  have hscale := integral_comp_mul_left_Ioi'
    (fun t : ℝ => Real.exp (-u⁻¹ * t) * Real.tanh (t / 2)) 0 hu
  have hfun : (fun t : ℝ => Real.exp (-u⁻¹ * (u * t)) * Real.tanh (u * t / 2)) =
      (fun t : ℝ => Real.exp (-t) * Real.tanh (u * t / 2)) := by
    funext t
    congr 2
    field_simp
  simp only [smul_eq_mul, mul_zero, hfun] at hscale
  have hlog : HasDerivAt (fun s => Real.log (haagerupF s))
      ((1 / 2 : ℝ) * ∫ t : ℝ in Ioi 0, Real.exp (-u⁻¹ * t) * Real.tanh (t / 2)) u⁻¹ := by
    rw [← deriv_log_haagerupF_laplace hui]
    exact (((differentiableAt_haagerupF hui).hasDerivAt.log (ne_of_gt (haagerupF_pos hui))).differentiableAt).hasDerivAt
  have hc := hlog.comp u ((hasDerivAt_id u).inv hu.ne')
  convert hc using 1
  · simp only [one_div, Function.comp_def]
  · simp only [id_eq]
    rw [← hscale, integral_div]
    generalize (∫ t : ℝ in Ioi 0, Real.exp (-t) * Real.tanh (u * t / 2)) = J
    field_simp

lemma rescaled_tanh_integral_antitone : AntitoneOn
    (fun u : ℝ => ∫ t : ℝ in Ioi 0, Real.exp (-t) * Real.tanh (u * t / 2) / u) (Ioi 0) := by
  intro x hx y hy hxy
  apply setIntegral_mono_on ((integrableOn_rescaled_tanh y).div_const y)
    ((integrableOn_rescaled_tanh x).div_const x) measurableSet_Ioi
  intro t ht
  have hxt : 0 < x * t / 2 := div_pos (mul_pos hx ht) (by norm_num)
  have hyt : 0 < y * t / 2 := div_pos (mul_pos hy ht) (by norm_num)
  have ht0 : 0 < t := ht
  have harg : x * t / 2 ≤ y * t / 2 := by nlinarith
  have h := tanh_div_antitone hxt hyt harg
  have hc := (div_le_div_iff₀ hyt hxt).mp h
  have hratio : Real.tanh (y * t / 2) / y ≤ Real.tanh (x * t / 2) / x := by
    apply (div_le_div_iff₀ hy hx).mpr
    have he : Real.tanh (y * t / 2) * (x * t / 2) =
        (Real.tanh (y * t / 2) * x) * (t / 2) := by ring
    have he' : Real.tanh (x * t / 2) * (y * t / 2) =
        (Real.tanh (x * t / 2) * y) * (t / 2) := by ring
    rw [he, he'] at hc
    exact (mul_le_mul_iff_of_pos_right (div_pos ht0 (by norm_num))).mp hc
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-t)).le

lemma log_haagerupF_inverse_convex :
    ConvexOn ℝ (Ioi 0) (fun u : ℝ => Real.log (haagerupF (1 / u))) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ioi 0)
  · intro u hu
    exact (inverse_log_hasDerivAt hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (inverse_log_hasDerivAt (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(inverse_log_hasDerivAt (interior_subset hx)).deriv,
      (inverse_log_hasDerivAt (interior_subset hy)).deriv]
    exact mul_le_mul_of_nonpos_left
      (rescaled_tanh_integral_antitone (interior_subset hx) (interior_subset hy) hxy) (by norm_num)

lemma haagerupF_inverse_convex :
    ConvexOn ℝ (Ioi 0) (fun u : ℝ => haagerupF (1 / u)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hlog := log_haagerupF_inverse_convex.2 hx hy ha hb hab
  have hexp := Real.exp_le_exp.mpr hlog
  have hcomb : a • x + b • y ∈ Ioi (0 : ℝ) := (convex_Ioi 0) hx hy ha hb hab
  rw [Real.exp_log (haagerupF_pos (one_div_pos.mpr hcomb))] at hexp
  have he := convexOn_exp.2
    (show Real.log (haagerupF (1 / x)) ∈ (univ : Set ℝ) by trivial)
    (show Real.log (haagerupF (1 / y)) ∈ (univ : Set ℝ) by trivial) ha hb hab
  rw [Real.exp_log (haagerupF_pos (one_div_pos.mpr hx)),
    Real.exp_log (haagerupF_pos (one_div_pos.mpr hy))] at he
  exact hexp.trans he

#print axioms Szarek.haagerupF_inverse_convex
end Szarek
