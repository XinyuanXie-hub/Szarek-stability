module

public import SmallCoefficientsBase
public import GaussianTail

@[expose] public section

open MeasureTheory Set
namespace Szarek

lemma tailPowerKernel_le_gaussian {u b t : ℝ} (hu : 0 ≤ u) (hb : 0 < b)
    (ht : 0 ≤ t) (htcut : t ≤ Real.pi / (2 * b)) :
    tailPowerKernel u b t ≤ Real.exp (-u * t ^ 2 / 2) / t ^ 2 := by
  have hbt : b * t ≤ Real.pi / 2 := by
    have h := (le_div_iff₀ (show 0 < 2*b by positivity)).mp htcut
    nlinarith
  have hc := cos_nonneg_first_quadrant (mul_nonneg hb.le ht) hbt
  have h := Real.rpow_le_rpow hc (cos_le_gaussian (mul_nonneg hb.le ht) hbt)
    (show 0 ≤ u / b ^ 2 by positivity)
  rw [← Real.exp_mul] at h
  have he : (-((b * t) ^ 2) / 2) * (u / b ^ 2) = -u * t ^ 2 / 2 := by
    field_simp
  rw [he] at h
  unfold tailPowerKernel
  rw [abs_of_nonneg hc]
  exact div_le_div_of_nonneg_right h (sq_nonneg t)

lemma integrable_scaled_gaussian_tail_cosine {u R : ℝ} (hu : 0 ≤ u) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => Real.exp (-u * t ^ 2 / 2) / t ^ 2) (Ioi R) := by
  have hi : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [Real.rpow_neg (show 0 ≤ t from (hR.trans ht).le), Real.rpow_two, one_div]
  apply hi.mono' ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-u * t ^ 2 / 2) / t ^ 2)).aestronglyMeasurable)
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg hu (sq_nonneg t)]

lemma integral_tailPowerKernel_scale {u b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi (Real.pi / (2 * b)), tailPowerKernel u b t) =
      b * ∫ t in Ioi (Real.pi / 2), |Real.cos t| ^ (u / b ^ 2) / t ^ 2 := by
  have he : tailPowerKernel u b = fun t => b ^ 2 *
      (|Real.cos (b * t)| ^ (u / b ^ 2) / (b * t) ^ 2) := by
    funext t
    unfold tailPowerKernel
    by_cases ht : t = 0
    · simp [ht]
    · field_simp
  rw [he, integral_const_mul,
    integral_comp_mul_left_Ioi (fun t => |Real.cos t| ^ (u / b ^ 2) / t ^ 2)
      (Real.pi / (2 * b)) hb]
  have harg : b * (Real.pi / (2 * b)) = Real.pi / 2 := by field_simp
  rw [harg, smul_eq_mul]
  field_simp

/-- Rescaled version of equation (19), used after splitting the tail at pi/(2b). -/
lemma integral_tailPowerKernel_bound_of_cosine_tail {u b : ℝ} (hu : 0 < u) (hb : 0 < b)
    (hp : 1 / 2 < u / b ^ 2)
    (hcos : ∀ s : ℝ, 1 / 2 < s →
      (∫ t in Ioi (Real.pi / 2), |Real.cos t| ^ s / t ^ 2) ≤
        (1 / 3 : ℝ) * Real.sqrt (Real.pi / (2 * s))) :
    (∫ t in Ioi (Real.pi / (2 * b)), tailPowerKernel u b t) ≤
      (1 / 3 : ℝ) * Real.sqrt (Real.pi / 2) * b ^ 2 / Real.sqrt u := by
  rw [integral_tailPowerKernel_scale hb]
  have h := mul_le_mul_of_nonneg_left (hcos _ hp) hb.le
  have he : Real.pi / (2 * (u / b ^ 2)) = (Real.pi / 2 * b ^ 2) / u := by
    field_simp
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le] at h
  convert h using 1; ring

/-- The scaled tail estimate required in the proof of paper Lemma 2. -/
theorem scaled_cosine_tail_bound {u b y : ℝ} (hb : 0 < b) (hby : b ≤ y)
    (hu : 3 * y ^ 2 ≤ u)
    (hcos : ∀ s : ℝ, 1 / 2 < s →
      (∫ t in Ioi (Real.pi / 2), |Real.cos t| ^ s / t ^ 2) ≤
        (1 / 3 : ℝ) * Real.sqrt (Real.pi / (2 * s))) :
    (∫ t in Ioi (Real.pi / (2 * y)), tailPowerKernel u b t) ≤
      (∫ t in Ioi (Real.pi / (2 * y)), Real.exp (-u * t ^ 2 / 2) / t ^ 2) +
        (1 / 3 : ℝ) * Real.sqrt (Real.pi / 2) * b ^ 2 / Real.sqrt u := by
  have hy : 0 < y := lt_of_lt_of_le hb hby
  have hu0 : 0 < u := by nlinarith [sq_pos_of_pos hy]
  have hRy : 0 < Real.pi / (2 * y) := by positivity
  have hRb : 0 < Real.pi / (2 * b) := by positivity
  have hcut : Real.pi / (2 * y) ≤ Real.pi / (2 * b) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
  have hp : 1 / 2 < u / b ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith [sq_nonneg (y-b)]
  have hfi := tailPowerKernel_integrable hu0.le hRy b
  have hfb := tailPowerKernel_integrable hu0.le hRb b
  have hgi := integrable_scaled_gaussian_tail_cosine hu0.le hRy
  have hi : IntegrableOn ((Ioi (Real.pi / (2*b))).indicator (tailPowerKernel u b))
      (Ioi (Real.pi / (2*y))) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr hfb).integrableOn
  have hpoint : ∀ t ∈ Ioi (Real.pi / (2*y)), tailPowerKernel u b t ≤
      Real.exp (-u*t^2/2)/t^2 + (Ioi (Real.pi/(2*b))).indicator (tailPowerKernel u b) t := by
    intro t ht
    by_cases htb : t ≤ Real.pi / (2*b)
    · rw [indicator_of_notMem (show t ∉ Ioi (Real.pi/(2*b)) from not_lt.mpr htb), add_zero]
      exact tailPowerKernel_le_gaussian hu0.le hb (le_of_lt (hRy.trans ht)) htb
    · rw [indicator_of_mem (show t ∈ Ioi (Real.pi/(2*b)) from lt_of_not_ge htb)]
      have hnonneg : 0 ≤ Real.exp (-u*t^2/2)/t^2 := by positivity
      linarith
  have h := integral_mono_ae hfi (hgi.add hi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpoint))
  simp only [Pi.add_apply] at h
  rw [integral_add hgi hi, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hcut)] at h
  exact h.trans (add_le_add le_rfl (integral_tailPowerKernel_bound_of_cosine_tail hu0 hb hp hcos))

#print axioms Szarek.scaled_cosine_tail_bound
end Szarek
