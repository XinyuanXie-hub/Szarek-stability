import GaussianTail
import CaseAlgebra
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped Topology
namespace Szarek

lemma integrable_scaled_gaussian_first_moment {u : ℝ} (hu : 0 < u) :
    Integrable (fun x : ℝ => x * Real.exp (-u * x ^ 2 / 2)) := by
  convert! integrable_mul_exp_neg_mul_sq (b := u / 2) (by positivity) using 1
  ext x
  congr 2
  ring

lemma integral_scaled_gaussian_first_moment {u : ℝ} (hu : 0 < u) (R : ℝ) :
    (∫ x in Ioi R, x * Real.exp (-u * x ^ 2 / 2)) = Real.exp (-u * R ^ 2 / 2) / u := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => -Real.exp (-u * x ^ 2 / 2) / u)
      (x * Real.exp (-u * x ^ 2 / 2)) x := by
    intro x
    convert! (((((hasDerivAt_id x).pow 2).const_mul (-u)).div_const 2).exp.neg.div_const u) using 1
    simp only [Pi.pow_apply, id_eq]
    field_simp
    ring
  have ht : Tendsto (fun x : ℝ => -Real.exp (-u * x ^ 2 / 2) / u) atTop (𝓝 (0 : ℝ)) := by
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop_of_neg (by linarith : -u / 2 < 0))
    have he : (fun x : ℝ => Real.exp (-u * x ^ 2 / 2)) =
        (fun x : ℝ => Real.exp ((-u / 2) * x ^ 2)) := by funext x; congr 1; ring
    have ht0 : Tendsto (fun x : ℝ => Real.exp (-u * x ^ 2 / 2)) atTop (𝓝 (0 : ℝ)) := by
      rw [he]
      exact h
    simpa using ht0.neg.div_const u
  simpa [neg_div, neg_neg] using integral_Ioi_of_hasDerivAt_of_tendsto' (a := R) (fun x _ => hd x)
    (integrable_scaled_gaussian_first_moment hu).integrableOn ht

lemma scaled_gaussian_tail_pointwise {R u x : ℝ} (hR : 0 < R) (hx : R ≤ x) :
    Real.exp (-u * x ^ 2 / 2) / x ^ 2 ≤
      (x * Real.exp (-u * x ^ 2 / 2)) / R ^ 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le hR hx
  have hcube : R ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hR.le hx 3
  apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (pow_pos hR 3)).mpr
  have h := mul_le_mul_of_nonneg_left hcube (Real.exp_pos (-u * x ^ 2 / 2)).le
  nlinarith only [h]

lemma integrable_scaled_gaussian_tail {R u : ℝ} (hu : 0 < u) (hR : 0 < R) :
    IntegrableOn (fun x : ℝ => Real.exp (-u * x ^ 2 / 2) / x ^ 2) (Ioi R) := by
  apply ((integrable_scaled_gaussian_first_moment hu).div_const (R ^ 3)).integrableOn.mono'
  · exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (-u * x ^ 2 / 2) / x ^ 2)).aestronglyMeasurable
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards [] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact scaled_gaussian_tail_pointwise hR hx.le

lemma integral_scaled_gaussian_tail_le {R u : ℝ} (hu : 0 < u) (hR : 0 < R) :
    (∫ x in Ioi R, Real.exp (-u * x ^ 2 / 2) / x ^ 2) ≤
      Real.exp (-u * R ^ 2 / 2) / (u * R ^ 3) := by
  calc
    _ ≤ ∫ x in Ioi R, (x * Real.exp (-u * x ^ 2 / 2)) / R ^ 3 := by
      apply integral_mono_ae (integrable_scaled_gaussian_tail hu hR)
        ((integrable_scaled_gaussian_first_moment hu).div_const _).integrableOn
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      exact Filter.Eventually.of_forall (fun x hx => scaled_gaussian_tail_pointwise hR hx.le)
    _ = _ := by rw [integral_div, integral_scaled_gaussian_first_moment hu]; ring

lemma exp_neg_three_le : Real.exp (-3) ≤ (1 : ℝ) / 16 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 5
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 16)).mpr
  linarith

/-- Gaussian-tail contribution to the smaller-coefficient comparison. -/
lemma scaled_gaussian_error_bound {u y : ℝ} (hu : 0 < u) (hy : 0 < y)
    (hscale : 3 * y ^ 2 ≤ u) :
    (2 / Real.pi) * (∫ t : ℝ in Ioi (Real.pi / (2 * y)),
      Real.exp (-u * t ^ 2 / 2) / t ^ 2) ≤
      Real.sqrt (2 / Real.pi) * (y ^ 2 / Real.sqrt u) / 60 := by
  have hp := Real.pi_pos
  have hR : 0 < Real.pi / (2 * y) := by positivity
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsq := Real.sq_sqrt hu.le
  have hyS : y ≤ Real.sqrt u := by nlinarith [sq_nonneg y]
  have hp2 : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hexponent : 3 ≤ u * (Real.pi / (2 * y)) ^ 2 / 2 := by
    have he : u * (Real.pi / (2 * y)) ^ 2 / 2 = Real.pi ^ 2 * u / (8 * y ^ 2) := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0 < 8 * y ^ 2)).mpr
    have hm := mul_le_mul_of_nonneg_right hp2 hu.le
    nlinarith only [hm, hscale]
  have he : Real.exp (-u * (Real.pi / (2 * y)) ^ 2 / 2) ≤ (1 : ℝ) / 16 := by
    apply (Real.exp_le_exp.mpr ?_).trans exp_neg_three_le
    linarith only [hexponent]
  have hp4 : (81 : ℝ) ≤ Real.pi ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 4
    norm_num at h
    exact h
  have hq : (60 : ℝ) / 81 ≤ Real.sqrt (2 / Real.pi) := by
    linarith [gaussian_constant_gt]
  calc
    _ ≤ (2 / Real.pi) * (Real.exp (-u * (Real.pi / (2 * y)) ^ 2 / 2) /
        (u * (Real.pi / (2 * y)) ^ 3)) :=
      mul_le_mul_of_nonneg_left (integral_scaled_gaussian_tail_le hu hR) (by positivity)
    _ ≤ (2 / Real.pi) * (((1 : ℝ) / 16) / (u * (Real.pi / (2 * y)) ^ 3)) := by
      gcongr
    _ = y ^ 3 / (Real.pi ^ 4 * u) := by field_simp; ring
    _ ≤ y ^ 3 / (81 * u) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hp4 hu.le
    _ ≤ y ^ 2 / (81 * Real.sqrt u) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 81 * u) (by positivity : 0 < 81 * Real.sqrt u)).mpr
      have hm := mul_le_mul_of_nonneg_left hyS (show 0 ≤ y ^ 2 * Real.sqrt u by positivity)
      nlinarith only [hm, hsq]
    _ ≤ Real.sqrt (2 / Real.pi) * (y ^ 2 / Real.sqrt u) / 60 := by
      have hm := mul_le_mul_of_nonneg_right hq (show 0 ≤ y ^ 2 / Real.sqrt u by positivity)
      calc
        _ = ((60 : ℝ) / 81 * (y ^ 2 / Real.sqrt u)) / 60 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hm (by norm_num)

#print axioms Szarek.scaled_gaussian_error_bound
end Szarek
