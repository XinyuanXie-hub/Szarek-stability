module

public import TrigKernel
public import CosineBeta
public import GammaBounds
public import EvenPeriodization
public import HaagerupIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

open Set MeasureTheory
open scoped Interval
namespace Szarek

noncomputable def foldedCosineTail (s t : ℝ) : ℝ :=
  Real.cos t ^ s * (1 / Real.sin t ^ 2 - 1 / t ^ 2)

lemma foldedCosineTail_nonneg {s t : ℝ} (ht : 0 < t) (htp : t < Real.pi / 2) :
    0 ≤ foldedCosineTail s t := by
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩).le
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hst : Real.sin t ^ 2 ≤ t ^ 2 := by nlinarith [Real.sin_le ht.le]
  exact mul_nonneg (Real.rpow_nonneg hc _)
    (sub_nonneg.mpr (one_div_le_one_div_of_le (sq_pos_of_pos hs) hst))

lemma foldedCosineTail_le {s t : ℝ} (ht : 0 < t) (htp : t < Real.pi / 2) :
    foldedCosineTail s t ≤ (1/3 : ℝ) * Real.cos t ^ (s - 1/2) := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩
  have he : Real.cos t ^ s = Real.cos t ^ (s - 1/2) * Real.sqrt (Real.cos t) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_left (trigKernel_le_one_third ht htp)
    (Real.rpow_nonneg hc.le (s-1/2))
  simpa only [foldedCosineTail, he, mul_assoc, mul_comm (1/3 : ℝ)] using h

lemma foldedCosineTail_intervalIntegrable {s : ℝ} (hs : 1/2 < s) :
    IntervalIntegrable (foldedCosineTail s) volume 0 (Real.pi / 2) := by
  have hg := (cosine_rpow_intervalIntegrable (show 0 ≤ s - 1/2 by linarith)).const_mul (1/3 : ℝ)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity : (0 : ℝ) ≤ Real.pi/2)] at hg ⊢
  apply hg.mono_nonneg
  · exact (show Measurable (foldedCosineTail s) by unfold foldedCosineTail; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact foldedCosineTail_nonneg ht.1 ht.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact foldedCosineTail_le ht.1 ht.2

lemma foldedCosineTail_integral_le {s : ℝ} (hs : 1/2 < s) :
    (∫ t : ℝ in (0:ℝ)..(Real.pi/2), foldedCosineTail s t) ≤
      (1/3 : ℝ) * (∫ t : ℝ in (0:ℝ)..(Real.pi/2), Real.cos t ^ (s-1/2)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by positivity)
    (foldedCosineTail_intervalIntegrable hs)
    ((cosine_rpow_intervalIntegrable (show 0 ≤ s-1/2 by linarith)).const_mul _)
  exact fun t ht => foldedCosineTail_le ht.1 ht.2

lemma foldedCosineTail_bound_of_kershaw {s : ℝ} (hs : 1/2 < s)
    (hk : haagerupF (s-1/2) ≤ Real.sqrt (2/Real.pi) *
      Real.sqrt ((s-1/2)/((s-1/2)+1/2))) :
    (∫ t : ℝ in (0:ℝ)..(Real.pi/2), foldedCosineTail s t) ≤
      (1/3 : ℝ) * Real.sqrt (Real.pi/(2*s)) := by
  have hu : 0 < s-1/2 := by linarith
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hss : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr (show 0<s by linarith)).ne'
  have hsu : Real.sqrt (s-1/2) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hs2 : Real.sqrt (2:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have he : (1/3:ℝ) * (∫ t : ℝ in (0:ℝ)..(Real.pi/2), Real.cos t ^ (s-1/2)) =
      (Real.pi / (6 * Real.sqrt (s-1/2))) * haagerupF (s-1/2) := by
    rw [haagerupF_cosine_integral hu]
    generalize hq : Real.sqrt (s-1/2) = q
    have hqne : q ≠ 0 := by rw [← hq]; exact hsu
    field_simp [hqne, Real.pi_ne_zero]
    ring
  calc
    _ ≤ (Real.pi/(6*Real.sqrt (s-1/2))) * haagerupF (s-1/2) := by
      rw [← he]
      exact foldedCosineTail_integral_le hs
    _ ≤ (Real.pi/(6*Real.sqrt (s-1/2))) *
        (Real.sqrt (2/Real.pi) * Real.sqrt ((s-1/2)/((s-1/2)+1/2))) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by
      rw [show s-1/2+1/2=s by ring,
        Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_div hu.le,
        Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      generalize hq : Real.sqrt (s-1/2) = q at *
      field_simp [hsu, hsp, hss, hs2]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sq_sqrt Real.pi_pos.le]

lemma foldedCosineTail_bound {s : ℝ} (hs : 1/2 < s) :
    (∫ t : ℝ in (0:ℝ)..(Real.pi/2), foldedCosineTail s t) ≤
      (1/3 : ℝ) * Real.sqrt (Real.pi/(2*s)) :=
  foldedCosineTail_bound_of_kershaw hs (haagerupF_kershaw (by linarith))

/-- Conditional composition pending only the periodic folding identity. -/
lemma cosine_tail_bound_of_folding {s : ℝ} (hs : 1/2 < s)
    (hfold : (∫ t : ℝ in Ioi (Real.pi/2), |Real.cos t| ^ s / t ^ 2) =
      ∫ t : ℝ in (0:ℝ)..(Real.pi/2), foldedCosineTail s t) :
    (∫ t : ℝ in Ioi (Real.pi/2), |Real.cos t| ^ s / t ^ 2) ≤
      (1/3 : ℝ) * Real.sqrt (Real.pi/(2*s)) := by
  rw [hfold]
  exact foldedCosineTail_bound hs

lemma cosine_tail_integrable {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ => |Real.cos t| ^ s / t ^ 2) (Ioi (Real.pi/2)) := by
  have hg : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi (Real.pi/2)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (c := Real.pi/2) (by norm_num) (by positivity)).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht1 : Real.pi/2 < t := ht
    have ht0 : 0 ≤ t := by linarith [Real.pi_pos]
    change t ^ (-(2:ℝ)) = 1 / t ^ 2
    rw [Real.rpow_neg ht0, Real.rpow_two, one_div]
  apply hg.mono_nonneg
  · exact (show Measurable (fun t : ℝ => |Real.cos t| ^ s / t ^ 2) by fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact div_le_div_of_nonneg_right (Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one t) hs) (sq_nonneg _)

#print axioms foldedCosineTail_bound
#print axioms cosine_tail_integrable
lemma cosine_tail_folding {s : ℝ} (hs : 0 ≤ s) :
    (∫ t : ℝ in Ioi (Real.pi/2), |Real.cos t| ^ s / t ^ 2) =
      ∫ t : ℝ in (0:ℝ)..(Real.pi/2), foldedCosineTail s t := by
  let g : ℝ → ℝ := fun t => |Real.cos t| ^ s / t ^ 2
  let f : ℝ → ℝ := fun t => if Real.pi/2 < |t| then g t else 0
  have he : Function.Even f := by
    intro t
    simp [f, g, Real.cos_neg]
  have hf_eq : f = fun t => (Ioi (Real.pi/2)).indicator g t + (Ioi (Real.pi/2)).indicator g (-t) := by
    funext t
    by_cases ht : 0 ≤ t
    · have hn : ¬ Real.pi/2 < -t := by linarith [Real.pi_pos]
      simp [f, Set.indicator_apply, mem_Ioi, abs_of_nonneg ht, hn]
    · have ht0 : t < 0 := lt_of_not_ge ht
      have hn : ¬ Real.pi/2 < t := by linarith [Real.pi_pos]
      simp [f, g, Set.indicator_apply, mem_Ioi, abs_of_neg ht0, hn, Real.cos_neg]
  have hi : Integrable f := by
    rw [hf_eq]
    have h := (cosine_tail_integrable hs).integrable_indicator measurableSet_Ioi
    exact h.add h.comp_neg
  have hpos : (∫ t in Ioi (0:ℝ), f t) = ∫ t in Ioi (Real.pi/2), g t := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Ioi (Real.pi/2)).indicator g t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [f, Set.indicator_apply, mem_Ioi, abs_of_pos (show 0<t from ht)]
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Ioi,
          inter_eq_right.mpr (Ioi_subset_Ioi (show (0:ℝ) ≤ Real.pi/2 by positivity))]
  rw [← hpos, integral_periodization_even_int Real.pi_pos hi he]
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hterm (n : ℤ) : f ((n:ℝ)*Real.pi+t) =
      Real.cos t ^ s * (if n = 0 then 0 else 1 / (t+(n:ℝ)*Real.pi)^2) := by
    by_cases hn : n = 0
    · subst n
      simp [f, ht.2.not_gt, abs_of_pos ht.1]
    · have hab : Real.pi/2 < |(n:ℝ)*Real.pi+t| := by
        rcases lt_or_gt_of_ne hn with hneg | hpos
        · have hn1 : (n:ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
          apply (lt_abs).mpr
          right
          nlinarith [ht.2, mul_nonpos_of_nonpos_of_nonneg (show (n:ℝ)+1 ≤ 0 by linarith) Real.pi_pos.le]
        · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          apply (lt_abs).mpr
          left
          nlinarith [ht.1, Real.pi_pos, mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith) Real.pi_pos.le]
      have hcos : |Real.cos ((n:ℝ)*Real.pi+t)| = Real.cos t := by
        rw [add_comm, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
          abs_of_pos hc]
      simp only [f, hab, ite_true, g, hcos, hn, ite_false]
      rw [add_comm ((n:ℝ)*Real.pi) t]
      ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum := scaled_reciprocal_square_int_sum ht
  have hsm : Summable (fun n : ℤ => 1 / (t+(n:ℝ)*Real.pi)^2) := by
    by_contra hh
    rw [tsum_eq_zero_of_not_summable hh] at hsum
    have : 0 < (1:ℝ) / Real.sin t ^ 2 := by positivity
    linarith
  have hrem := hsm.tsum_eq_add_tsum_ite (0:ℤ)
  simp only [Int.cast_zero, zero_mul, add_zero] at hrem
  rw [hsum] at hrem
  have hh : (∑' n : ℤ, if n=0 then 0 else 1/(t+(n:ℝ)*Real.pi)^2) =
      1/Real.sin t^2 - 1/t^2 := by linarith
  rw [hh]
  rfl

lemma cosine_tail_bound {s : ℝ} (hs : 1/2 < s) :
    (∫ t : ℝ in Ioi (Real.pi/2), |Real.cos t| ^ s / t ^ 2) ≤
      (1/3 : ℝ) * Real.sqrt (Real.pi/(2*s)) :=
  cosine_tail_bound_of_folding hs (cosine_tail_folding (by linarith))

#print axioms cosine_tail_bound
end Szarek
