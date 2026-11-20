module

public import WeightedHaagerup
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

open MeasureTheory Set
namespace Szarek

lemma one_sub_rpow_le_max {s x : ℝ} (hs : 0 < s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x ^ s ≤ max 1 s * (1 - x) := by
  rcases eq_or_lt_of_le hx0 with hx | hx
  · subst x
    simp [Real.zero_rpow hs.ne']
  · by_cases hle : s ≤ 1
    · rw [max_eq_left hle, one_mul]
      have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 hle
      simpa only [Real.rpow_one] using sub_le_sub_left h (1:ℝ)
    · have hge : 1 ≤ s := le_of_not_ge hle
      have h := one_add_mul_self_le_rpow_one_add (s := x-1) (by linarith) hge
      rw [show 1 + (x-1) = x by ring] at h
      rw [max_eq_right hge]
      linarith

lemma poweredCosKernel_nonneg {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    0 ≤ poweredCosKernel s t :=
  div_nonneg (sub_nonneg.mpr (Real.rpow_le_one (abs_nonneg _) (Real.abs_cos_le_one t) hs))
    (sq_nonneg _)

lemma poweredCosKernel_le_fourier {s : ℝ} (hs : 0 < s) (t : ℝ) :
    poweredCosKernel s t ≤ max 1 s * fourierKernel 1 t := by
  have h := one_sub_rpow_le_max hs (abs_nonneg (Real.cos t)) (Real.abs_cos_le_one t)
  have hM : 0 ≤ max 1 s := le_trans (by norm_num) (le_max_left (1:ℝ) s)
  have h' : max 1 s * (1 - |Real.cos t|) ≤ max 1 s * (1 - Real.cos t) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left (le_abs_self _) _) hM
  have hd := div_le_div_of_nonneg_right (h.trans h') (sq_nonneg t)
  simpa only [poweredCosKernel, fourierKernel, mul_one, mul_div_assoc] using hd

lemma integrable_poweredCosKernel {s : ℝ} (hs : 0 < s) :
    Integrable (poweredCosKernel s) := by
  apply ((integrable_fourierKernel 1).const_mul (max 1 s)).mono_nonneg
  · exact (show Measurable (poweredCosKernel s) by unfold poweredCosKernel; fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (poweredCosKernel_nonneg hs.le)
  · exact Filter.Eventually.of_forall (poweredCosKernel_le_fourier hs)

lemma integrableOn_poweredCosKernel {s : ℝ} (hs : 0 < s) :
    IntegrableOn (poweredCosKernel s) (Ioi (0:ℝ)) :=
  (integrable_poweredCosKernel hs).integrableOn

lemma poweredCosKernel_local_bounds {s t : ℝ} (hs : 0 < s)
    (ht : t ∈ Ioo 0 (Real.pi/2)) :
    0 ≤ (1 - Real.cos t ^ s) / Real.sin t ^ 2 ∧
      (1 - Real.cos t ^ s) / Real.sin t ^ 2 ≤ max 1 s := by
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩).le
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hcos := Real.cos_le_one t
  constructor
  · exact div_nonneg (sub_nonneg.mpr (Real.rpow_le_one hc hcos hs.le)) (sq_nonneg _)
  · apply (div_le_iff₀ (sq_pos_of_pos hsin)).mpr
    have h := one_sub_rpow_le_max hs hc hcos
    have hM : 0 ≤ max 1 s := le_trans (by norm_num) (le_max_left (1:ℝ) s)
    have hdiff : 1 - Real.cos t ≤ Real.sin t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t, mul_nonneg hc (sub_nonneg.mpr hcos)]
    exact h.trans (mul_le_mul_of_nonneg_left hdiff hM)

lemma integrableOn_poweredCosKernel_local {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => (1 - Real.cos t ^ s) / Real.sin t ^ 2) (Ioo 0 (Real.pi/2)) := by
  have hg : IntegrableOn (fun _ : ℝ => max 1 s) (Ioo 0 (Real.pi/2)) :=
    (continuous_const.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  apply hg.mono_nonneg
  · exact (show Measurable (fun t : ℝ => (1 - Real.cos t ^ s) / Real.sin t ^ 2) by fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (poweredCosKernel_local_bounds hs ht).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (poweredCosKernel_local_bounds hs ht).2

#print axioms one_sub_rpow_le_max
#print axioms integrable_poweredCosKernel
end Szarek
