module

public import WeightedHaagerup
public import LemmaThree
public import CosineGaussian
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Szarek

noncomputable def tailPowerKernel (u b t : ℝ) : ℝ :=
  |Real.cos (b * t)| ^ (u / b ^ 2) / t ^ 2

lemma tailPowerKernel_integrable {u R : ℝ} (hu : 0 ≤ u) (hR : 0 < R) (b : ℝ) :
    IntegrableOn (tailPowerKernel u b) (Ioi R) := by
  have hi : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [Real.rpow_neg (show 0 ≤ t from (hR.trans ht).le), Real.rpow_two, one_div]
  apply hi.mono' ((by unfold tailPowerKernel; fun_prop : Measurable (tailPowerKernel u b)).aestronglyMeasurable)
  filter_upwards [] with t
  rw [tailPowerKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  have h := Real.rpow_le_rpow (abs_nonneg (Real.cos (b * t)))
    (Real.abs_cos_le_one (b * t)) (div_nonneg hu (sq_nonneg b))
  simpa using h

lemma tail_weighted_cos {m : ℕ} (b : Fin m → ℝ) {u : ℝ} (hu : 0 < u)
    (hsum : ∑ i, b i ^ 2 = u) (t : ℝ) :
    ∏ i, |Real.cos (b i * t)| ≤
      ∑ i, (b i ^ 2 / u) * |Real.cos (b i * t)| ^ (u / b i ^ 2) := by
  have hw : ∑ i, b i ^ 2 / u = 1 := by rw [← Finset.sum_div, hsum]; exact div_self hu.ne'
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun i => b i ^ 2 / u) (fun i => |Real.cos (b i * t)| ^ (u / b i ^ 2))
    (fun i _ => by positivity) hw (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have he : ∏ i, (|Real.cos (b i * t)| ^ (u / b i ^ 2)) ^ (b i ^ 2 / u) =
      ∏ i, |Real.cos (b i * t)| := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hb : b i = 0
    · simp [hb]
    · rw [← Real.rpow_mul (abs_nonneg _),
        show u / b i ^ 2 * (b i ^ 2 / u) = 1 by field_simp, Real.rpow_one]
  rwa [he] at h

lemma head_tail_cos_le_weighted {m : ℕ} (b : Fin m → ℝ) {u : ℝ} (hu : 0 < u)
    (hsum : ∑ i, b i ^ 2 = u) (x t : ℝ) :
    Real.cos (x * t) * (∏ i, Real.cos (b i * t)) ≤
      ∑ i, (b i ^ 2 / u) * |Real.cos (b i * t)| ^ (u / b i ^ 2) := by
  calc
    _ ≤ |Real.cos (x * t) * (∏ i, Real.cos (b i * t))| := le_abs_self _
    _ = |Real.cos (x * t)| * ∏ i, |Real.cos (b i * t)| := by rw [abs_mul, Finset.abs_prod]
    _ ≤ 1 * ∏ i, |Real.cos (b i * t)| :=
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ ≤ _ := by simpa using tail_weighted_cos b hu hsum t

lemma small_interval_cos_comparison {m : ℕ} (b : Fin m → ℝ) {u y : ℝ}
    (hy : 0 < y) (hsum : ∑ i, b i ^ 2 = u) (hb0 : ∀ i, 0 ≤ b i)
    (hby : ∀ i, b i ≤ y) (x : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (htR : t ≤ Real.pi / (2 * y)) :
    Real.cos (x * t) * (∏ i, Real.cos (b i * t)) ≤
      max (Real.cos (x * t)) 0 * Real.exp (-u * t ^ 2 / 2) := by
  have harg (i : Fin m) : b i * t ≤ Real.pi / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * y by positivity)).mp htR
    nlinarith [mul_le_mul_of_nonneg_right (hby i) ht]
  have hc0 (i : Fin m) : 0 ≤ Real.cos (b i * t) :=
    cos_nonneg_first_quadrant (mul_nonneg (hb0 i) ht) (harg i)
  have hp : ∏ i, Real.cos (b i * t) ≤ Real.exp (-u * t ^ 2 / 2) := by
    calc
      _ ≤ ∏ i, Real.exp (-((b i * t) ^ 2) / 2) :=
        Finset.prod_le_prod₀ (fun i _ => hc0 i)
          (fun i _ => cos_le_gaussian (mul_nonneg (hb0 i) ht) (harg i))
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        calc
          _ = ∑ i, b i ^ 2 * (-(t ^ 2) / 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [← Finset.sum_mul, hsum]; ring
  exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg (fun i _ => hc0 i))).trans
    (mul_le_mul_of_nonneg_left hp (le_max_right _ _))

end Szarek
