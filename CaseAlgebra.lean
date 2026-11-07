import Definitions
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

namespace Szarek

/-- Failure of the fourth-moment case forces separation of the first two coefficients. -/
theorem coefficient_separation (x y : ℝ) (hy : 0 < y) (hxy : y ≤ x)
    (ht : x + y ≤ 1)
    (hfail : (x + y) ^ 2 < 4 * (x ^ 4 + (1 - x ^ 2) * y ^ 2)) :
    (9 : ℝ) / 5 * y < x ∧ x ^ 2 + 3 * y ^ 2 ≤ 1 := by
  have hx : 0 < x := lt_of_lt_of_le hy hxy
  have ht0 : 0 < x + y := by linarith
  have ht2 : (x + y) ^ 2 ≤ 1 := by nlinarith
  have hid : 4 * (x ^ 4 + (1 - x ^ 2) * y ^ 2) - (x + y) ^ 2 =
      (x - y) * (4 * x ^ 2 * (x + y) - x - 3 * y) := by ring
  have hprod : 0 < (x - y) * (4 * x ^ 2 * (x + y) - x - 3 * y) := by
    rw [← hid]
    linarith
  have hgap : 0 < 4 * x ^ 2 * (x + y) - x - 3 * y := by
    exact pos_of_mul_pos_right hprod (sub_nonneg.mpr hxy)
  have hmul := mul_pos hgap ht0
  have hbound := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr ht2)
  have hsep : 0 < 3 * x ^ 2 - 4 * x * y - 3 * y ^ 2 := by
    nlinarith only [hmul, hbound]
  have hratio : (9 : ℝ) / 5 * y < x := by
    by_contra h
    have hle : x ≤ (9 : ℝ) / 5 * y := le_of_not_gt h
    have hfac := mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ x + (9 : ℝ) / 5 * y by positivity)
    have hfac2 := mul_nonneg hy.le (sub_nonneg.mpr hxy)
    nlinarith only [hsep, hfac, hfac2, sq_pos_of_pos hy]
  refine ⟨hratio, ?_⟩
  have hm := mul_nonneg hy.le (show 0 ≤ x - y by linarith)
  nlinarith only [ht2, hm]

/-- The quantitative separation estimate used with paper Lemma 2. -/
theorem small_second_coefficient (x y : ℝ) (hy : 0 < y) (hxy : y ≤ x)
    (ht : x + y ≤ 1)
    (hfail : (x + y) ^ 2 < 4 * (x ^ 4 + (1 - x ^ 2) * y ^ 2)) :
    y ^ 2 / Real.sqrt (1 - x ^ 2) < (x + y) ^ 2 / 6 := by
  have hr := (coefficient_separation x y hy hxy ht hfail).1
  have hx : 0 < x := lt_of_lt_of_le hy hxy
  have ht0 : 0 < x + y := by linarith
  have ht2 : (x + y) ^ 2 ≤ 1 := by nlinarith
  have hu : 0 < 1 - x ^ 2 := by nlinarith
  have hnum : (4508 : ℝ) / 125 * y ^ 4 < y * (2 * x + y) * (x + y) ^ 2 := by
    calc
      _ = y * ((23 : ℝ) / 5 * y) * (((14 : ℝ) / 5 * y) ^ 2) := by ring
      _ < _ := by gcongr <;> linarith
  have hden : y * (2 * x + y) ≤ (1 - x ^ 2) * (x + y) ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr ht2)]
  have hden2 := mul_le_mul_of_nonneg_right hden (sq_nonneg (x + y))
  have hy4 : 0 < y ^ 4 := pow_pos hy _
  have hquart : 36 * y ^ 4 < (1 - x ^ 2) * (x + y) ^ 4 := by
    nlinarith only [hnum, hden2, hy4]
  have hs := Real.sq_sqrt hu.le
  have hs0 : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hu
  have hsq : ((x + y) ^ 2 * Real.sqrt (1 - x ^ 2)) ^ 2 =
      (x + y) ^ 4 * (1 - x ^ 2) := by rw [mul_pow, hs]; ring
  have hpos : 0 ≤ (x + y) ^ 2 * Real.sqrt (1 - x ^ 2) := by positivity
  apply (div_lt_iff₀ hs0).mpr
  nlinarith only [hquart, hsq, hpos, sq_nonneg (6 * y ^ 2 - (x + y) ^ 2 * Real.sqrt (1 - x ^ 2))]

lemma gaussian_constant_gt : (90 : ℝ) / 113 < Real.sqrt (2 / Real.pi) := by
  have hp := Real.pi_pos
  have hb := Real.pi_lt_d4
  have h : ((90 : ℝ) / 113) ^ 2 < 2 / Real.pi := by
    apply (lt_div_iff₀ hp).mpr
    nlinarith only [hb]
  have hs := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
  have hs0 := Real.sqrt_nonneg (2 / Real.pi)
  nlinarith only [h, hs, hs0]

/-- The difficult-case comparison, conditional on the two analytic bounds. -/
theorem hard_case_of_analytic_bounds (x y E : ℝ) (hy : 0 < y) (hxy : y ≤ x)
    (ht : x + y ≤ 1)
    (hfail : (x + y) ^ 2 < 4 * (x ^ 4 + (1 - x ^ 2) * y ^ 2))
    (hgauss : Real.sqrt (2 / Real.pi) *
      (1 - (7 : ℝ) / 20 * (y ^ 2 / Real.sqrt (1 - x ^ 2))) ≤ E)
    (hchord : haagerupF (4 / (x + y) ^ 2) ≤
      (1 - (x + y) ^ 2) * Real.sqrt (2 / Real.pi) + (3 : ℝ) / 4 * (x + y) ^ 2) :
    haagerupF (4 / (x + y) ^ 2) ≤ E := by
  have hb := small_second_coefficient x y hy hxy ht hfail
  have hq0 : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < x + y := by linarith
  have hq := gaussian_constant_gt
  have hstep : Real.sqrt (2 / Real.pi) * (1 - 7 / 120 * (x + y) ^ 2) <
      Real.sqrt (2 / Real.pi) * (1 - 7 / 20 * (y ^ 2 / Real.sqrt (1 - x ^ 2))) := by
    have hm := mul_pos hq0 (sub_pos.mpr hb)
    nlinarith only [hm]
  have hstep2 : (1 - (x + y) ^ 2) * Real.sqrt (2 / Real.pi) +
      3 / 4 * (x + y) ^ 2 < Real.sqrt (2 / Real.pi) * (1 - 7 / 120 * (x + y) ^ 2) := by
    have hm := mul_pos (sq_pos_of_pos ht0)
      (show 0 < 113 * Real.sqrt (2 / Real.pi) - 90 by linarith only [hq])
    nlinarith only [hm]
  exact le_trans hchord (le_trans hstep2.le (le_trans hstep.le hgauss))

end Szarek
