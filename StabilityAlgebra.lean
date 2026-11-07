import Definitions
import SharpConstant

namespace Szarek

/-- The scalar algebra needed to deduce the small-top-two range of Theorem 1
from the elementary lower bound in Theorem 2. -/
theorem stability_scalar_small (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / Real.sqrt 2 + bestConstant * Real.sqrt (2 - Real.sqrt 2 * t) ≤
      (3 : ℝ) / 4 + (1 - t ^ 2) / 24 := by
  let r := Real.sqrt 2
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr_bound : r < 17 / 12 := by nlinarith
  have hr3 : r ^ 3 = 2 * r := by nlinarith [hr2]
  have hr4 : r ^ 4 = 4 := by nlinarith [sq_nonneg (r ^ 2 - 2)]
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht3 : t ^ 3 ≤ t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht2)]
  have hqarg : 0 ≤ 2 - r * t := by nlinarith
  have hq2 := Real.sq_sqrt hqarg
  have hq0 := Real.sqrt_nonneg (2 - r * t)
  have hc : bestConstant = SzarekSharpConstant.c := SzarekSharpConstant.rpow_eq_c
  have hc0 : 0 ≤ bestConstant := by rw [hc]; exact le_of_lt SzarekSharpConstant.c_pos
  have hcsq : bestConstant ^ 2 = (2 - r) ^ 3 / 64 := by
    rw [hc]
    unfold SzarekSharpConstant.c
    change ((2 - r) * Real.sqrt (2 - r) / 8) ^ 2 = _
    calc
      _ = (2 - r) ^ 2 * (Real.sqrt (2 - r)) ^ 2 / 64 := by ring
      _ = _ := by rw [Real.sq_sqrt (by linarith : 0 ≤ 2 - r)]; ring
  have hpol : 0 ≤ 289 - 204 * r + (37 - 24 * r) * t - t ^ 2 - t ^ 3 := by
    have h := mul_nonneg ht (show 0 ≤ 37 - 24 * r - 3 by linarith)
    nlinarith
  have hid : (19 - t ^ 2 - 12 * r) ^ 2 - 9 * (2 - r) ^ 3 * (2 - r * t) =
      (1 - t) * (289 - 204 * r + (37 - 24 * r) * t - t ^ 2 - t ^ 3) := by
    ring_nf
    rw [hr4, hr3, hr2]
    ring
  have hgap : 0 ≤ (19 - t ^ 2 - 12 * r) ^ 2 -
      9 * (2 - r) ^ 3 * (2 - r * t) := by
    rw [hid]
    exact mul_nonneg (sub_nonneg.mpr ht1) hpol
  have hleft : 0 ≤ 19 - t ^ 2 - 12 * r := by nlinarith
  have hprod : (24 * bestConstant * Real.sqrt (2 - r * t)) ^ 2 =
      9 * (2 - r) ^ 3 * (2 - r * t) := by
    calc
      _ = 576 * bestConstant ^ 2 * (Real.sqrt (2 - r * t)) ^ 2 := by ring
      _ = _ := by rw [hcsq, hq2]; ring
  have hpos : 0 ≤ 24 * bestConstant * Real.sqrt (2 - r * t) := by positivity
  have hle : 24 * bestConstant * Real.sqrt (2 - r * t) ≤ 19 - t ^ 2 - 12 * r := by
    nlinarith only [hgap, hprod, hpos, hleft]
  have hinv : 1 / Real.sqrt 2 = r / 2 := by
    apply (div_eq_iff (ne_of_gt hr0)).mpr
    change 1 = r / 2 * r
    nlinarith only [hr2]
  rw [hinv]
  change r / 2 + bestConstant * Real.sqrt (2 - r * t) ≤ _
  linarith only [hle]

end Szarek
