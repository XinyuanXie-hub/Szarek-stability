import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SzarekSharpConstant

noncomputable def c : ℝ := (2 - Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) / 8

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

lemma c_pos : 0 < c := by
  unfold c
  have h : 0 < 2 - Real.sqrt 2 := sub_pos.mpr sqrt_two_lt_two
  exact div_pos (mul_pos h (Real.sqrt_pos.mpr h)) (by norm_num)

lemma equality_identity : 1 / Real.sqrt 2 + c * Real.sqrt (2 - Real.sqrt 2) = 3 / 4 := by
  have ht : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 - Real.sqrt 2 by linarith [sqrt_two_lt_two])
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt ht)).mpr
    nlinarith
  rw [hinv]
  unfold c
  have hp : (2 - Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) / 8 *
      Real.sqrt (2 - Real.sqrt 2) = (2 - Real.sqrt 2) ^ 2 / 8 := by
    calc
      _ = (2 - Real.sqrt 2) * (Real.sqrt (2 - Real.sqrt 2) ^ 2) / 8 := by ring
      _ = _ := by rw [hs2]; ring
  rw [hp]
  nlinarith

lemma rpow_eq_c : (2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8 = c := by
  have h : 0 < 2 - Real.sqrt 2 := sub_pos.mpr sqrt_two_lt_two
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add h,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  rfl

lemma coefficient_le {k : ℝ}
    (h : 1 / Real.sqrt 2 + k * Real.sqrt (2 - Real.sqrt 2) ≤ 3 / 4) :
    k ≤ c := by
  have hs : 0 < Real.sqrt (2 - Real.sqrt 2) :=
    Real.sqrt_pos.mpr (sub_pos.mpr sqrt_two_lt_two)
  have he := equality_identity
  nlinarith

end SzarekSharpConstant
