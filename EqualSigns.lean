import Definitions
import BinomialAbs
import PaddedSharpness
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators
noncomputable section
namespace Szarek

/-- Boolean sign vectors identified with their positive-coordinate sets. -/
def signsFinsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun ε := Finset.univ.filter (fun i => ε i = true)
  invFun s := fun i => decide (i ∈ s)
  left_inv ε := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases ε i <;> rfl
  right_inv s := by
    ext i
    simp

lemma signs_sum_of_set {n : ℕ} (s : Finset (Fin n)) :
    (∑ i : Fin n, (if i ∈ s then (1 : ℝ) else -1)) = 2 * s.card - n := by
  calc
    _ = ∑ i : Fin n, (2 * (if i ∈ s then (1 : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> norm_num
    _ = _ := by
      simp [Finset.sum_sub_distrib, mul_comm]

lemma sum_over_signs_eq_choose (n : ℕ) (f : ℝ → ℝ) :
    (∑ ε : Fin n → Bool, f (∑ i : Fin n, if ε i then (1 : ℝ) else -1)) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f (2 * k - n) := by
  classical
  calc
    _ = ∑ s : Finset (Fin n), f (2 * s.card - n) := by
      apply Fintype.sum_equiv (signsFinsetEquiv n)
      intro ε
      have hs := signs_sum_of_set ((signsFinsetEquiv n) ε)
      simpa [signsFinsetEquiv] using congrArg f hs
    _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, f (2 * s.card - n) := by
      simp
    _ = _ := by
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro k hk
      simpa only [nsmul_eq_mul, Nat.cast_id, Finset.card_univ, Fintype.card_fin] using
        Finset.sum_powersetCard k (Finset.univ : Finset (Fin n))
          (fun k => f (2 * k - n))

lemma rademacherMean_const_one (n : ℕ) :
    rademacherMean (fun _ : Fin n => (1 : ℝ)) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * |(n : ℝ) - 2 * k|) /
        (2 : ℝ) ^ n := by
  unfold rademacherMean
  simp only [one_mul]
  rw [sum_over_signs_eq_choose]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [abs_sub_comm]

lemma rademacherMean_scale {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    rademacherMean (fun i => c * a i) = |c| * rademacherMean a := by
  unfold rademacherMean
  simp_rw [mul_assoc, ← Finset.mul_sum, abs_mul, ← Finset.mul_sum]
  ring

lemma rademacherMean_evenEqual_base_scale (m : ℕ) :
    rademacherMean (evenEqual (2 * m) m) =
      rademacherMean (fun _ : Fin (2 * m) => (1 : ℝ)) / Real.sqrt (2 * (m : ℝ)) := by
  have hfun : evenEqual (2 * m) m =
      fun i : Fin (2 * m) => (1 / Real.sqrt (2 * (m : ℝ))) * (1 : ℝ) := by
    funext i
    simp [evenEqual, i.isLt]
  rw [hfun, rademacherMean_scale, abs_of_nonneg (by positivity)]
  ring

lemma rademacherMean_const_one_even (m : ℕ) :
    rademacherMean (fun _ : Fin (2 * m) => (1 : ℝ)) =
      (2 * (m : ℝ)) * ((2 * m).choose m : ℝ) / (2 : ℝ) ^ (2 * m) := by
  rw [rademacherMean_const_one]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [binomial_abs_even]

lemma rademacherMean_evenEqual_base (m : ℕ) (hm : 1 ≤ m) :
    rademacherMean (evenEqual (2 * m) m) =
      Real.sqrt (2 * (m : ℝ)) * ((2 * m).choose m : ℝ) / (2 : ℝ) ^ (2 * m) := by
  rw [rademacherMean_evenEqual_base_scale, rademacherMean_const_one_even]
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hs : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * (m : ℝ) by positivity)
  apply (div_eq_iff (ne_of_gt hs)).mpr
  rw [div_mul_eq_mul_div]
  congr 1
  nlinarith only [hs2]

#print axioms Szarek.rademacherMean_evenEqual_base
end Szarek
