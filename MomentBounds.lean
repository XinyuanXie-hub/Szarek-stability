import Geometry
import Mathlib.Tactic

open scoped BigOperators
namespace Szarek

lemma fourthMoment_pos {n : ℕ} {a : Fin n → ℝ} (ha : orderedUnit a) :
    0 < ∑ i, a i ^ 4 := by
  by_contra h
  have hn : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have he : ∑ i, a i ^ 4 = 0 := le_antisymm (le_of_not_gt h) hn
  have hall : ∀ i, a i = 0 := by
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => show 0 ≤ a j ^ 4 by positivity)).mp he i (Finset.mem_univ i)
    exact (pow_eq_zero_iff (by norm_num)).mp hi
  have hu := ha.2.2
  simp [hall] at hu

lemma fourthMoment_le {n : ℕ} {a : Fin (n + 2) → ℝ} (ha : orderedUnit a) :
    (∑ i, a i ^ 4) ≤ a 0 ^ 4 + (1 - a 0 ^ 2) * a 1 ^ 2 := by
  have hu := ha.2.2
  rw [Fin.sum_univ_succ] at hu ⊢
  have htail : (∑ i : Fin (n + 1), a i.succ ^ 4) ≤
      (∑ i : Fin (n + 1), a i.succ ^ 2) * a 1 ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hle : a i.succ ≤ a 1 := ha.1 (by simp [Fin.le_def])
    have hnon := ha.2.1 i.succ
    have hs : a i.succ ^ 2 ≤ a 1 ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (a i.succ))
    nlinarith only [hm]
  nlinarith only [htail, hu]

/-- The fourth-moment case, conditional on Haagerup's bound and monotonicity. -/
theorem easy_case_of_analytic_bounds {n : ℕ} {a : Fin (n + 2) → ℝ}
    (ha : orderedUnit a)
    (hcase : a 0 ^ 4 + (1 - a 0 ^ 2) * a 1 ^ 2 ≤ (a 0 + a 1) ^ 2 / 4)
    (hmean : haagerupF (1 / (∑ i, a i ^ 4)) ≤ rademacherMean a)
    (hmono : MonotoneOn haagerupF (Set.Ioi 0)) :
    haagerupF (4 / topTwo a ^ 2) ≤ rademacherMean a := by
  have hs := fourthMoment_pos ha
  have ht := topTwo_pos (by omega) ha
  have ht2 : 0 < topTwo a ^ 2 := sq_pos_of_pos ht
  have hmoment : (∑ i, a i ^ 4) ≤ topTwo a ^ 2 / 4 := by
    rw [topTwo_eq]
    exact (fourthMoment_le ha).trans hcase
  have hpos1 : 4 / topTwo a ^ 2 ∈ Set.Ioi (0 : ℝ) := by
    simpa only [Set.mem_Ioi] using div_pos (by norm_num : (0 : ℝ) < 4) ht2
  have hpos2 : 1 / (∑ i, a i ^ 4) ∈ Set.Ioi (0 : ℝ) := by
    simpa only [Set.mem_Ioi] using div_pos (by norm_num : (0 : ℝ) < 1) hs
  apply le_trans (hmono hpos1 hpos2 ?_) hmean
  apply (div_le_div_iff₀ ht2 hs).mpr
  linarith only [hmoment]

end Szarek
