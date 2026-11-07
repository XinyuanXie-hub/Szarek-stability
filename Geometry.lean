import Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
noncomputable section
namespace Szarek

lemma topTwo_eq {n : ℕ} (a : Fin (n + 2) → ℝ) : topTwo a = a 0 + a 1 := by
  simp [topTwo, Finset.sum_filter, Fin.sum_univ_succ]

lemma topTwo_pos {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ} (ha : orderedUnit a) :
    0 < topTwo a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h0 : 0 < a 0 := by
    by_contra h
    have hzero : a 0 = 0 := le_antisymm (le_of_not_gt h) (ha.2.1 0)
    have hall : a = 0 := by
      funext i
      apply le_antisymm
      · simpa [hzero] using ha.1 (show (0 : Fin (m + 2)) ≤ i by exact Fin.zero_le i)
      · exact ha.2.1 i
    have hu := ha.2.2
    simp [hall] at hu
  rw [topTwo_eq]
  exact add_pos_of_pos_of_nonneg h0 (ha.2.1 1)

lemma distance_sq_identity {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ}
    (ha : orderedUnit a) :
    (∑ i, (a i - if i.val < 2 then 1 / Real.sqrt 2 else 0) ^ 2) =
      2 - Real.sqrt 2 * topTwo a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hi : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hp)).mpr
    nlinarith
  have hu := ha.2.2
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hu
  rw [topTwo_eq]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  simp only [show (0 : ℕ) < 2 by omega, show (1 : ℕ) < 2 by omega,
    show ∀ i : Fin m, ¬ (i.val + 1 + 1 < 2) by omega, ite_true, ite_false, sub_zero]
  rw [hi]
  simp only [Fin.succ_zero_eq_one] at hu ⊢
  nlinarith

lemma extremizerDistance_identity {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ}
    (ha : orderedUnit a) :
    extremizerDistance a = Real.sqrt (2 - Real.sqrt 2 * topTwo a) := by
  unfold extremizerDistance
  rw [distance_sq_identity hn ha]

#print axioms Szarek.topTwo_pos
#print axioms Szarek.extremizerDistance_identity
end Szarek
