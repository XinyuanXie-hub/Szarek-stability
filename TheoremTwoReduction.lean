import MomentBounds
import CaseAlgebra
import FangWang
import GammaSpecial
import Reductions

open scoped BigOperators
namespace Szarek

lemma first_eq_one_of_second_zero {n : ℕ} {a : Fin (n + 2) → ℝ}
    (ha : orderedUnit a) (hz : a 1 = 0) : a 0 = 1 := by
  have htail : ∀ i : Fin (n + 1), a i.succ = 0 := by
    intro i
    apply le_antisymm
    · have h := ha.1 (show (1 : Fin (n + 2)) ≤ i.succ by
        simp [Fin.le_def])
      simpa [hz] using h
    · exact ha.2.1 _
  have hu := ha.2.2
  rw [Fin.sum_univ_succ] at hu
  have hsq : a 0 ^ 2 = 1 := by simpa only [htail, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero, add_zero] using hu
  nlinarith [ha.2.1 0]

/-- Complete finite/algebraic reduction of Theorem 2's bounds to its analytic inputs.
All analytic statements remain explicit hypotheses until independently proved. -/
theorem theorem2_bounds_of_analytic_estimates
    (hmean : ∀ (n : ℕ) (a : Fin n → ℝ), orderedUnit a →
      haagerupF (1 / (∑ i, a i ^ 4)) ≤ rademacherMean a)
    (hmono : MonotoneOn haagerupF (Set.Ioi 0))
    (hchord : ∀ t : ℝ, 0 < t → t ≤ 1 → haagerupF (4 / t ^ 2) ≤
      (1 - t ^ 2) * Real.sqrt (2 / Real.pi) + (3 : ℝ) / 4 * t ^ 2)
    (hsmall : ∀ (n : ℕ) (a : Fin (n + 2) → ℝ), orderedUnit a →
      0 < a 1 → a 0 ^ 2 + 3 * a 1 ^ 2 ≤ 1 →
      Real.sqrt (2 / Real.pi) *
        (1 - (7 : ℝ) / 20 * (a 1 ^ 2 / Real.sqrt (1 - a 0 ^ 2))) ≤ rademacherMean a)
    (hscalar : ∀ s : ℝ, 4 ≤ s → (19 : ℝ) / 24 - 1 / (6 * s) ≤ haagerupF s)
    (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : orderedUnit a) (ht : topTwo a ≤ 1) :
    haagerupF (4 / topTwo a ^ 2) ≤ rademacherMean a ∧
      (3 : ℝ) / 4 + (1 - topTwo a ^ 2) / 24 ≤ haagerupF (4 / topTwo a ^ 2) := by
  refine ⟨?_, second_inequality_of_scalar_bound hscalar hn ha ht⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have htpos := topTwo_pos (by omega) ha
  have hxy : a 1 ≤ a 0 := ha.1 (Fin.zero_le 1)
  by_cases hy : a 1 = 0
  · have hx := first_eq_one_of_second_zero ha hy
    have hsum : topTwo a = 1 := by rw [topTwo_eq, hx, hy]; ring
    rw [hsum]
    norm_num only [one_pow, div_one]
    rw [haagerupF_four]
    have he := head_le_rademacherMean a
    rw [hx] at he
    linarith
  · have hypos : 0 < a 1 := lt_of_le_of_ne (ha.2.1 1) (Ne.symm hy)
    by_cases hc : a 0 ^ 4 + (1 - a 0 ^ 2) * a 1 ^ 2 ≤ (a 0 + a 1) ^ 2 / 4
    · exact easy_case_of_analytic_bounds ha hc (hmean _ _ ha) hmono
    · have hf : (a 0 + a 1) ^ 2 < 4 * (a 0 ^ 4 + (1 - a 0 ^ 2) * a 1 ^ 2) := by linarith
      have ht' : a 0 + a 1 ≤ 1 := by simpa [topTwo_eq] using ht
      have hsep := coefficient_separation (a 0) (a 1) hypos hxy ht' hf
      have hch := hchord (topTwo a) htpos ht
      rw [topTwo_eq] at hch ⊢
      exact hard_case_of_analytic_bounds _ _ _ hypos hxy ht' hf
        (hsmall m a ha hypos hsep.2) hch

end Szarek
