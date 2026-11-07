import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

open scoped BigOperators
open Finset
namespace Szarek

lemma signed_binomial_partial (n r : ℕ) (hr : r ≤ n) :
    (∑ k ∈ range (r + 1), (n.choose k : ℝ) * ((n : ℝ) - 2 * k)) =
      ((n : ℝ) - r) * (n.choose r : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrn : r ≤ n := by omega
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq n r)
    push_cast [Nat.cast_sub hrn] at h
    rw [sum_range_succ, ih hrn]
    push_cast
    nlinarith only [h]

lemma binomial_abs_even (m : ℕ) :
    (∑ k ∈ range (2 * m + 1), ((2 * m).choose k : ℝ) *
      |(2 * (m : ℝ)) - 2 * k|) =
      (2 * (m : ℝ)) * ((2 * m).choose m : ℝ) := by
  let f : ℕ → ℝ := fun k => ((2 * m).choose k : ℝ) * |2 * (m : ℝ) - 2 * k|
  have hsymm (k : ℕ) (hk : k ≤ 2 * m) : f (2 * m - k) = f k := by
    dsimp [f]
    rw [Nat.choose_symm hk, Nat.cast_sub hk]
    push_cast
    rw [show 2 * (m : ℝ) - 2 * (2 * m - k) = -(2 * m - 2 * k) by ring, abs_neg]
  have hm : f m = 0 := by simp [f]
  have hhalf : ∑ k ∈ range (m + 1), f k = (m : ℝ) * ((2 * m).choose m : ℝ) := by
    calc
      _ = ∑ k ∈ range (m + 1), ((2 * m).choose k : ℝ) * ((2 * m : ℕ) - 2 * (k : ℝ)) := by
        refine sum_congr rfl fun k hk => ?_
        have hk' : k ≤ m := by simpa using hk
        have hkreal : (k : ℝ) ≤ m := by exact_mod_cast hk'
        simp only [f, Nat.cast_mul, Nat.cast_ofNat]
        rw [abs_of_nonneg (by linarith)]
      _ = _ := by
        convert signed_binomial_partial (2 * m) m (by omega) using 1
        push_cast
        ring
  have htail : ∑ k ∈ range m, f (m + 1 + k) = ∑ k ∈ range m, f k := by
    calc
      _ = ∑ k ∈ range m, f (m - 1 - k) := by
        refine sum_congr rfl fun k hk => ?_
        have hk' : k < m := mem_range.mp hk
        have hh : 2 * m - (m + 1 + k) = m - 1 - k := by omega
        rw [← hh, hsymm _ (by omega)]
      _ = _ := sum_range_reflect f m
  change ∑ k ∈ range (2 * m + 1), f k = _
  rw [show 2 * m + 1 = (m + 1) + m by omega, sum_range_add, htail]
  have hs : ∑ k ∈ range m, f k = ∑ k ∈ range (m + 1), f k := by
    rw [sum_range_succ, hm, add_zero]
  rw [hs, hhalf]
  ring

#print axioms binomial_abs_even
end Szarek
