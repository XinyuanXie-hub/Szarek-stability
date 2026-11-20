module

public import PaddedSharpness
public import Geometry

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Szarek

lemma evenEqual_succ {n m : ℕ} (hn : 2 * m ≤ n) :
    evenEqual (n + 1) m = Fin.snoc (evenEqual n m) 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [evenEqual, Nat.not_lt.mpr hn]
  · simp [evenEqual]

lemma evenEqual_mean_padding {n m : ℕ} (hn : 2 * m ≤ n) :
    rademacherMean (evenEqual n m) = rademacherMean (evenEqual (2 * m) m) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [evenEqual_succ hn, rademacherMean_snoc_zero, ih]

lemma evenEqual_unit {n m : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n) :
    orderedUnit (evenEqual n m) := by
  have hmpos : 0 < (2 : ℝ) * m := by positivity
  have hs : (Real.sqrt (2 * (m : ℝ))) ^ 2 = 2 * (m : ℝ) := Real.sq_sqrt hmpos.le
  have hsp : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.mpr hmpos
  have hsum : ∑ i, (evenEqual n m i) ^ 2 = 1 := by
    induction n, hn using Nat.le_induction with
    | base =>
      simp only [evenEqual, Fin.is_lt, ite_true]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_ofNat]
      rw [div_pow, one_pow, hs]
      calc
        _ = (2 * (m : ℝ)) / (2 * (m : ℝ)) := by ring
        _ = 1 := div_self (ne_of_gt hmpos)
    | succ n hn ih =>
      rw [evenEqual_succ hn]
      simpa [Fin.sum_univ_castSucc] using ih
  refine ⟨?_, ?_, hsum⟩
  · intro i j hij
    simp only [evenEqual]
    split_ifs with hj hi
    · rfl
    · have : i.val < 2 * m := lt_of_le_of_lt hij hj
      contradiction
    · positivity
    · rfl
  · intro i
    simp only [evenEqual]
    split_ifs <;> positivity

lemma evenEqual_topTwo {n m : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n) :
    topTwo (evenEqual n m) = 2 / Real.sqrt (2 * (m : ℝ)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [topTwo_eq]
  simp only [evenEqual, Fin.val_zero, Fin.val_one,
    show 0 < 2 * m by omega, show 1 < 2 * m by omega, ite_true]
  ring

lemma evenEqual_topTwo_le_one {n m : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n) :
    topTwo (evenEqual n m) ≤ 1 := by
  rw [evenEqual_topTwo hm hn]
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * m by positivity)
  have hsp : 0 < Real.sqrt (2 * (m : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_one hsp).mpr
  nlinarith [Real.sqrt_nonneg (2 * (m : ℝ))]

lemma evenEqual_argument {n m : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n) :
    4 / (topTwo (evenEqual n m)) ^ 2 = 2 * (m : ℝ) := by
  rw [evenEqual_topTwo hm hn, div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  norm_num

#print axioms Szarek.evenEqual_unit
#print axioms Szarek.evenEqual_argument
end Szarek
