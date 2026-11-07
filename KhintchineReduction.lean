import FangWang
import EqualSigns

open scoped BigOperators
noncomputable section
namespace Szarek

lemma rademacherMean_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ rademacherMean a := by
  unfold rademacherMean
  positivity

lemma rademacherMean_le_cons {n : ℕ} (x : ℝ) (a : Fin n → ℝ) :
    rademacherMean a ≤ rademacherMean (Fin.cons x a) := by
  rw [rademacherMean_cons]
  have hpoint (s : ℝ) : 2 * |s| ≤ |x + s| + |-x + s| := by
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs]
      linarith [le_abs_self (x + s), le_abs_self (-x + s)]
    · rw [abs_of_nonpos hs]
      linarith [neg_le_abs (x + s), neg_le_abs (-x + s)]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (ε : Fin n → Bool) _ => hpoint (signLinear a ε))
  rw [← Finset.mul_sum] at h
  unfold rademacherMean
  change (∑ ε, |signLinear a ε|) / (2 : ℝ) ^ n ≤ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 2 ^ n by positivity)]

lemma abs_coordinate_le_rademacherMean {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    |a i| ≤ rademacherMean a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact abs_head_le_rademacherMean a
    · have h := (ih (Fin.tail a) j).trans (rademacherMean_le_cons (a 0) (Fin.tail a))
      simpa [Fin.tail] using h

/-- Sharp unit-vector Khintchine from the weighted Haagerup bound and monotonicity.
Both analytic results are explicit hypotheses, not new axioms. -/
lemma unit_khintchine_of_haagerup
    (hweighted : ∀ (n : ℕ) (a : Fin n → ℝ), (∑ i, (a i) ^ 2) = 1 →
      (∑ i, (a i) ^ 2 * haagerupF (1 / (a i) ^ 2)) ≤ rademacherMean a)
    (hmono : MonotoneOn haagerupF (Set.Ioi 0))
    {n : ℕ} (a : Fin n → ℝ) (hu : ∑ i, (a i) ^ 2 = 1) :
    1 / Real.sqrt 2 ≤ rademacherMean a := by
  by_cases hex : ∃ i, 1 / Real.sqrt 2 ≤ |a i|
  · obtain ⟨i, hi⟩ := hex
    exact hi.trans (abs_coordinate_le_rademacherMean a i)
  · push Not at hex
    have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hr2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
      apply (div_eq_iff (ne_of_gt hr0)).mpr
      nlinarith
    have hterm (i : Fin n) :
        (a i) ^ 2 * (1 / Real.sqrt 2) ≤ (a i) ^ 2 * haagerupF (1 / (a i) ^ 2) := by
      by_cases hi : a i = 0
      · simp [hi]
      · have hpos : 0 < (a i) ^ 2 := sq_pos_of_ne_zero hi
        have habs := hex i
        rw [hinv] at habs
        have hsmall : (a i) ^ 2 < 1 / 2 := by
          nlinarith [sq_abs (a i), abs_nonneg (a i)]
        have harg : 2 ≤ 1 / (a i) ^ 2 := by
          apply (le_div_iff₀ hpos).mpr
          linarith
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [← haagerupF_two]
        exact hmono (by norm_num) (show 0 < 1 / (a i) ^ 2 by positivity) harg
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
    rw [← Finset.sum_mul, hu, one_mul] at hsum
    exact hsum.trans (hweighted n a hu)

lemma khintchine_of_haagerup
    (hweighted : ∀ (n : ℕ) (a : Fin n → ℝ), (∑ i, (a i) ^ 2) = 1 →
      (∑ i, (a i) ^ 2 * haagerupF (1 / (a i) ^ 2)) ≤ rademacherMean a)
    (hmono : MonotoneOn haagerupF (Set.Ioi 0))
    (n : ℕ) (a : Fin n → ℝ) :
    Real.sqrt (∑ i, (a i) ^ 2) / Real.sqrt 2 ≤ rademacherMean a := by
  let s := Real.sqrt (∑ i, (a i) ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ∑ i, (a i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  by_cases hs : s = 0
  · change s / Real.sqrt 2 ≤ _
    rw [hs, zero_div]
    exact rademacherMean_nonneg a
  · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hu : (∑ i, (a i / s) ^ 2) = 1 := by
      simp_rw [div_pow, ← Finset.sum_div]
      rw [← hs2, div_self (pow_ne_zero _ hs)]
    have h := unit_khintchine_of_haagerup hweighted hmono (fun i => a i / s) hu
    have he : rademacherMean (fun i => a i / s) = rademacherMean a / s := by
      have hscale := rademacherMean_scale a (1 / s)
      simpa [div_eq_mul_inv, mul_comm, abs_of_pos (inv_pos.mpr hsp)] using hscale
    rw [he] at h
    have hm := (le_div_iff₀ hsp).mp h
    change s / Real.sqrt 2 ≤ _
    simpa [div_eq_mul_inv, mul_comm] using hm

#print axioms Szarek.khintchine_of_haagerup
#print axioms Szarek.abs_coordinate_le_rademacherMean
end Szarek
