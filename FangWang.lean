import Geometry
import FiniteSharpness
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open scoped BigOperators
noncomputable section
namespace Szarek

/-- The signed linear form on a finite Boolean cube. -/
def signLinear {n : ℕ} (a : Fin n → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ i, a i * (if ε i then 1 else -1)

lemma rademacherMean_cons {n : ℕ} (x : ℝ) (a : Fin n → ℝ) :
    rademacherMean (Fin.cons x a) =
      (∑ ε, (|x + signLinear a ε| + |-x + signLinear a ε|)) / (2 : ℝ) ^ (n + 1) := by
  simp [rademacherMean, signLinear, sum_signs_succ, Fin.sum_univ_succ,
    Finset.sum_add_distrib]

lemma rademacherMean_cons_cons {n : ℕ} (x y : ℝ) (a : Fin n → ℝ) :
    rademacherMean (Fin.cons x (Fin.cons y a)) =
      (∑ ε, (|x + y + signLinear a ε| + |x - y + signLinear a ε| +
        |-x + y + signLinear a ε| + |-x - y + signLinear a ε|)) /
        (2 : ℝ) ^ (n + 2) := by
  simp [rademacherMean, signLinear, sum_signs_succ, Fin.sum_univ_succ,
    Finset.sum_add_distrib, add_assoc, sub_eq_add_neg]
  ring

lemma abs_pair_ge (x y s : ℝ) :
    2 * (x + y) + (|x - y + s| + |-(x - y) + s|) ≤
      |x + y + s| + |x - y + s| + |-x + y + s| + |-x - y + s| := by
  have h₁ := le_abs_self (x + y + s)
  have h₂ := neg_le_abs (-x - y + s)
  have he : -(x - y) = -x + y := by ring
  rw [he]
  linarith

/-- The finite conditioning reduction underlying Fang--Wang's four-coordinate bound. -/
lemma first_two_merge_bound {n : ℕ} (x y : ℝ) (a : Fin n → ℝ) :
    (x + y + rademacherMean (Fin.cons (x - y) a)) / 2 ≤
      rademacherMean (Fin.cons x (Fin.cons y a)) := by
  rw [rademacherMean_cons, rademacherMean_cons_cons]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun (ε : Fin n → Bool) _ => abs_pair_ge x y (signLinear a ε))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hp : 0 < (2 : ℝ) ^ n := by positivity
  rw [pow_add, pow_add]
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ n * 4)).mpr
  field_simp
  simp only [neg_sub, Finset.sum_add_distrib] at *
  nlinarith

lemma abs_pair_ge_abs (x s : ℝ) :
    2 * |x| ≤ |x + s| + |-x + s| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [le_abs_self (x + s), neg_le_abs (-x + s)]
  · rw [abs_of_nonpos hx]
    linarith [neg_le_abs (x + s), le_abs_self (-x + s)]

lemma abs_head_le_rademacherMean_cons {n : ℕ} (x : ℝ) (a : Fin n → ℝ) :
    |x| ≤ rademacherMean (Fin.cons x a) := by
  rw [rademacherMean_cons]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (ε : Fin n → Bool) _ => abs_pair_ge_abs x (signLinear a ε))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat] at h
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n + 1))).mpr
  rw [pow_succ]
  nlinarith

lemma abs_head_le_rademacherMean {n : ℕ} (a : Fin (n + 1) → ℝ) :
    |a 0| ≤ rademacherMean a := by
  have h := abs_head_le_rademacherMean_cons (a 0) (Fin.tail a)
  simpa using h

lemma head_le_rademacherMean {n : ℕ} (a : Fin (n + 1) → ℝ) :
    a 0 ≤ rademacherMean a :=
  (le_abs_self _).trans (abs_head_le_rademacherMean a)

/-- A precise reduction of the large-coordinate branch to sharp Khintchine
for the merged vector. The hypothesis `hk` remains a genuine proof obligation. -/
lemma first_two_bound_of_merged_khintchine {n : ℕ} (x y : ℝ) (a : Fin n → ℝ)
    (hu : x ^ 2 + y ^ 2 + ∑ i, (a i) ^ 2 = 1)
    (hk : Real.sqrt ((x - y) ^ 2 + ∑ i, (a i) ^ 2) / Real.sqrt 2 ≤
      rademacherMean (Fin.cons (x - y) a)) :
    (x + y) / 2 + Real.sqrt (2 - (x + y) ^ 2) / 4 ≤
      rademacherMean (Fin.cons x (Fin.cons y a)) := by
  let t := (x - y) ^ 2 + ∑ i, (a i) ^ 2
  have ht : 0 ≤ t := add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hcomp : 2 - (x + y) ^ 2 ≤ 2 * t := by
    dsimp [t]
    nlinarith [sq_nonneg (x - y)]
  have hroot := Real.sqrt_le_sqrt hcomp
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hroot
  have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hroot hrp.le
  have hrhs : Real.sqrt 2 * Real.sqrt t * Real.sqrt 2 = 2 * Real.sqrt t := by
    calc
      _ = (Real.sqrt 2) ^ 2 * Real.sqrt t := by ring
      _ = _ := by rw [hr]
  rw [hrhs] at hmul
  have hs : Real.sqrt (2 - (x + y) ^ 2) / 4 ≤
      (Real.sqrt t / Real.sqrt 2) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (le_div_iff₀ hrp).mpr
    nlinarith
  have hb := first_two_merge_bound x y a
  change Real.sqrt t / Real.sqrt 2 ≤ _ at hk
  linarith

lemma large_profile_scalar {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ Real.sqrt (2 - Real.sqrt 2)) :
    1 / Real.sqrt 2 + bestConstant * t ≤
      1 / Real.sqrt 2 + (Real.sqrt (1 - t ^ 2 / 4) - t) * t / (2 * Real.sqrt 2) := by
  let r := Real.sqrt 2
  let s := Real.sqrt (2 - Real.sqrt 2)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrlt : r < 2 := SzarekSharpConstant.sqrt_two_lt_two
  have hs0 : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr SzarekSharpConstant.sqrt_two_lt_two)
  have hs2 : s ^ 2 = 2 - r := Real.sq_sqrt (by linarith)
  have hr3 : r ^ 3 = 2 * r := by
    calc
      _ = r * r ^ 2 := by ring
      _ = _ := by rw [hr2]; ring
  have he2 : (((r + 1) * s) / 2) ^ 2 = 1 - (2 - r) / 4 := by
    rw [div_pow, mul_pow, hs2]
    ring_nf
    rw [hr3]
    ring
  have hepos : 0 ≤ ((r + 1) * s) / 2 := by positivity
  have hbase : 0 ≤ 1 - (2 - r) / 4 := by linarith
  have he : Real.sqrt (1 - (2 - r) / 4) = ((r + 1) * s) / 2 := by
    have hsqrt := Real.sq_sqrt hbase
    have hsqrt0 := Real.sqrt_nonneg (1 - (2 - r) / 4)
    nlinarith
  have ht2 : t ^ 2 ≤ 2 - r := by
    change t ≤ s at ht
    nlinarith
  have hroot := Real.sqrt_le_sqrt (show 1 - (2 - r) / 4 ≤ 1 - t ^ 2 / 4 by linarith)
  rw [he] at hroot
  have hc : bestConstant = (2 - r) * s / 8 := by
    rw [bestConstant, SzarekSharpConstant.rpow_eq_c]
    rfl
  have hcoef : 2 * r * bestConstant ≤ Real.sqrt (1 - t ^ 2 / 4) - t := by
    rw [hc]
    have hrs : r ^ 2 * s = 2 * s := by rw [hr2]
    change t ≤ s at ht
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef ht0
  have hden : 0 < 2 * Real.sqrt 2 := by positivity
  have hd : bestConstant * t ≤
      (Real.sqrt (1 - t ^ 2 / 4) - t) * t / (2 * Real.sqrt 2) := by
    apply (le_div_iff₀ hden).mpr
    change _ ≤ _ at hmul
    dsimp [r] at hmul
    nlinarith
  linarith

lemma large_sum_scalar {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ Real.sqrt 2) :
    1 / Real.sqrt 2 + bestConstant * Real.sqrt (2 - Real.sqrt 2 * q) ≤
      q / 2 + Real.sqrt (2 - q ^ 2) / 4 := by
  let r := Real.sqrt 2
  let t := Real.sqrt (2 - r * q)
  let v := Real.sqrt (1 - t ^ 2 / 4)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdelta : 0 ≤ 2 - r * q := by nlinarith
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 - r * q := Real.sq_sqrt hdelta
  have htle : t ≤ Real.sqrt (2 - Real.sqrt 2) := by
    apply Real.sqrt_le_sqrt
    change 2 - r * q ≤ 2 - r
    nlinarith
  have hvbase : 0 ≤ 1 - t ^ 2 / 4 := by nlinarith
  have hv2 : v ^ 2 = 1 - t ^ 2 / 4 := Real.sq_sqrt hvbase
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hid : (r * t * v) ^ 2 = 2 - q ^ 2 := by
    rw [mul_pow, mul_pow, hr2, hv2, ht2]
    ring_nf
    rw [hr2]
    ring
  have hu : Real.sqrt (2 - q ^ 2) = r * t * v := by
    rw [← hid, Real.sqrt_sq (by positivity)]
  have hprof := large_profile_scalar ht0 htle
  change 1 / r + bestConstant * t ≤ 1 / r + (v - t) * t / (2 * r) at hprof
  have he : q / 2 + (r * t * v) / 4 = 1 / r + (v - t) * t / (2 * r) := by
    field_simp
    nlinarith [show r ^ 2 * (t * v) = 2 * (t * v) by rw [hr2]]
  rw [hu, he]
  exact hprof

lemma topTwo_le_sqrt_two {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ}
    (ha : orderedUnit a) : topTwo a ≤ Real.sqrt 2 := by
  have hsum : 0 ≤ ∑ i, (a i - if i.val < 2 then 1 / Real.sqrt 2 else 0) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [distance_sq_identity hn ha] at hsum
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- Conditional assembly of the complete large-top-two branch. Its single
external input is the explicitly quantified sharp Khintchine inequality. -/
lemma stability_large_of_khintchine
    (hk : ∀ (k : ℕ) (b : Fin k → ℝ),
      Real.sqrt (∑ i, (b i) ^ 2) / Real.sqrt 2 ≤ rademacherMean b)
    {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ} (ha : orderedUnit a)
    (hlarge : 1 ≤ topTwo a) :
    1 / Real.sqrt 2 + bestConstant * extremizerDistance a ≤ rademacherMean a := by
  have hupper := topTwo_le_sqrt_two hn ha
  have hscalar := large_sum_scalar hlarge hupper
  rw [← extremizerDistance_identity hn ha] at hscalar
  apply hscalar.trans
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let tail : Fin m → ℝ := fun i => a i.succ.succ
  have hu : (a 0) ^ 2 + (a 1) ^ 2 + ∑ i, (tail i) ^ 2 = 1 := by
    have h := ha.2.2
    simpa [Fin.sum_univ_succ, Fin.succ_zero_eq_one, tail, add_assoc] using h
  have hk' := hk (m + 1) (Fin.cons (a 0 - a 1) tail)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hk'
  have hb := first_two_bound_of_merged_khintchine (a 0) (a 1) tail hu hk'
  have he : Fin.cons (a 0) (Fin.cons (a 1) tail) = a := by
    calc
      _ = Fin.cons (a 0) (Fin.tail a) := by
        congr 1
        exact Fin.cons_self_tail (Fin.tail a)
      _ = a := Fin.cons_self_tail a
  rw [he] at hb
  simpa [topTwo_eq] using hb

lemma haagerupF_two : haagerupF 2 = 1 / Real.sqrt 2 := by
  have hhalf : Real.Gamma ((3 : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
    have h := Real.Gamma_add_one (s := (1 : ℝ) / 2) (by norm_num)
    norm_num [Real.Gamma_one_half_eq] at h
    linarith
  have hpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  unfold haagerupF
  norm_num [hhalf, Real.Gamma_one, Real.sqrt_mul Real.pi_pos.le]
  field_simp [hpi]

#print axioms Szarek.haagerupF_two
#print axioms Szarek.stability_large_of_khintchine
#print axioms Szarek.large_sum_scalar
#print axioms Szarek.large_profile_scalar
#print axioms Szarek.first_two_bound_of_merged_khintchine
#print axioms Szarek.head_le_rademacherMean
#print axioms Szarek.first_two_merge_bound
end Szarek
