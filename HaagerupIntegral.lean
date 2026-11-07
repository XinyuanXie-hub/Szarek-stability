import ScalarFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries

open scoped BigOperators Topology
open Set Filter
noncomputable section
namespace Szarek

def cotPair (n : ℕ) (x : ℝ) : ℝ :=
  1 / (x - (n+1)) + 1 / (x + (n+1))

def cotPairDeriv (n : ℕ) (x : ℝ) : ℝ :=
  -(1 / (x - (n+1))^2 + 1 / (x + (n+1))^2)

lemma real_mem_integerComplement {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hr : (n : ℝ) = x := by exact_mod_cast hn
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith [hx.1])
  have hn1 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith [hx.2])
  omega

lemma hasSum_cotPair {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasSum (fun n => cotPair n x) (Real.pi * Real.cot (Real.pi*x) - 1/x) := by
  have hc := (summable_cotTerm (real_mem_integerComplement hx)).hasSum
  have he := cot_series_rep' (real_mem_integerComplement hx)
  change (Real.pi : ℂ) * Complex.cot (Real.pi * (x : ℂ)) - 1/(x : ℂ) =
    ∑' n : ℕ, cotTerm (x : ℂ) n at he
  rw [← he] at hc
  have hr := Complex.hasSum_re hc
  simpa only [cotPair, cotTerm, ← Complex.ofReal_natCast, ← Complex.ofReal_one,
    ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    ← Complex.ofReal_mul, ← Complex.ofReal_cot, Complex.ofReal_re] using hr

lemma hasDerivAt_cotPair (n : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    HasDerivAt (cotPair n) (cotPairDeriv n x) x := by
  have hn : (1 : ℝ) ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : x - ((n : ℝ)+1) ≠ 0 := by linarith [hx.2]
  have hp : x + ((n : ℝ)+1) ≠ 0 := by linarith [hx.1]
  have h := (((hasDerivAt_id x).sub_const ((n : ℝ)+1)).inv hm).add
    (((hasDerivAt_id x).add_const ((n : ℝ)+1)).inv hp)
  convert h using 1
  · funext y
    simp [cotPair, one_div]
  · simp only [cotPairDeriv, id_eq]
    ring

lemma norm_cotPairDeriv_le (n : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    ‖cotPairDeriv n x‖ ≤ 5 / ((n : ℝ)+1)^2 := by
  have hn : (1 : ℝ) ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnpos : 0 < (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : x - ((n : ℝ)+1) ≠ 0 := by linarith [hx.2]
  have hp : x + ((n : ℝ)+1) ≠ 0 := by linarith [hx.1]
  have hminus : 1 / (x-((n : ℝ)+1))^2 ≤ 4 / ((n : ℝ)+1)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hm) (sq_pos_of_pos hnpos)).2
    have h0 : 0 ≤ ((n : ℝ)+1)/2-x := by linarith [hx.2]
    nlinarith [sq_nonneg (((n : ℝ)+1)/2-x)]
  have hplus : 1 / (x+((n : ℝ)+1))^2 ≤ 1 / ((n : ℝ)+1)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hp) (sq_pos_of_pos hnpos)).2
    nlinarith [hx.1]
  rw [cotPairDeriv, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ 4 / ((n : ℝ)+1)^2 + 1 / ((n : ℝ)+1)^2 := add_le_add hminus hplus
    _ = _ := by ring

lemma summable_cotPairBound : Summable (fun n : ℕ => 5 / ((n : ℝ)+1)^2) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)^2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hs := (summable_nat_add_iff 1).2 h
  simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hs.mul_left 5

lemma hasDerivAt_tsum_cotPair {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    HasDerivAt (fun y => ∑' n, cotPair n y) (∑' n, cotPairDeriv n x) x := by
  exact hasDerivAt_tsum_of_isPreconnected summable_cotPairBound isOpen_Ioo
    (convex_Ioo (0 : ℝ) (1/2)).isPreconnected
    (fun n y hy => hasDerivAt_cotPair n hy)
    (fun n y hy => norm_cotPairDeriv_le n hy) hx
    (hasSum_cotPair ⟨hx.1, by linarith [hx.2]⟩).summable hx

lemma hasDerivAt_cot_expression {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    HasDerivAt (fun y => Real.pi * Real.cot (Real.pi*y) - 1/y)
      (-Real.pi^2 / Real.sin (Real.pi*x)^2 + 1/x^2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have harg : Real.pi*x < Real.pi := by nlinarith [Real.pi_pos, hx.2]
  have hs : Real.sin (Real.pi*x) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx.1) harg)
  have hc := (Real.hasDerivAt_cos (Real.pi*x)).comp x ((hasDerivAt_id x).const_mul Real.pi)
  have hsin := (Real.hasDerivAt_sin (Real.pi*x)).comp x ((hasDerivAt_id x).const_mul Real.pi)
  have hd := ((hc.div hsin hs).const_mul Real.pi).sub ((hasDerivAt_id x).inv hx0)
  convert hd using 1
  · funext y
    simp [Real.cot_eq_cos_div_sin, one_div]
  · simp only [id_eq, mul_one, Function.comp_apply]
    field_simp
    have htrig := Real.sin_sq_add_cos_sq (Real.pi*x)
    have he := congrArg (fun z : ℝ => Real.pi^2*x^2*z) htrig
    nlinarith only [he]

lemma reciprocal_square_pair_sum {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    (∑' n : ℕ, (1 / (x-((n : ℝ)+1))^2 + 1 / (x+((n : ℝ)+1))^2)) =
      Real.pi^2 / Real.sin (Real.pi*x)^2 - 1/x^2 := by
  have hsum := hasDerivAt_tsum_cotPair hx
  have hev : (fun y => Real.pi * Real.cot (Real.pi*y) - 1/y) =ᶠ[𝓝 x]
      (fun y => ∑' n, cotPair n y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasSum_cotPair ⟨hy.1, by linarith [hy.2]⟩).tsum_eq.symm
  have heq := (hsum.congr_of_eventuallyEq hev).unique (hasDerivAt_cot_expression hx)
  simp_rw [cotPairDeriv] at heq
  rw [tsum_neg] at heq
  simp only [neg_div] at heq
  linarith

lemma summable_reciprocal_square_pairs {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    Summable (fun n : ℕ => (1 / (x-((n : ℝ)+1))^2 + 1 / (x+((n : ℝ)+1))^2)) := by
  have hd : Summable (fun n => cotPairDeriv n x) :=
    .of_norm_bounded summable_cotPairBound (fun n => norm_cotPairDeriv_le n hx)
  simpa only [cotPairDeriv, neg_neg] using hd.neg

set_option maxHeartbeats 800000 in
lemma reciprocal_square_int_sum {x : ℝ} (hx : x ∈ Ioo 0 (1/2 : ℝ)) :
    (∑' n : ℤ, 1 / (x+(n : ℝ))^2) = Real.pi^2 / Real.sin (Real.pi*x)^2 := by
  have hs := summable_reciprocal_square_pairs hx
  have hm : Summable (fun n : ℕ => 1 / (x-((n : ℝ)+1))^2) :=
    hs.of_nonneg_of_le (fun n => by positivity) (fun n => le_add_of_nonneg_right (by positivity))
  have hp : Summable (fun n : ℕ => 1 / (x+((n : ℝ)+1))^2) :=
    hs.of_nonneg_of_le (fun n => by positivity) (fun n => le_add_of_nonneg_left (by positivity))
  have hm' : Summable (fun n : ℕ => 1 / (x+((-(n+1) : ℤ) : ℝ))^2) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, ← sub_eq_add_neg] using hm
  have hp' : Summable (fun n : ℕ => 1 / (x+(((n+1) : ℤ) : ℝ))^2) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hp
  rw [tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => 1 / (x+(n : ℝ))^2) hp' hm']
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_zero,
    add_zero, ← sub_eq_add_neg]
  have he := reciprocal_square_pair_sum hx
  rw [hm.tsum_add hp] at he
  linarith

lemma scaled_reciprocal_square_int_sum {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    (∑' n : ℤ, 1 / (t+(n : ℝ)*Real.pi)^2) = 1 / Real.sin t^2 := by
  have hx : t / Real.pi ∈ Ioo 0 (1/2 : ℝ) := by
    constructor
    · exact div_pos ht.1 Real.pi_pos
    · apply (div_lt_iff₀ Real.pi_pos).2
      linarith [ht.2]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hterm : ∀ n : ℤ, 1 / (t+(n : ℝ)*Real.pi)^2 =
      (Real.pi^2)⁻¹ * (1 / (t/Real.pi+(n : ℝ))^2) := by
    intro n
    have he : t+(n : ℝ)*Real.pi = Real.pi*(t/Real.pi+(n : ℝ)) := by field_simp
    rw [he, mul_pow, one_div, mul_inv_rev, one_div]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, reciprocal_square_int_sum hx]
  have hpxt : Real.pi*(t/Real.pi) = t := by field_simp
  rw [hpxt]
  field_simp

end Szarek
