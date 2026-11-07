import Definitions
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

open Filter Set
open scoped Topology BigOperators

namespace Szarek

noncomputable def realDigamma (x : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) x

lemma logGamma_differentiable {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x := by
  exact (Real.differentiableAt_Gamma (fun m => ne_of_gt
    (lt_of_le_of_lt (neg_nonpos.mpr (Nat.cast_nonneg m)) hx))).log
    (ne_of_gt (Real.Gamma_pos_of_pos hx))

lemma logGamma_add_one {x : ℝ} (hx : 0 < x) :
    (Real.log ∘ Real.Gamma) (x + 1) =
      (Real.log ∘ Real.Gamma) x + Real.log x := by
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]

lemma realDigamma_add_one {x : ℝ} (hx : 0 < x) :
    realDigamma (x + 1) = realDigamma x + 1 / x := by
  unfold realDigamma
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (logGamma_differentiable hx) (Real.differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with z hz using logGamma_add_one hz

lemma realDigamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    realDigamma (x + n) = realDigamma x + ∑ k ∈ Finset.range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, realDigamma_add_one (by positivity), ih,
      Finset.sum_range_succ]
    ring

lemma realDigamma_le_log {x : ℝ} (hx : 0 < x) : realDigamma x ≤ Real.log x := by
  have h := Real.convexOn_log_Gamma.deriv_le_slope hx
    (show 0 < x + 1 by linarith) (show x < x + 1 by linarith)
    (logGamma_differentiable hx)
  have hr := logGamma_add_one hx
  simp only [slope_def_field, show x + 1 - x = 1 by ring, div_one] at h
  change realDigamma x ≤ _ at h
  linarith

lemma log_sub_one_le_realDigamma {x : ℝ} (hx : 1 < x) :
    Real.log (x - 1) ≤ realDigamma x := by
  have h := Real.convexOn_log_Gamma.slope_le_deriv
    (show 0 < x - 1 by linarith) (show 0 < x by linarith)
    (show x - 1 < x by linarith) (logGamma_differentiable (by linarith : 0 < x))
  have hr := logGamma_add_one (show 0 < x - 1 by linarith)
  simp only [sub_add_cancel] at hr
  simp only [slope_def_field, show x - (x - 1) = 1 by ring, div_one] at h
  change _ ≤ realDigamma x at h
  linarith

lemma tendsto_realDigamma_sub_log :
    Tendsto (fun x : ℝ => realDigamma x - Real.log x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => Real.log x - Real.log (x - 1)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg, add_comm] using (Real.tendsto_log_comp_add_sub_log (-1)).neg
  have haux := squeeze_zero'
    (show ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log x - realDigamma x from
      (eventually_gt_atTop 1).mono fun x hx => sub_nonneg.mpr (realDigamma_le_log (by linarith)))
    (show ∀ᶠ x : ℝ in atTop, Real.log x - realDigamma x ≤
      Real.log x - Real.log (x - 1) from
      (eventually_gt_atTop 1).mono fun x hx => by linarith [log_sub_one_le_realDigamma hx])
    hlim
  simpa only [neg_zero, neg_sub] using haux.neg

lemma tendsto_realDigamma_shift_sub (x y : ℝ) :
    Tendsto (fun n : ℕ => realDigamma (x + n) - realDigamma (y + n)) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hy : Tendsto (fun n : ℕ => y + (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (x + n) - Real.log (y + n)) atTop (𝓝 0) := by
    convert (Real.tendsto_log_comp_add_sub_log (x - y)).comp hy using 1
    funext n
    simp only [Function.comp_apply]
    congr 2
    ring
  convert ((tendsto_realDigamma_sub_log.comp hx).sub
    (tendsto_realDigamma_sub_log.comp hy)).add hlog using 1
  · funext n
    simp only [Function.comp_apply]
    ring
  · norm_num

theorem hasSum_realDigamma_sub {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    HasSum (fun k : ℕ => 1 / (x + k) - 1 / (y + k)) (realDigamma y - realDigamma x) := by
  have hy : 0 < y := hx.trans_le hxy
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => ?_) _).2
  · have hlim := (tendsto_realDigamma_shift_sub x y).add_const
      (realDigamma y - realDigamma x)
    simp only [zero_add] at hlim
    convert hlim using 1
    funext n
    rw [realDigamma_add_nat hx, realDigamma_add_nat hy, Finset.sum_sub_distrib]
    ring
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))

lemma log_haagerupF {s : ℝ} (hs : 0 < s) :
    Real.log (haagerupF s) = Real.log 2 - (Real.log Real.pi + Real.log s) / 2 +
      (Real.log ∘ Real.Gamma) ((s + 1) / 2) - (Real.log ∘ Real.Gamma) (s / 2) := by
  have hnum : Real.Gamma ((s + 1) / 2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hden : Real.Gamma (s / 2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hroot : Real.sqrt (Real.pi * s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [haagerupF, Real.log_mul (div_ne_zero (by norm_num) hroot) (div_ne_zero hnum hden),
    Real.log_div (by norm_num) hroot, Real.log_div hnum hden,
    Real.log_sqrt (by positivity), Real.log_mul Real.pi_ne_zero hs.ne']
  simp only [Function.comp_apply]
  ring

theorem hasDerivAt_log_haagerupF {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => Real.log (haagerupF s))
      (-1 / (2 * s) + (realDigamma ((s + 1) / 2) - realDigamma (s / 2)) / 2) s := by
  have h1 := (logGamma_differentiable (show 0 < (s + 1) / 2 by linarith)).hasDerivAt.comp s
    (((hasDerivAt_id s).add_const 1).div_const 2)
  have h2 := (logGamma_differentiable (show 0 < s / 2 by linarith)).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const 2)
  have h3 := ((hasDerivAt_const s (Real.log Real.pi)).add (Real.hasDerivAt_log hs.ne')).div_const 2
  have h := (((hasDerivAt_const s (Real.log 2)).sub h3).add h1).sub h2
  have heq : (fun z => Real.log 2 - (Real.log Real.pi + Real.log z) / 2 +
      (Real.log ∘ Real.Gamma) ((z + 1) / 2) - (Real.log ∘ Real.Gamma) (z / 2)) =ᶠ[𝓝 s]
        (fun z => Real.log (haagerupF z)) := by
    filter_upwards [eventually_gt_nhds hs] with z hz using (log_haagerupF hz).symm
  convert h.congr_of_eventuallyEq heq.symm using 1
  simp only [realDigamma]
  ring

theorem hasSum_haagerup_reciprocal {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => 1 / (s + 2 * k) - 1 / (s + 2 * k + 1))
      ((realDigamma ((s + 1) / 2) - realDigamma (s / 2)) / 2) := by
  have h := (hasSum_realDigamma_sub (show 0 < s / 2 by linarith)
    (show s / 2 ≤ (s + 1) / 2 by linarith)).div_const 2
  convert h using 1
  funext k
  have h0 : s + 2 * (k : ℝ) ≠ 0 := by positivity
  have h1 : s + 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The series version of equation (15) in the paper. -/
theorem deriv_log_haagerupF_series {s : ℝ} (hs : 0 < s) :
    deriv (fun s => Real.log (haagerupF s)) s = -1 / (2 * s) +
      ∑' k : ℕ, (1 / (s + 2 * k) - 1 / (s + 2 * k + 1)) := by
  rw [(hasDerivAt_log_haagerupF hs).deriv, (hasSum_haagerup_reciprocal hs).tsum_eq]

end Szarek
