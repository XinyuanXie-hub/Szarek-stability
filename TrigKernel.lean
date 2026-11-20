module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Tactic

@[expose] public section

open Set Filter
open scoped Topology
namespace Szarek

private lemma nonneg_from_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo 0 (Real.pi / 2), 0 ≤ deriv f x)
    {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2)) : 0 ≤ f t := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2))
    hf.continuous.continuousOn hf.differentiableOn
    (fun x hx => hd x (by simpa using hx))
  simpa [h0] using hm (show (0 : ℝ) ∈ Icc 0 (Real.pi / 2) by
    constructor <;> positivity) ht ht.1

lemma sin_sub_mul_cos_nonneg {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin t - t * Real.cos t := by
  apply nonneg_from_deriv (f := fun x => Real.sin x - x * Real.cos x) (by fun_prop)
    (by simp) ?_ ht
  intro x hx
  have hd : HasDerivAt (fun x => Real.sin x - x * Real.cos x) (x * Real.sin x) x := by
    convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> first | rfl | (dsimp; ring)
  rw [hd.deriv]
  exact mul_nonneg hx.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2, Real.pi_pos]))

lemma two_sub_two_cos_sub_mul_sin_nonneg {t : ℝ} (ht : t ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ 2 - 2 * Real.cos t - t * Real.sin t := by
  apply nonneg_from_deriv (f := fun x => 2 - 2 * Real.cos x - x * Real.sin x) (by fun_prop)
    (by simp) ?_ ht
  intro x hx
  have hd : HasDerivAt (fun x => 2 - 2 * Real.cos x - x * Real.sin x)
      (Real.sin x - x * Real.cos x) x := by
    convert ((hasDerivAt_const x (2 : ℝ)).sub ((Real.hasDerivAt_cos x).const_mul 2)).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)) using 1 <;> first | rfl | (dsimp; ring)
  rw [hd.deriv]
  exact sin_sub_mul_cos_nonneg ⟨hx.1.le, hx.2.le⟩

lemma cusa_huygens {t : ℝ} (ht : 0 < t) (htp : t ≤ Real.pi / 2) :
    Real.sin t / t ≤ (2 + Real.cos t) / 3 := by
  have h : 0 ≤ t * (2 + Real.cos t) - 3 * Real.sin t := by
    apply nonneg_from_deriv (f := fun x => x * (2 + Real.cos x) - 3 * Real.sin x)
      (by fun_prop) (by simp) ?_ ⟨ht.le, htp⟩
    intro x hx
    have hd : HasDerivAt (fun x => x * (2 + Real.cos x) - 3 * Real.sin x)
        (2 - 2 * Real.cos x - x * Real.sin x) x := by
      convert ((hasDerivAt_id x).mul ((hasDerivAt_const x (2 : ℝ)).add
        (Real.hasDerivAt_cos x))).sub ((Real.hasDerivAt_sin x).const_mul 3) using 1 <;> first | rfl | (dsimp; ring)
    rw [hd.deriv]
    exact two_sub_two_cos_sub_mul_sin_nonneg ⟨hx.1.le, hx.2.le⟩
  apply (div_le_iff₀ ht).mpr
  nlinarith

noncomputable def trigKernel (t : ℝ) : ℝ :=
  Real.sqrt (Real.cos t) * (1 / Real.sin t ^ 2 - 1 / t ^ 2)

lemma kernel_polynomial_nonpos {t : ℝ} (ht : 0 < t) (htp : t < Real.pi / 2) :
    4 * Real.cos t * (Real.sin t / t)^3 + Real.sin t ^ 2 * (Real.sin t / t)^2 -
      1 - 3 * Real.cos t ^ 2 ≤ 0 := by
  have hc : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩).le
  have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.le (by linarith [Real.pi_pos])
  have hcu := cusa_huygens ht htp.le
  have hratio : 0 ≤ Real.sin t / t := div_nonneg hs ht.le
  calc
    _ ≤ 4 * Real.cos t * ((2 + Real.cos t)/3)^3 +
        Real.sin t ^ 2 * ((2 + Real.cos t)/3)^2 - 1 - 3 * Real.cos t ^ 2 := by
      gcongr
    _ = -(1 - Real.cos t)^3 * (Real.cos t + 15) / 27 := by
      rw [Real.sin_sq]
      ring
    _ ≤ 0 := by
      have h1 : 0 ≤ 1 - Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg h1 3)) (by linarith)) (by norm_num)

lemma trigKernel_deriv_nonpos {t : ℝ} (ht : 0 < t) (htp : t < Real.pi / 2) :
    deriv trigKernel t ≤ 0 := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hq : 0 < Real.sqrt (Real.cos t) := Real.sqrt_pos.mpr hc
  have hd := ((Real.hasDerivAt_cos t).sqrt hc.ne').mul
    (((hasDerivAt_const t (1 : ℝ)).div ((Real.hasDerivAt_sin t).pow 2) (pow_ne_zero 2 hs.ne')).sub
      ((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne')))
  change HasDerivAt trigKernel _ t at hd
  rw [hd.deriv]
  apply nonpos_of_mul_nonpos_left (b := 2 * Real.sqrt (Real.cos t) * Real.sin t ^ 3) ?_ (by positivity)
  have heq : 2 * Real.sqrt (Real.cos t) * Real.sin t ^ 3 *
      (-Real.sin t / (2 * Real.sqrt (Real.cos t)) * (1 / Real.sin t ^ 2 - 1 / t ^ 2) +
       Real.sqrt (Real.cos t) * ((0 * Real.sin t ^ 2 - 1 * (2 * Real.sin t ^ (2-1) * Real.cos t)) / (Real.sin t ^ 2)^2 -
        (0 * t^2 - 1 * (2 * t^(2-1) * 1))/(t^2)^2)) =
      4 * Real.cos t * (Real.sin t / t)^3 + Real.sin t^2 * (Real.sin t/t)^2 - 1 - 3 * Real.cos t^2 := by
    field_simp [hs.ne', ht.ne', hq.ne']
    have hsq := Real.sq_sqrt hc.le
    rw [hsq]
    norm_num
    linear_combination -(Real.sin t * t ^ 4) * (Real.sin_sq_add_cos_sq t)
  convert heq.le.trans (kernel_polynomial_nonpos ht htp) using 1
  simp
  ring

lemma tendsto_sin_div_right : Tendsto (fun t : ℝ => Real.sin t / t) (𝓝[>] 0) (𝓝 1) :=
  Real.tendsto_sin_div_nhdsNE_zero.mono_left (nhdsWithin_mono _ (fun _ hx => ne_of_gt hx))

lemma tendsto_one_sub_cos_div_sq_right :
    Tendsto (fun t : ℝ => (1 - Real.cos t) / t ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := Real.sin) (g' := fun x => 2 * x)
  · exact Filter.Eventually.of_forall fun x => by
      convert (hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x) using 1
      simp
  · exact Filter.Eventually.of_forall fun x => by
      convert (hasDerivAt_id x).pow 2 using 1 <;> first | rfl | simp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  · simpa using (show Continuous (fun x : ℝ => 1 - Real.cos x) by fun_prop).continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0) |>.tendsto
  · simpa using (show Continuous (fun x : ℝ => x ^ 2) by fun_prop).continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0) |>.tendsto
  · convert tendsto_sin_div_right.div_const 2 using 1
    simp [div_div, mul_comm]

lemma tendsto_sine_remainder_cubic_right :
    Tendsto (fun t : ℝ => (t - Real.sin t) / t ^ 3) (𝓝[>] 0) (𝓝 (1 / 6)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun x => 1 - Real.cos x) (g' := fun x => 3 * x ^ 2)
  · exact Filter.Eventually.of_forall fun x => by
      convert (hasDerivAt_id x).sub (Real.hasDerivAt_sin x) using 1
      rfl
  · exact Filter.Eventually.of_forall fun x => by
      convert (hasDerivAt_id x).pow 3 using 1 <;> first | rfl | simp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hx))
  · simpa using (show Continuous (fun x : ℝ => x - Real.sin x) by fun_prop).continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0) |>.tendsto
  · simpa using (show Continuous (fun x : ℝ => x ^ 3) by fun_prop).continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0) |>.tendsto
  · convert tendsto_one_sub_cos_div_sq_right.div_const 3 using 1 <;> norm_num [div_div, mul_comm]

lemma trigKernel_limit_right : Tendsto trigKernel (𝓝[>] 0) (𝓝 (1 / 3)) := by
  have hratio := tendsto_sin_div_right
  have hsqrt : Tendsto (fun t => Real.sqrt (Real.cos t)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (show Continuous (fun t => Real.sqrt (Real.cos t)) by fun_prop).continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0) |>.tendsto
  have h := hsqrt.mul ((tendsto_sine_remainder_cubic_right.mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add hratio)).div (hratio.pow 2) (by norm_num))
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < Real.pi by positivity))] with t ht htp
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht htp).ne'
  dsimp [trigKernel]
  field_simp [ne_of_gt (show 0 < t from ht), hs]
  ring

lemma trigKernel_differentiableAt {t : ℝ} (ht : 0 < t) (htp : t < Real.pi / 2) :
    DifferentiableAt ℝ trigKernel t := by
  have hc : Real.cos t ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩).ne'
  have hs : Real.sin t ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])).ne'
  have hss : Real.sin t ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have htt : t ^ 2 ≠ 0 := pow_ne_zero 2 ht.ne'
  unfold trigKernel
  fun_prop (disch := assumption)

lemma trigKernel_antitone : AntitoneOn trigKernel (Ioo 0 (Real.pi / 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
  · intro t ht
    exact (trigKernel_differentiableAt ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    simp only [interior_Ioo] at ht
    exact (trigKernel_differentiableAt ht.1 ht.2).differentiableWithinAt
  · intro t ht
    simp only [interior_Ioo] at ht
    exact trigKernel_deriv_nonpos ht.1 ht.2

/-- Paper inequality (20), the pointwise kernel estimate in Lemma 4. -/
lemma trigKernel_le_one_third {t : ℝ} (ht : 0 < t) (htp : t < Real.pi / 2) :
    Real.sqrt (Real.cos t) * (1 / Real.sin t ^ 2 - 1 / t ^ 2) ≤ 1 / 3 := by
  change trigKernel t ≤ 1 / 3
  apply ge_of_tendsto trigKernel_limit_right
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht)] with x hx hxt
  exact trigKernel_antitone ⟨hx, lt_trans hxt htp⟩ ⟨ht, htp⟩ (le_of_lt hxt)

#print axioms trigKernel_le_one_third
end Szarek
