module

public import HaagerupAnalysis
public import PoweredCosIntegrability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Szarek

def cosineIBPPrimitive (s t : ℝ) : ℝ :=
  (1 - (Real.cos t) ^ s) * Real.cos t / Real.sin t

lemma cosineIBPPrimitive_deriv {s t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (cosineIBPPrimitive s)
      (s * (Real.cos t) ^ s - (1 - (Real.cos t) ^ s) / (Real.sin t) ^ 2) t := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
  have hn : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hp := (Real.hasDerivAt_cos t).rpow_const (p := s) (Or.inl hc.ne')
  have h := (((hasDerivAt_const t (1 : ℝ)).sub hp).mul (Real.hasDerivAt_cos t)).div
    (Real.hasDerivAt_sin t) hn.ne'
  convert h using 1
  · rfl
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [Real.rpow_sub hc, Real.rpow_one]
    field_simp
    have hs := Real.sin_sq_add_cos_sq t
    have he : (1 - Real.cos t ^ s) * (Real.sin t ^ 2 + Real.cos t ^ 2) =
        1 - Real.cos t ^ s := by rw [hs]; ring
    nlinarith only [he]

lemma cosineIBPPrimitive_zero_limit (s : ℝ) :
    Tendsto (cosineIBPPrimitive s) (𝓝[>] 0) (𝓝 0) := by
  have hn : HasDerivAt (fun t : ℝ => 1 - (Real.cos t) ^ s) 0 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub
      ((Real.hasDerivAt_cos 0).rpow_const (p := s) (Or.inl (by norm_num))) using 1
    simp
  have hN : Tendsto (fun t : ℝ => (1 - (Real.cos t) ^ s) / t) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [slope_fun_def_field, Real.cos_zero, Real.one_rpow, sub_self, sub_zero] using hn.tendsto_slope
  have hs : Tendsto (fun t : ℝ => t / Real.sin t) (𝓝[≠] 0) (𝓝 1) := by
    simpa using Real.tendsto_sin_div_nhdsNE_zero.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcos : Tendsto Real.cos (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero] using (Real.continuous_cos.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hprod := (hN.mul hcos).mul hs
  have heq : cosineIBPPrimitive s =ᶠ[𝓝[≠] 0]
      (fun t : ℝ => ((1 - (Real.cos t) ^ s) / t) * Real.cos t * (t / Real.sin t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    unfold cosineIBPPrimitive
    field_simp
  exact ((tendsto_congr' heq).mpr (by simpa using hprod)).mono_left (nhdsGT_le_nhdsNE 0)

lemma cosineIBPPrimitive_halfpi_limit {s : ℝ} (hs : 0 < s) :
    Tendsto (cosineIBPPrimitive s) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hc : Continuous fun t : ℝ => (Real.cos t) ^ s :=
    Real.continuous_cos.rpow_const (fun _ => Or.inr hs.le)
  have h : ContinuousAt (cosineIBPPrimitive s) (Real.pi / 2) := by
    exact ((continuousAt_const.sub hc.continuousAt).mul Real.continuous_cos.continuousAt).div
      Real.continuous_sin.continuousAt (by norm_num)
  simpa [cosineIBPPrimitive] using h.tendsto.mono_left nhdsWithin_le_nhds

/-- The local integration-by-parts identity in paper equation (12). -/
lemma local_cosine_integral_identity {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in Ioo 0 (Real.pi / 2),
      (1 - (Real.cos t) ^ s) / (Real.sin t) ^ 2) =
      s * ∫ t : ℝ in 0..(Real.pi / 2), (Real.cos t) ^ s := by
  have hB : (0 : ℝ) < Real.pi / 2 := by positivity
  have hc : Continuous (fun t : ℝ => (Real.cos t) ^ s) :=
    Real.continuous_cos.rpow_const (fun _ => Or.inr hs.le)
  have hci : IntervalIntegrable (fun t : ℝ => (Real.cos t) ^ s) volume 0 (Real.pi / 2) :=
    hc.intervalIntegrable _ _
  have hki : IntervalIntegrable (fun t : ℝ => (1 - (Real.cos t) ^ s) / (Real.sin t) ^ 2)
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hB.le).mpr (integrableOn_poweredCosKernel_local hs)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hB
    (fun t ht => cosineIBPPrimitive_deriv (s := s) ht) ((hci.const_mul s).sub hki)
    (cosineIBPPrimitive_zero_limit s) (cosineIBPPrimitive_halfpi_limit hs)
  rw [intervalIntegral.integral_sub (hci.const_mul s) hki,
    intervalIntegral.integral_const_mul] at hi
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hB.le]
  linarith

#print axioms Szarek.local_cosine_integral_identity
end Szarek
