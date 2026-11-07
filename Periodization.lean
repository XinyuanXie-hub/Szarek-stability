import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas

open MeasureTheory Set
open scoped Topology Pointwise
noncomputable section
namespace Szarek

/-- Periodizing an integrable function over any fundamental interval. -/
theorem integral_periodization {T : ℝ} (hT : 0 < T) (a : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f) :
    (∫ x, f x) = ∫ t in Ioc a (a+T), ∑' n : ℤ, f ((n : ℝ)*T+t) := by
  let G := AddSubgroup.zmultiples T
  let S := Ioc a (a+T)
  have hfd := isAddFundamentalDomain_Ioc hT a
  have hisum : Integrable f (Measure.sum (fun g : G => volume.restrict (g +ᵥ S))) := by
    rw [hfd.sum_restrict]
    exact hf
  have hnorm : Summable (fun g : G => ∫ t in S, ‖f (g +ᵥ t)‖) := by
    apply hisum.summable_integral.congr
    intro g
    exact (measurePreserving_vadd g volume).setIntegral_image_emb
      (measurableEmbedding_const_vadd g) (fun t => ‖f t‖) S
  have hsec : ∀ g : G, IntegrableOn (fun t => f (g +ᵥ t)) S := by
    intro g
    exact ((measurePreserving_vadd g volume).integrable_comp hf.aestronglyMeasurable).2 hf |>.integrableOn
  calc
    _ = ∑' g : G, ∫ t in S, f (g +ᵥ t) := hfd.integral_eq_tsum'' f hf
    _ = ∫ t in S, ∑' g : G, f (g +ᵥ t) :=
      integral_tsum_of_summable_integral_norm hsec hnorm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have he := ((AddSubgroup.zmultiplesEquivInt hT.ne').symm.toEquiv.tsum_eq
        (fun g : G => f (g +ᵥ t))).symm
      change (∑' g : G, f ((g : ℝ)+t)) =
        ∑' n : ℤ, f ((((AddSubgroup.zmultiplesEquivInt hT.ne').symm n : G) : ℝ)+t) at he
      change (∑' g : G, f ((g : ℝ)+t)) = _
      simpa only [AddSubgroup.coe_zmultiplesEquivInt_symm_apply, zsmul_eq_mul] using he

end Szarek
