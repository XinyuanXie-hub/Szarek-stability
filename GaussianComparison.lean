module

public import CosineGaussian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open MeasureTheory Set
namespace Szarek

/-- The cutoff argument in Lemma 3: retain the signed integrand on the initial
interval, and discard only the negative part represented by h on the tail. -/
theorem gaussian_weight_cutoff_bound (f h : ℝ → ℝ) (R L : ℝ)
    (hR : 0 < R) (hL : 0 ≤ L)
    (hf : IntegrableOn f (Ioi 0)) (hh : IntegrableOn h (Ioi R))
    (hfneg : ∀ x, 0 < x → x ≤ R → f x ≤ 0)
    (hhpos : ∀ x, R < x → 0 ≤ h x)
    (hfadd : ∀ x, R < x → 0 ≤ f x + h x) :
    (∫ x in Ioi 0, Real.exp (-L * x ^ 2) * f x) ≤
      Real.exp (-L * R ^ 2) * ((∫ x in Ioi 0, f x) + ∫ x in Ioi R, h x) := by
  have hsub : Ioi R ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans hR hx
  have hi : IntegrableOn ((Ioi R).indicator h) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr hh).integrableOn
  have hw : AEStronglyMeasurable (fun x : ℝ => Real.exp (-L * x ^ 2))
      (volume.restrict (Ioi 0)) := by
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).aestronglyMeasurable
  have hwb : ∀ x : ℝ, ‖Real.exp (-L * x ^ 2)‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [mul_nonneg hL (sq_nonneg x)]
  have hwi : IntegrableOn (fun x => Real.exp (-L * x ^ 2) * f x) (Ioi 0) :=
    hf.bdd_mul hw (Filter.Eventually.of_forall hwb)
  have hri : IntegrableOn (fun x => Real.exp (-L * R ^ 2) * f x +
      Real.exp (-L * R ^ 2) * (Ioi R).indicator h x) (Ioi 0) :=
    (hf.const_mul _).add (hi.const_mul _)
  have hpoint : ∀ x ∈ Ioi (0 : ℝ), Real.exp (-L * x ^ 2) * f x ≤
      Real.exp (-L * R ^ 2) * f x + Real.exp (-L * R ^ 2) * (Ioi R).indicator h x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases hxR : x ≤ R
    · have hind : (Ioi R).indicator h x = 0 := indicator_of_notMem (not_lt.mpr hxR) _
      rw [hind, mul_zero, add_zero]
      have hwle : Real.exp (-L * R ^ 2) ≤ Real.exp (-L * x ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hs : x ^ 2 ≤ R ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hs hL]
      exact mul_le_mul_of_nonpos_right hwle (hfneg x hx hxR)
    · have hxR' : R < x := lt_of_not_ge hxR
      rw [indicator_of_mem (show x ∈ Ioi R from hxR'), ← mul_add]
      have hwle : Real.exp (-L * x ^ 2) ≤ Real.exp (-L * R ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hs : R ^ 2 ≤ x ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hs hL]
      calc
        _ ≤ Real.exp (-L * x ^ 2) * (f x + h x) :=
          mul_le_mul_of_nonneg_left (by linarith [hhpos x hxR']) (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_right hwle (hfadd x hxR')
  have hbound := integral_mono_ae hwi hri
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpoint))
  rw [integral_add (hf.const_mul _) (hi.const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr hsub] at hbound
  simpa only [mul_add] using hbound

#print axioms Szarek.gaussian_weight_cutoff_bound
end Szarek
