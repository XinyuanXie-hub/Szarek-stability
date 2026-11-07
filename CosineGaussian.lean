import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace Szarek

lemma cosine_gaussian_deriv (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2) * Real.cos x)
      (Real.exp (t ^ 2 / 2) * (t * Real.cos t - Real.sin t)) t := by
  convert ((((hasDerivAt_id t).pow 2).div_const 2).exp.mul (Real.hasDerivAt_cos t)) using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq]
    ring

/-- Equation (14) of the paper, proved by a differential inequality. -/
theorem cos_le_gaussian {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi / 2) :
    Real.cos t ≤ Real.exp (-(t ^ 2) / 2) := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (x ^ 2 / 2) * Real.cos x)
      (Set.Icc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact ((Real.continuous_exp.comp ((continuous_id.pow 2).div_const 2)).mul
        Real.continuous_cos).continuousOn
    · intro x hx
      exact (cosine_gaussian_deriv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(cosine_gaussian_deriv x).deriv]
      have hx' : 0 < x ∧ x < Real.pi / 2 := by simpa only [interior_Icc, Set.mem_Ioo] using hx
      have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx'.2⟩
      have htan := Real.le_tan hx'.1.le hx'.2
      rw [Real.tan_eq_sin_div_cos] at htan
      have hs : x * Real.cos x ≤ Real.sin x := (le_div_iff₀ hc).mp htan
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hs)
  have h := hanti (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) by
    exact ⟨le_rfl, by positivity⟩) ⟨ht, htpi⟩ ht
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero, Real.cos_zero,
    one_mul] at h
  have heq : Real.exp (-(t ^ 2) / 2) = (Real.exp (t ^ 2 / 2))⁻¹ := by
    rw [show -(t ^ 2) / 2 = -(t ^ 2 / 2) by ring, Real.exp_neg]
  rw [heq, ← one_div]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h)

theorem cos_nonneg_first_quadrant {t : ℝ} (ht : 0 ≤ t) (htpi : t ≤ Real.pi / 2) :
    0 ≤ Real.cos t :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], htpi⟩

/-- The numerator in equation (18) is nonpositive through the first negative cosine lobe. -/
theorem positive_cos_sub_gaussian_nonpos {t : ℝ} (ht : 0 ≤ t)
    (htpi : t ≤ 3 * Real.pi / 2) :
    max (Real.cos t) 0 - Real.exp (-(t ^ 2) / 2) ≤ 0 := by
  by_cases h : t ≤ Real.pi / 2
  · rw [max_eq_left (cos_nonneg_first_quadrant ht h)]
    exact sub_nonpos.mpr (cos_le_gaussian ht h)
  · have hc : Real.cos t ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le
      (le_of_not_ge h) (by linarith)
    rw [max_eq_right hc]
    exact sub_nonpos.mpr (Real.exp_pos _).le

open scoped BigOperators

/-- The product comparison on the initial nonnegative-cosine interval. -/
lemma prod_cos_le_gaussian {ι : Type*} (s : Finset ι) (a : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hcut : ∀ i ∈ s, a i * t ≤ Real.pi / 2) :
    (∏ i ∈ s, Real.cos (a i * t)) ≤
      Real.exp (-(∑ i ∈ s, (a i) ^ 2) * t ^ 2 / 2) := by
  calc
    _ ≤ ∏ i ∈ s, Real.exp (-((a i * t) ^ 2) / 2) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact cos_nonneg_first_quadrant (mul_nonneg (ha i hi) ht) (hcut i hi)
      · intro i hi
        exact cos_le_gaussian (mul_nonneg (ha i hi) ht) (hcut i hi)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      calc
        _ = ∑ i ∈ s, (a i) ^ 2 * (-(t ^ 2) / 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [← Finset.sum_mul]; ring

#print axioms Szarek.cos_le_gaussian
#print axioms Szarek.positive_cos_sub_gaussian_nonpos
end Szarek
