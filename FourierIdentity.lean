import FiniteSharpness
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp

open scoped BigOperators
open MeasureTheory Set
noncomputable section
namespace Szarek

/-- The characteristic-function identity for the finite uniform sign cube. -/
theorem sum_cos_signs {n : ℕ} (a : Fin n → ℝ) :
    (∑ ε : Fin n → Bool, Real.cos (∑ i, a i * (if ε i then 1 else -1))) =
      (2 : ℝ)^n * ∏ i, Real.cos (a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_signs_succ, Fintype.sum_bool]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ite_true, Bool.false_eq_true, ite_false, mul_one, mul_neg_one]
    rw [← Finset.sum_add_distrib]
    have h : ∀ x y : ℝ, Real.cos (x + y) + Real.cos (-x + y) =
        2 * Real.cos x * Real.cos y := by
      intro x y
      rw [Real.cos_add, Real.cos_add, Real.cos_neg, Real.sin_neg]
      ring
    simp_rw [h]
    rw [← Finset.mul_sum, ih, Fin.prod_univ_succ, pow_succ]
    ring

/-- Averaging the Fourier kernels gives the product-of-cosines kernel pointwise. -/
theorem average_fourier_kernel {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    (∑ ε : Fin n → Bool,
      (1 - Real.cos (t * ∑ i, a i * (if ε i then 1 else -1))) / t^2) / (2 : ℝ)^n =
      (1 - ∏ i, Real.cos (t * a i)) / t^2 := by
  have h := sum_cos_signs (fun i => t * a i)
  simp only [mul_assoc, ← Finset.mul_sum] at h
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_one]
  rw [h]
  have hp : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The scalar Fourier kernel, with the harmless total-field value zero at t=0. -/
def fourierKernel (x t : ℝ) : ℝ := (1 - Real.cos (t * x)) / t^2

lemma fourierKernel_nonneg (x t : ℝ) : 0 ≤ fourierKernel x t :=
  div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)

lemma fourierKernel_le_cauchy (x t : ℝ) :
    fourierKernel x t ≤ (x^2 / 2 + 2) / (1 + t^2) := by
  by_cases ht : t = 0
  · subst t
    simp only [fourierKernel, zero_mul, Real.cos_zero, sub_self, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, add_zero, div_one]
    positivity
  have ht2 : 0 < t^2 := sq_pos_of_ne_zero ht
  have hsmall : fourierKernel x t ≤ x^2 / 2 := by
    apply (div_le_iff₀ ht2).2
    have h := Real.one_sub_sq_div_two_le_cos (x := t*x)
    nlinarith only [h]
  have hlarge : 1 - Real.cos (t*x) ≤ 2 := by linarith [Real.neg_one_le_cos (t*x)]
  apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).2
  calc
    _ = fourierKernel x t + (1 - Real.cos (t*x)) := by
      unfold fourierKernel
      field_simp
    _ ≤ _ := add_le_add hsmall hlarge

/-- Absolute integrability follows from a Cauchy-kernel bound, without using
any unproved Fourier evaluation. -/
theorem integrable_fourierKernel (x : ℝ) : Integrable (fourierKernel x) := by
  apply (integrable_inv_one_add_sq.const_mul (x^2/2+2)).mono'
  · unfold fourierKernel
    exact (by fun_prop : Measurable (fun t : ℝ => (1 - Real.cos (t*x))/t^2)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (fourierKernel_nonneg x t)]
    simpa only [div_eq_mul_inv] using fourierKernel_le_cauchy x t

/-- Integral interchange for the finite sign cube. All scalar kernels are
proved integrable above; no Fourier evaluation is assumed here. -/
theorem integral_product_fourier_kernel {n : ℕ} (a : Fin n → ℝ) :
    (∫ t in Ioi (0 : ℝ), (1 - ∏ i, Real.cos (t * a i)) / t^2) =
      (∑ ε : Fin n → Bool,
        ∫ t in Ioi (0 : ℝ), fourierKernel (∑ i, a i * (if ε i then 1 else -1)) t) /
          (2 : ℝ)^n := by
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        (∑ ε : Fin n → Bool, fourierKernel (∑ i, a i * (if ε i then 1 else -1)) t) /
          (2 : ℝ)^n := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (average_fourier_kernel a t).symm
    _ = _ := by
      rw [integral_div, integral_finsetSum]
      intro ε hε
      exact (integrable_fourierKernel _).integrableOn

/-- The finite representation follows from the scalar improper-integral
identity. The latter is an explicit premise, not an axiom or established result. -/
theorem rademacher_fourier_of_scalar
    (hscalar : ∀ x : ℝ, |x| = (2 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), fourierKernel x t)
    {n : ℕ} (a : Fin n → ℝ) :
    rademacherMean a = (2 / Real.pi) *
      ∫ t in Ioi (0 : ℝ), (1 - ∏ i, Real.cos (t * a i)) / t^2 := by
  rw [integral_product_fourier_kernel]
  unfold rademacherMean
  simp_rw [hscalar]
  rw [← Finset.mul_sum]
  ring

#print axioms Szarek.integrable_fourierKernel
#print axioms Szarek.integral_product_fourier_kernel
end Szarek
