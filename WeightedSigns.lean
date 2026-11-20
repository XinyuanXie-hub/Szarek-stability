module

public import WeightedHaagerup

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace Szarek

lemma cos_mul_abs (t x : ℝ) : Real.cos (t * |x|) = Real.cos (t * x) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, mul_neg, Real.cos_neg]

lemma rademacherMean_abs {n : ℕ} (a : Fin n → ℝ) :
    rademacherMean (fun i => |a i|) = rademacherMean a := by
  rw [rademacher_fourier, rademacher_fourier]
  simp only [cos_mul_abs]

lemma weighted_haagerup_all_signs_of_integral
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t : ℝ in Ioi 0, poweredCosKernel s t) = haagerupF s)
    (n : ℕ) (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    ∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2) ≤ rademacherMean a := by
  have habs : ∑ i, |a i| ^ 2 = 1 := by simpa only [sq_abs] using ha
  simpa only [sq_abs, rademacherMean_abs] using
    weighted_haagerup_of_integral heval (fun i => |a i|) (fun i => abs_nonneg _) habs

end Szarek
