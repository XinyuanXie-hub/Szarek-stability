module

public import ScalarFourier
public import HaagerupAnalysis
public import HaagerupConvexity
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Szarek

noncomputable def poweredCosKernel (s t : ℝ) : ℝ :=
  (1 - |Real.cos t| ^ s) / t ^ 2

lemma weighted_cos_product {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (t : ℝ) :
    ∏ i, Real.cos (t * a i) ≤
      ∑ i, a i ^ 2 * |Real.cos (t * a i)| ^ (1 / a i ^ 2) := by
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun i => a i ^ 2) (fun i => |Real.cos (t * a i)| ^ (1 / a i ^ 2))
    (fun i _ => sq_nonneg _) ha (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hprod : ∏ i, (|Real.cos (t * a i)| ^ (1 / a i ^ 2)) ^ (a i ^ 2) =
      ∏ i, |Real.cos (t * a i)| := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : a i = 0
    · simp [hi]
    · rw [← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ _ (pow_ne_zero _ hi), Real.rpow_one]
  rw [hprod] at h
  exact (le_abs_self (∏ i, Real.cos (t * a i))).trans
    (by simpa only [Finset.abs_prod] using h)

lemma weighted_cos_kernel {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (t : ℝ) :
    ∑ i, a i ^ 2 * ((1 - |Real.cos (t * a i)| ^ (1 / a i ^ 2)) / t ^ 2) ≤
      (1 - ∏ i, Real.cos (t * a i)) / t ^ 2 := by
  have h := weighted_cos_product a ha t
  have he : ∑ i, a i ^ 2 * ((1 - |Real.cos (t * a i)| ^ (1 / a i ^ 2)) / t ^ 2) =
      (1 - ∑ i, a i ^ 2 * |Real.cos (t * a i)| ^ (1 / a i ^ 2)) / t ^ 2 := by
    simp_rw [← mul_div_assoc, mul_sub, mul_one]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ha]
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)

lemma integrableOn_product_cos_kernel {n : ℕ} (a : Fin n → ℝ) :
    IntegrableOn (fun t : ℝ => (1 - ∏ i, Real.cos (t * a i)) / t ^ 2) (Ioi 0) := by
  have hsum : IntegrableOn (fun t => ∑ ε : Fin n → Bool,
      fourierKernel (∑ i, a i * (if ε i then 1 else -1)) t) (Ioi 0) := by
    exact integrable_finsetSum Finset.univ
      (fun ε _ => (integrable_fourierKernel (∑ i, a i * (if ε i then 1 else -1))).integrableOn)
  have h := hsum.div_const ((2 : ℝ) ^ n)
  apply h.congr
  filter_upwards [] with t
  exact average_fourier_kernel a t

noncomputable def coefficientCosKernel (a t : ℝ) : ℝ :=
  (1 - |Real.cos (t * a)| ^ (1 / a ^ 2)) / t ^ 2

lemma coefficientCosKernel_zero (t : ℝ) : coefficientCosKernel 0 t = 0 := by
  simp [coefficientCosKernel]

/-- The sole analytic premise is the exact powered-cosine integral evaluation. -/
lemma coefficientCosKernel_integral
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t : ℝ in Ioi 0, poweredCosKernel s t) = haagerupF s)
    {a : ℝ} (ha : 0 < a) :
    (2 / Real.pi) * (∫ t : ℝ in Ioi 0, coefficientCosKernel a t) = haagerupF (1 / a ^ 2) := by
  have he := heval (1 / a ^ 2) (by positivity)
  have hsqrt : Real.sqrt (1 / a ^ 2) = 1 / a := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hsqrt] at he
  have hk : coefficientCosKernel a = fun t => a ^ 2 * poweredCosKernel (1 / a ^ 2) (a * t) := by
    funext t
    unfold coefficientCosKernel poweredCosKernel
    rw [mul_comm a t]
    field_simp
  rw [hk, integral_const_mul, integral_comp_mul_left_Ioi _ 0 ha]
  simp only [mul_zero, smul_eq_mul]
  rw [← he]
  field_simp

lemma coefficientCosKernel_integrable
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t : ℝ in Ioi 0, poweredCosKernel s t) = haagerupF s)
    {a : ℝ} (ha : 0 ≤ a) : IntegrableOn (coefficientCosKernel a) (Ioi 0) := by
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    have hz : coefficientCosKernel 0 = 0 := funext coefficientCosKernel_zero
    rw [hz]
    exact integrable_zero ℝ ℝ (volume.restrict (Ioi 0))
  · by_contra hn
    have he := coefficientCosKernel_integral heval h
    rw [integral_undef hn, mul_zero] at he
    exact (ne_of_gt (haagerupF_pos (show 0 < 1 / a ^ 2 by positivity))) he.symm

theorem weighted_haagerup_of_integral
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t : ℝ in Ioi 0, poweredCosKernel s t) = haagerupF s)
    {n : ℕ} (a : Fin n → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : ∑ i, a i ^ 2 = 1) :
    ∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2) ≤ rademacherMean a := by
  have hi (i : Fin n) : IntegrableOn (coefficientCosKernel (a i)) (Ioi 0) :=
    coefficientCosKernel_integrable heval (ha0 i)
  have hsum : IntegrableOn (fun t => ∑ i, a i ^ 2 * coefficientCosKernel (a i) t) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmono := setIntegral_mono_on hsum (integrableOn_product_cos_kernel a) measurableSet_Ioi
    (fun t _ => weighted_cos_kernel a ha t)
  have heq : (2 / Real.pi) * (∫ t : ℝ in Ioi 0, ∑ i, a i ^ 2 * coefficientCosKernel (a i) t) =
      ∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2) := by
    rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    by_cases hz : a i = 0
    · simp [hz]
    · have he := coefficientCosKernel_integral heval (lt_of_le_of_ne (ha0 i) (Ne.symm hz))
      nlinarith only [he]
  rw [rademacher_fourier, ← heq]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

theorem haagerup_jensen
    (hconv : ConvexOn ℝ (Ioi 0) (fun u : ℝ => haagerupF (1 / u)))
    {n : ℕ} (a : Fin n → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    haagerupF (1 / ∑ i, a i ^ 4) ≤ ∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2) := by
  let supp := Finset.univ.filter (fun i : Fin n => a i ≠ 0)
  have hsum : ∑ i ∈ supp, a i ^ 2 = 1 := by
    rw [← ha]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : a i = 0 := by simpa [supp] using hi
    simp [hz]
  have h := hconv.map_sum_le (t := supp) (w := fun i => a i ^ 2) (p := fun i => a i ^ 2)
    (fun i _ => sq_nonneg _) hsum
    (fun i hi => sq_pos_of_ne_zero (Finset.mem_filter.mp hi).2)
  simp only [smul_eq_mul] at h
  have hfour : ∑ i ∈ supp, a i ^ 2 * a i ^ 2 = ∑ i, a i ^ 4 := by
    simp_rw [show ∀ x : ℝ, x ^ 2 * x ^ 2 = x ^ 4 by intro x; ring]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : a i = 0 := by simpa [supp] using hi
    simp [hz]
  have hright : ∑ i ∈ supp, a i ^ 2 * haagerupF (1 / a i ^ 2) =
      ∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : a i = 0 := by simpa [supp] using hi
    simp [hz]
  rwa [hfour, hright] at h

/-- Jensen's part of (6), with no analytic premises. Zero coefficients are
removed from the finite support before applying convexity on the positive ray. -/
theorem haagerup_jensen_unconditional {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    haagerupF (1 / ∑ i, a i ^ 4) ≤ ∑ i, a i ^ 2 * haagerupF (1 / a i ^ 2) :=
  haagerup_jensen haagerupF_inverse_convex a ha

/-- The full fourth-moment consequence of (6), conditional only on the exact
scalar powered-cosine integral evaluation. -/
theorem haagerup_fourth_moment_of_integral
    (heval : ∀ s : ℝ, 0 < s → (2 / (Real.pi * Real.sqrt s)) *
      (∫ t : ℝ in Ioi 0, poweredCosKernel s t) = haagerupF s)
    {n : ℕ} (a : Fin n → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : ∑ i, a i ^ 2 = 1) :
    haagerupF (1 / ∑ i, a i ^ 4) ≤ rademacherMean a :=
  (haagerup_jensen_unconditional a ha).trans (weighted_haagerup_of_integral heval a ha0 ha)

end Szarek
