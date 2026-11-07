import SmallCoefficientsBase
import ScaledGaussianTail
import ScaledCosineTail

open MeasureTheory Set
open scoped BigOperators

namespace Szarek

theorem smaller_coefficients_eq22 {m : ℕ} (x y : ℝ) (b : Fin m → ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 < y) (hu : 0 < 1 - x ^ 2)
    (hb0 : ∀ i, 0 ≤ b i) (hby : ∀ i, b i ≤ y)
    (hsum : ∑ i, b i ^ 2 = 1 - x ^ 2)
    (hcomp : Real.sqrt (2 / Real.pi) ≤ (2 / Real.pi) *
      ∫ t : ℝ in Ioi 0, gaussianComparisonKernel x t) :
    Real.sqrt (2 / Real.pi) - (2 / Real.pi) *
      ∑ i, (b i ^ 2 / (1 - x ^ 2)) *
        (∫ t : ℝ in Ioi (Real.pi / (2 * y)), tailPowerKernel (1 - x ^ 2) (b i) t) ≤
      rademacherMean (Fin.cons x b) := by
  let u := 1 - x ^ 2
  let R := Real.pi / (2 * y)
  let P := fun t : ℝ => (1 - Real.cos (x * t) * ∏ i, Real.cos (b i * t)) / t ^ 2
  let E := fun t : ℝ => ∑ i, (b i ^ 2 / u) * tailPowerKernel u (b i) t
  have hR : 0 < R := by dsimp [R]; positivity
  have hP : IntegrableOn P (Ioi 0) := by
    have h := integrableOn_product_cos_kernel (Fin.cons x b)
    simpa only [P, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_comm] using h
  have hE : IntegrableOn E (Ioi R) :=
    integrable_finsetSum _ (fun i _ => (tailPowerKernel_integrable hu.le hR (b i)).const_mul _)
  have hEi : Integrable ((Ioi R).indicator E) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hE
  have hpoint (t : ℝ) (ht : t ∈ Ioi 0) :
      gaussianComparisonKernel x t ≤ P t + (Ioi R).indicator E t := by
    by_cases htR : t ≤ R
    · rw [indicator_of_notMem (show t ∉ Ioi R from not_lt.mpr htR), add_zero]
      have h := small_interval_cos_comparison b hy hsum hb0 hby x ht.le htR
      unfold gaussianComparisonKernel P
      apply div_le_div_of_nonneg_right _ (sq_nonneg t)
      simpa only [neg_mul] using sub_le_sub_left h 1
    · rw [indicator_of_mem (show t ∈ Ioi R from lt_of_not_ge htR)]
      have h := head_tail_cos_le_weighted b hu hsum x t
      have hc : 0 ≤ max (Real.cos (x * t)) 0 * Real.exp (-u * t ^ 2 / 2) := by positivity
      have hnum : 1 - max (Real.cos (x * t)) 0 * Real.exp (-u * t ^ 2 / 2) ≤
          (1 - Real.cos (x * t) * ∏ i, Real.cos (b i * t)) +
            ∑ i, (b i ^ 2 / u) * |Real.cos (b i * t)| ^ (u / b i ^ 2) := by
        dsimp [u] at *
        linarith
      have hd := div_le_div_of_nonneg_right hnum (sq_nonneg t)
      simpa only [gaussianComparisonKernel, P, E, tailPowerKernel, add_div,
        Finset.sum_div, mul_div_assoc, neg_mul] using hd
  have hmono := setIntegral_mono_on (integrable_gaussianComparisonKernel x hx hx1).integrableOn
    (hP.add hEi.integrableOn) measurableSet_Ioi hpoint
  simp only [Pi.add_apply] at hmono
  rw [integral_add hP hEi.integrableOn, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_right hR.le, integral_finsetSum _ (fun i _ =>
      (tailPowerKernel_integrable hu.le hR (b i)).const_mul _)] at hmono
  simp_rw [integral_const_mul] at hmono
  have hmean : rademacherMean (Fin.cons x b) = (2 / Real.pi) * ∫ t : ℝ in Ioi 0, P t := by
    rw [rademacher_fourier]
    congr 2
    funext t
    simp only [P, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_comm]
  rw [hmean]
  have hh := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 / Real.pi by positivity)
  dsimp [E, u, R] at hh
  linarith

theorem smaller_coefficients_from_individual_tails {m : ℕ} (x y : ℝ) (b : Fin m → ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 < y) (hu : 0 < 1 - x ^ 2)
    (hb0 : ∀ i, 0 ≤ b i) (hby : ∀ i, b i ≤ y)
    (hsum : ∑ i, b i ^ 2 = 1 - x ^ 2) (hscale : 3 * y ^ 2 ≤ 1 - x ^ 2)
    (hcomp : Real.sqrt (2 / Real.pi) ≤ (2 / Real.pi) *
      ∫ t : ℝ in Ioi 0, gaussianComparisonKernel x t)
    (htail : ∀ i, 0 < b i →
      (∫ t : ℝ in Ioi (Real.pi / (2 * y)), tailPowerKernel (1 - x ^ 2) (b i) t) ≤
        (∫ t : ℝ in Ioi (Real.pi / (2 * y)), Real.exp (-(1 - x ^ 2) * t ^ 2 / 2) / t ^ 2) +
          (1 / 3 : ℝ) * Real.sqrt (Real.pi / 2) * (b i ^ 2 / Real.sqrt (1 - x ^ 2))) :
    Real.sqrt (2 / Real.pi) * (1 - (7 / 20 : ℝ) * y ^ 2 / Real.sqrt (1 - x ^ 2)) ≤
      rademacherMean (Fin.cons x b) := by
  let u := 1 - x ^ 2
  let G := ∫ t : ℝ in Ioi (Real.pi / (2 * y)), Real.exp (-u * t ^ 2 / 2) / t ^ 2
  let C := (1 / 3 : ℝ) * Real.sqrt (Real.pi / 2) / Real.sqrt u
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hweights : ∑ i, b i ^ 2 / u = 1 := by
    rw [← Finset.sum_div, hsum]
    exact div_self hu.ne'
  have hfour : ∑ i, (b i ^ 2 / u) * b i ^ 2 ≤ y ^ 2 := by
    calc
      _ ≤ ∑ i, (b i ^ 2 / u) * y ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sq_le_sq₀ (hb0 i) hy.le).mpr (hby i)
      _ = _ := by rw [← Finset.sum_mul, hweights, one_mul]
  have hsumtail : ∑ i, (b i ^ 2 / u) *
        (∫ t : ℝ in Ioi (Real.pi / (2 * y)), tailPowerKernel u (b i) t) ≤ G + C * y ^ 2 := by
    calc
      _ ≤ ∑ i, (b i ^ 2 / u) * (G + C * b i ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hz : b i = 0
        · simp [hz]
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          convert htail i (lt_of_le_of_ne (hb0 i) (Ne.symm hz)) using 1
          dsimp [G, C, u]
          ring
      _ = G + C * ∑ i, (b i ^ 2 / u) * b i ^ 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hweights, one_mul]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hfour hC)
  have h22 := smaller_coefficients_eq22 x y b hx hx1 hy hu hb0 hby hsum hcomp
  have herror := scaled_gaussian_error_bound hu hy hscale
  have hscaled := mul_le_mul_of_nonneg_left hsumtail (show 0 ≤ 2 / Real.pi by positivity)
  have hnorm : (2 / Real.pi) * (C * y ^ 2) =
      Real.sqrt (2 / Real.pi) * (y ^ 2 / Real.sqrt u) / 3 := by
    calc
      _ = ((2 / Real.pi) * Real.sqrt (Real.pi / 2)) * (y ^ 2 / Real.sqrt u) / 3 := by dsimp [C]; ring
      _ = _ := by rw [gaussian_normalization]
  rw [mul_add, hnorm] at hscaled
  change (2 / Real.pi) * G ≤ Real.sqrt (2 / Real.pi) * (y ^ 2 / Real.sqrt u) / 60 at herror
  change Real.sqrt (2 / Real.pi) - (2 / Real.pi) *
    ∑ i, (b i ^ 2 / u) * (∫ t : ℝ in Ioi (Real.pi / (2 * y)), tailPowerKernel u (b i) t) ≤ _ at h22
  have he : Real.sqrt (2 / Real.pi) * (1 - (7 / 20 : ℝ) * y ^ 2 / Real.sqrt (1 - x ^ 2)) =
      Real.sqrt (2 / Real.pi) -
        (7 / 20 : ℝ) * (Real.sqrt (2 / Real.pi) * (y ^ 2 / Real.sqrt u)) := by dsimp [u]; ring
  rw [he]
  linarith only [h22, herror, hscaled]

/-- Paper Lemma 2 for a head coefficient and its ordered nonnegative tail.
The two remaining periodic integral inputs are stated explicitly. -/
theorem smaller_coefficients_of_cosine_integrals {m : ℕ} (x y : ℝ) (b : Fin m → ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 < y)
    (hb0 : ∀ i, 0 ≤ b i) (hby : ∀ i, b i ≤ y)
    (hsum : ∑ i, b i ^ 2 = 1 - x ^ 2) (hscale : 3 * y ^ 2 ≤ 1 - x ^ 2)
    (habs : (∫ t : ℝ in Ioi 0, absoluteCosKernel t) = 1)
    (hcos : ∀ s : ℝ, (1 : ℝ) / 2 < s →
      (∫ t : ℝ in Ioi (Real.pi / 2), |Real.cos t| ^ s / t ^ 2) ≤
        (1 / 3 : ℝ) * Real.sqrt (Real.pi / (2 * s))) :
    Real.sqrt (2 / Real.pi) * (1 - (7 / 20 : ℝ) * y ^ 2 / Real.sqrt (1 - x ^ 2)) ≤
      rademacherMean (Fin.cons x b) := by
  have hu : 0 < 1 - x ^ 2 := lt_of_lt_of_le (by positivity) hscale
  apply smaller_coefficients_from_individual_tails x y b hx hx1 hy hu hb0 hby hsum hscale
    (lemma3_of_absoluteCos x hx hx1 habs)
  intro i hi
  convert scaled_cosine_tail_bound hi (hby i) hscale hcos using 1
  ring

theorem lemma2_of_cosine_integrals
    (habs : (∫ t : ℝ in Ioi 0, absoluteCosKernel t) = 1)
    (hcos : ∀ s : ℝ, (1 : ℝ) / 2 < s →
      (∫ t : ℝ in Ioi (Real.pi / 2), |Real.cos t| ^ s / t ^ 2) ≤
        (1 / 3 : ℝ) * Real.sqrt (Real.pi / (2 * s)))
    (n : ℕ) (a : Fin (n + 2) → ℝ) (ha : orderedUnit a)
    (ha1 : 0 < a 1) (hscale : a 0 ^ 2 + 3 * a 1 ^ 2 ≤ 1) :
    Real.sqrt (2 / Real.pi) *
      (1 - (7 : ℝ) / 20 * (a 1 ^ 2 / Real.sqrt (1 - a 0 ^ 2))) ≤ rademacherMean a := by
  have hx1 : a 0 ≤ 1 := by nlinarith [sq_nonneg (a 1), ha.2.1 0]
  have hsum : ∑ i, Fin.tail a i ^ 2 = 1 - a 0 ^ 2 := by
    have h := ha.2.2
    rw [Fin.sum_univ_succ] at h
    change a 0 ^ 2 + ∑ i, Fin.tail a i ^ 2 = 1 at h
    linarith
  have hby (i : Fin (n + 1)) : Fin.tail a i ≤ a 1 := by
    exact ha.1 (show (1 : Fin (n + 2)) ≤ i.succ by
      change 1 ≤ i.val + 1
      omega)
  have h := smaller_coefficients_of_cosine_integrals (a 0) (a 1) (Fin.tail a)
    (ha.2.1 0) hx1 ha1 (fun i => ha.2.1 i.succ) hby hsum
    (by linarith) habs hcos
  rw [Fin.cons_self_tail] at h
  convert h using 1
  ring

end Szarek
