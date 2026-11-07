import Definitions
import GammaSpecial
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
namespace Szarek

lemma haagerupF_pos {s : ℝ} (hs : 0 < s) : 0 < haagerupF s := by
  unfold haagerupF
  positivity

lemma haagerupF_scaled {s : ℝ} (hs : 0 < s) :
    haagerupF s * Real.sqrt s =
      2 / Real.sqrt Real.pi * (Real.Gamma ((s + 1) / 2) / Real.Gamma (s / 2)) := by
  unfold haagerupF
  rw [Real.sqrt_mul Real.pi_pos.le]
  have hsq : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  field_simp

lemma haagerupF_scaled_step {s : ℝ} (hs : 0 < s) :
    haagerupF (s + 2) * Real.sqrt (s + 2) * s =
      haagerupF s * Real.sqrt s * (s + 1) := by
  rw [haagerupF_scaled (by linarith), haagerupF_scaled hs]
  have hnum : Real.Gamma ((s + 2 + 1) / 2) =
      ((s + 1) / 2) * Real.Gamma ((s + 1) / 2) := by
    rw [show (s + 2 + 1) / 2 = (s + 1) / 2 + 1 by ring]
    exact Real.Gamma_add_one (by linarith)
  have hden : Real.Gamma ((s + 2) / 2) = (s / 2) * Real.Gamma (s / 2) := by
    rw [show (s + 2) / 2 = s / 2 + 1 by ring]
    exact Real.Gamma_add_one (by linarith)
  rw [hnum, hden]
  have hg : Real.Gamma (s / 2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

lemma haagerupF_lt_step {s : ℝ} (hs : 0 < s) : haagerupF s < haagerupF (s + 2) := by
  have he := haagerupF_scaled_step hs
  have hF := haagerupF_pos hs
  have hF' := haagerupF_pos (show 0 < s + 2 by linarith)
  have hr := Real.sqrt_pos.mpr hs
  have hr' := Real.sqrt_pos.mpr (show 0 < s + 2 by linarith)
  have hr2 := Real.sq_sqrt hs.le
  have hr2' := Real.sq_sqrt (show 0 ≤ s + 2 by linarith)
  have hcoeff : Real.sqrt (s + 2) * s < Real.sqrt s * (s + 1) := by
    have ha : 0 < Real.sqrt (s + 2) * s := mul_pos hr' hs
    have hb : 0 < Real.sqrt s * (s + 1) := mul_pos hr (by linarith)
    have hid : (Real.sqrt s * (s + 1)) ^ 2 - (Real.sqrt (s + 2) * s) ^ 2 = s := by
      rw [mul_pow, mul_pow, hr2, hr2']
      ring
    nlinarith only [ha, hb, hid, hs]
  have hmul := mul_lt_mul_of_pos_left hcoeff hF
  have hd : 0 < Real.sqrt (s + 2) * s := mul_pos hr' hs
  have h : haagerupF s * (Real.sqrt (s + 2) * s) <
      haagerupF (s + 2) * (Real.sqrt (s + 2) * s) := by nlinarith only [hmul, he]
  exact (mul_lt_mul_iff_of_pos_right hd).mp h

lemma differentiableAt_haagerupF {s : ℝ} (hs : 0 < s) :
    DifferentiableAt ℝ haagerupF s := by
  have hg₁ : DifferentiableAt ℝ Real.Gamma ((s + 1) / 2) :=
    Real.differentiableAt_Gamma (fun m => by have hm := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
  have hg₂ : DifferentiableAt ℝ Real.Gamma (s / 2) :=
    Real.differentiableAt_Gamma (fun m => by have hm := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)
  have hgs₁ : DifferentiableAt ℝ (fun t : ℝ => Real.Gamma ((t + 1) / 2)) s :=
    DifferentiableAt.comp s (f := fun t : ℝ => (t + 1) / 2) (g := Real.Gamma) hg₁ (by fun_prop)
  have hgs₂ : DifferentiableAt ℝ (fun t : ℝ => Real.Gamma (t / 2)) s :=
    DifferentiableAt.comp s (f := fun t : ℝ => t / 2) (g := Real.Gamma) hg₂ (by fun_prop)
  unfold haagerupF
  apply DifferentiableAt.mul
  · apply DifferentiableAt.div (by fun_prop)
    · apply DifferentiableAt.sqrt (by fun_prop)
      positivity
    · exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hs))
  · exact hgs₁.div hgs₂ (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))

lemma continuousOn_haagerupF : ContinuousOn haagerupF (Set.Ioi 0) :=
  fun _s hs => (differentiableAt_haagerupF hs).continuousAt.continuousWithinAt

lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hf : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    exact (Real.tanh_eq_sinh_div_cosh y).symm
  rw [hf] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

lemma tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd (y : ℝ) : HasDerivAt (fun t => t - Real.tanh t) (Real.tanh y ^ 2) y := by
    convert (hasDerivAt_id y).sub (hasDerivAt_tanh y) using 1
    · rfl
    · ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun y => sq_nonneg (Real.tanh y))
  have hh := hm hx
  simpa using hh

lemma tanh_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.tanh x := by
  have hd (y : ℝ) : HasDerivAt (fun t => Real.tanh t - t + t ^ 3 / 3)
      (y ^ 2 - Real.tanh y ^ 2) y := by
    convert ((hasDerivAt_tanh y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 3) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : MonotoneOn (fun t => Real.tanh t - t + t ^ 3 / 3) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)).continuousOn
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy)
      have ht := tanh_le_self hy0
      have ht0 : 0 ≤ Real.tanh y := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr hy0) (Real.cosh_pos y).le
      nlinarith
  have hh := hm (by simp) hx hx
  simp only [Real.tanh_zero, sub_self, zero_pow (by norm_num : 3 ≠ 0), zero_div, add_zero] at hh
  linarith

lemma monotone_tanh : Monotone Real.tanh :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_tanh (fun x => le_of_lt (sub_pos.mpr (Real.tanh_sq_lt_one x)))

lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  simpa only [Real.tanh_zero] using monotone_tanh hx

lemma tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

lemma concaveOn_tanh : ConcaveOn ℝ (Set.Ici 0) Real.tanh := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)).continuousOn
  · intro x hx
    exact (hasDerivAt_tanh x).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [(hasDerivAt_tanh x).deriv, (hasDerivAt_tanh y).deriv]
    have h := monotone_tanh hxy
    have hx0 := tanh_nonneg (show 0 ≤ x from interior_subset hx)
    have hy0 := tanh_nonneg (show 0 ≤ y from interior_subset hy)
    nlinarith

lemma tanh_div_antitone : AntitoneOn (fun x : ℝ => Real.tanh x / x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hm : AntitoneOn (slope Real.tanh 0) (Set.Ici 0 \ {0}) :=
    concaveOn_tanh.slope_anti (by simp : (0 : ℝ) ∈ Set.Ici 0)
  have h := hm
    (show x ∈ Set.Ici 0 \ {0} from ⟨show 0 ≤ x from (show 0 < x from hx).le, by simpa using ne_of_gt hx⟩)
    (show y ∈ Set.Ici 0 \ {0} from ⟨show 0 ≤ y from (show 0 < y from hy).le, by simpa using ne_of_gt hy⟩) hxy
  simpa [slope, Real.tanh_zero, div_eq_mul_inv, mul_comm] using h

open MeasureTheory Set

lemma integrableOn_pow_exp {s : ℝ} (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-s * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := 1) (b := s) (by have hn := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) (by norm_num) hs
  simpa using h

lemma integral_pow_exp {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-s * t)) = (n.factorial : ℝ) / s ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := s) (by positivity) hs
  have hp : (1 / s) ^ ((n : ℝ) + 1) = (1 / s) ^ (n + 1) := by
    rw [← Nat.cast_add_one, Real.rpow_natCast]
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial, hp] at h
  simpa [Real.rpow_natCast, neg_mul, div_pow, mul_comm, div_eq_mul_inv] using h

lemma integrableOn_exp_tanh {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * Real.tanh (t / 2)) (Ioi 0) := by
  have hcont : Continuous Real.tanh :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_tanh t).continuousAt)
  refine (exp_neg_integrableOn_Ioi 0 hs).mono' (by fun_prop) ?_
  filter_upwards [] with t
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one (t / 2)).le (Real.exp_pos (-s * t)).le

lemma laplace_tanh_lower {s : ℝ} (hs : 0 < s) :
    1 / (4 * s ^ 2) - 1 / (8 * s ^ 4) ≤
      (1 / 2 : ℝ) * ∫ t : ℝ in Ioi 0, Real.exp (-s * t) * Real.tanh (t / 2) := by
  have h₁ := (integrableOn_pow_exp hs 1).div_const 2
  have h₃ := (integrableOn_pow_exp hs 3).div_const 24
  have he : (fun t : ℝ => Real.exp (-s * t) * (t / 2 - (t / 2) ^ 3 / 3)) =
      (fun t : ℝ => (t ^ 1 * Real.exp (-s * t)) / 2 - (t ^ 3 * Real.exp (-s * t)) / 24) := by
    funext t
    ring
  have hpoly : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * (t / 2 - (t / 2) ^ 3 / 3)) (Ioi 0) := by
    rw [he]
    exact h₁.sub h₃
  have hi : (∫ t : ℝ in Ioi 0, Real.exp (-s * t) * (t / 2 - (t / 2) ^ 3 / 3)) =
      1 / (2 * s ^ 2) - 1 / (4 * s ^ 4) := by
    rw [he, integral_sub h₁ h₃, integral_div, integral_div, integral_pow_exp hs 1,
      integral_pow_exp hs 3]
    norm_num
    ring
  have hmono := setIntegral_mono_on hpoly (integrableOn_exp_tanh hs) measurableSet_Ioi
    (fun t ht => mul_le_mul_of_nonneg_left (tanh_cubic_lower (div_nonneg (show 0 ≤ t from le_of_lt ht) (by norm_num)))
      (Real.exp_pos (-s * t)).le)
  rw [hi] at hmono
  have heq : 1 / (4 * s ^ 2) - 1 / (8 * s ^ 4) =
      (1 / 2 : ℝ) * (1 / (2 * s ^ 2) - 1 / (4 * s ^ 4)) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hmono (by norm_num)

lemma laplace_tanh_pos {s : ℝ} (hs : 0 < s) :
    0 < ∫ t : ℝ in Ioi 0, Real.exp (-s * t) * Real.tanh (t / 2) := by
  have hsupp : (Function.support (fun t : ℝ => Real.exp (-s * t) * Real.tanh (t / 2))) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro t ht
    exact (mul_pos (Real.exp_pos _) (tanh_pos (div_pos ht (by norm_num)))).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hsupp, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · refine Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) ?_
    intro t ht
    exact (mul_pos (Real.exp_pos _) (tanh_pos (div_pos ht (by norm_num)))).le
  · exact integrableOn_exp_tanh hs

lemma deriv_log_haagerupF_eq {s : ℝ} (hs : 0 < s) :
    deriv (fun x => Real.log (haagerupF x)) s = deriv haagerupF s / haagerupF s :=
  ((differentiableAt_haagerupF hs).hasDerivAt.log (ne_of_gt (haagerupF_pos hs))).deriv

/-- The remaining scalar calculus step, with its log-derivative premise explicit. -/
lemma scalar_bound_of_log_derivative_lower
    (hlog : ∀ s : ℝ, 4 ≤ s → 1 / (4 * s ^ 2) - 1 / (8 * s ^ 4) ≤
      deriv haagerupF s / haagerupF s) :
    ∀ s : ℝ, 4 ≤ s → 19 / 24 - 1 / (6 * s) ≤ haagerupF s := by
  have hdpos (s : ℝ) (hs : 4 ≤ s) : 0 ≤ deriv haagerupF s := by
    have hs0 : 0 < s := by linarith
    have hF := haagerupF_pos hs0
    have h := (le_div_iff₀ hF).mp (hlog s hs)
    have hl : 0 ≤ 1 / (4 * s ^ 2) - 1 / (8 * s ^ 4) := by
      field_simp
      nlinarith [sq_nonneg s]
    exact (mul_nonneg hl hF.le).trans h
  have hmono : MonotoneOn haagerupF (Ici 4) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 4)
    · exact continuousOn_haagerupF.mono (by intro s hs; have hs' : 4 ≤ s := hs; exact (by linarith : 0 < s))
    · intro s hs
      exact (differentiableAt_haagerupF (by have hh : 4 ≤ s := interior_subset hs; linarith)).hasDerivAt.hasDerivWithinAt
    · intro s hs
      exact hdpos s (interior_subset hs)
  have hFbound (s : ℝ) (hs : 4 ≤ s) : (3 : ℝ) / 4 ≤ haagerupF s := by
    rw [← haagerupF_four]
    exact hmono (by simp) hs hs
  have hderiv (s : ℝ) (hs : 4 ≤ s) : 1 / (6 * s ^ 2) ≤ deriv haagerupF s := by
    have hs0 : 0 < s := by linarith
    have hF := haagerupF_pos hs0
    have h := (le_div_iff₀ hF).mp (hlog s hs)
    have hl : 0 ≤ 1 / (4 * s ^ 2) - 1 / (8 * s ^ 4) := by
      field_simp
      nlinarith [sq_nonneg s]
    have hmul := mul_le_mul_of_nonneg_left (hFbound s hs) hl
    have hpoly : 1 / (6 * s ^ 2) ≤
        (1 / (4 * s ^ 2) - 1 / (8 * s ^ 4)) * (3 / 4) := by
      field_simp
      nlinarith [sq_nonneg s]
    exact hpoly.trans (hmul.trans h)
  have hd (s : ℝ) (hs : 4 ≤ s) : HasDerivAt
      (fun x => haagerupF x + (1 / 6 : ℝ) * x⁻¹)
      (deriv haagerupF s - 1 / (6 * s ^ 2)) s := by
    have hs0 : s ≠ 0 := by linarith
    have h := (differentiableAt_haagerupF (by linarith)).hasDerivAt.add
      (((hasDerivAt_id s).inv hs0).const_mul (1 / 6 : ℝ))
    convert h using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring
  have hgmono : MonotoneOn (fun x => haagerupF x + (1 / 6 : ℝ) * x⁻¹) (Ici 4) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 4)
    · intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      exact sub_nonneg.mpr (hderiv s (interior_subset hs))
  intro s hs
  have h := hgmono (by simp) hs hs
  dsimp only at h
  rw [haagerupF_four] at h
  have heq : (1 / 6 : ℝ) * s⁻¹ = 1 / (6 * s) := by ring
  rw [heq] at h
  norm_num at h
  linarith

end Szarek
