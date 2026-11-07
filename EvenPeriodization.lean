import Periodization
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace Szarek

lemma even_apply_abs {f : ℝ → ℝ} (hf : Function.Even f) (x : ℝ) : f |x| = f x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, hf]

lemma integral_even_eq_two_Ioi {f : ℝ → ℝ} (hf : Function.Even f) :
    (∫ x, f x) = 2 * ∫ x in Ioi 0, f x := by
  simpa only [even_apply_abs hf] using (integral_comp_abs (f := f))

lemma integral_even_symmetric {f : ℝ → ℝ} (hf : Function.Even f) {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioc (-a) a, f x) = 2 * ∫ x in (0 : ℝ)..a, f x := by
  let g := (Ioo (-a) a).indicator f
  have hg : Function.Even g := by
    intro x
    simp only [g, Set.indicator_apply, mem_Ioo]
    have he : (-a < -x ∧ -x < a) ↔ (-a < x ∧ x < a) := by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simp only [he, hf x]
  have hi := integral_even_eq_two_Ioi hg
  change (∫ x, (Ioo (-a) a).indicator f x) =
    2 * ∫ x in Ioi 0, (Ioo (-a) a).indicator f x at hi
  rw [integral_indicator measurableSet_Ioo, setIntegral_indicator measurableSet_Ioo] at hi
  have hinter : Ioi (0 : ℝ) ∩ Ioo (-a) a = Ioo 0 a := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨hx, _, hxa⟩
      exact ⟨hx, hxa⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨hx, by linarith, hxa⟩
  rw [hinter] at hi
  rw [integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le ha.le,
    integral_Ioc_eq_integral_Ioo]
  exact hi

lemma periodization_even {T : ℝ} {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (fun t : ℝ => ∑' n : ℤ, f ((n : ℝ) * T + t)) := by
  intro t
  calc
    _ = ∑' n : ℤ, f (((-n : ℤ) : ℝ) * T + t) := by
      apply tsum_congr
      intro n
      rw [Int.cast_neg]
      have he : -(n : ℝ) * T + t = -((n : ℝ) * T + -t) := by ring
      rw [he, hf]
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => f ((n : ℝ) * T + t))

lemma integral_periodization_even_int {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f) :
    (∫ x in Ioi 0, f x) =
      ∫ t in (0 : ℝ)..T / 2, ∑' n : ℤ, f ((n : ℝ) * T + t) := by
  have h := integral_periodization hT (-T / 2) hf
  rw [show -T / 2 + T = T / 2 by ring] at h
  rw [integral_even_eq_two_Ioi heven] at h
  have hs := integral_even_symmetric (periodization_even (T := T) heven)
    (show 0 < T / 2 by positivity)
  rw [show -(T / 2) = -T / 2 by ring] at hs
  rw [hs] at h
  linarith

lemma tsum_int_pair_shifts {T t : ℝ} {f : ℝ → ℝ}
    (hf : Summable (fun n : ℤ => f ((n : ℝ) * T + t))) :
    (∑' n : ℤ, f ((n : ℝ) * T + t)) =
      f t + ∑' n : ℕ, (f (t + (n + 1) * T) + f (t - (n + 1) * T)) := by
  let g : ℤ → ℝ := fun n => f ((n : ℝ) * T + t)
  have hf' : Summable g := hf
  have hp : Summable (fun n : ℕ => g (n + 1)) := hf'.comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ) + 1) by intro i j h; exact_mod_cast (add_right_cancel h : (i : ℤ) = j))
  have hn : Summable (fun n : ℕ => g (-(n + 1))) := hf'.comp_injective (show Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) by intro i j h; exact_mod_cast (add_right_cancel (neg_injective h) : (i : ℤ) = j))
  rw [show (∑' n : ℤ, f ((n : ℝ) * T + t)) = ∑' n : ℤ, g n by rfl,
    tsum_of_add_one_of_neg_add_one hp hn]
  have he : (∑' n : ℕ, g (n + 1)) + g 0 + ∑' n : ℕ, g (-(n + 1)) =
      g 0 + ∑' n : ℕ, (g (n + 1) + g (-(n + 1))) := by
    rw [hp.tsum_add hn]
    ring
  rw [he]
  simp only [g, Int.cast_zero, zero_mul, zero_add, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Int.cast_neg]
  congr 1
  apply tsum_congr
  intro n
  congr 2 <;> ring

/-- Fold an even integrable function into one half of a fundamental interval.
Summability is required only on the open interior, so singular endpoint values do not matter. -/
theorem integral_periodization_even {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    (hsum : ∀ t ∈ Ioo 0 (T / 2), Summable (fun n : ℤ => f ((n : ℝ) * T + t))) :
    (∫ x in Ioi 0, f x) = ∫ t in (0 : ℝ)..T / 2,
      (f t + ∑' n : ℕ, (f (t + (n + 1) * T) + f (t - (n + 1) * T))) := by
  rw [integral_periodization_even_int hT hf heven]
  rw [intervalIntegral.integral_of_le (by positivity : 0 ≤ T / 2),
    intervalIntegral.integral_of_le (by positivity : 0 ≤ T / 2),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact tsum_int_pair_shifts (hsum t ht)

#print axioms Szarek.integral_periodization_even
end Szarek
