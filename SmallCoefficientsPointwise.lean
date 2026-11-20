module

public import CosineGaussian
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators
namespace Szarek

/-- Initial-interval comparison for the separated largest coefficient in Lemma 2. -/
lemma head_tail_cosine_bound {m : ℕ} (x y : ℝ) (b : Fin m → ℝ)
    (hy : 0 < y) (hb0 : ∀ i, 0 ≤ b i) (hby : ∀ i, b i ≤ y)
    (hs : ∑ i, (b i) ^ 2 = 1 - x ^ 2)
    (t : ℝ) (ht : 0 ≤ t) (htcut : t ≤ Real.pi / (2 * y)) :
    (∏ i : Fin (m + 1), Real.cos ((Fin.cons (α := fun _ : Fin (m + 1) => ℝ) x b) i * t)) ≤
      max (Real.cos (x * t)) 0 * Real.exp (-((1 - x ^ 2) * t ^ 2) / 2) := by
  have hyt : y * t ≤ Real.pi / 2 := by
    have ht' : t ≤ (Real.pi / 2) / y := by
      convert htcut using 1; ring
    simpa only [mul_comm] using (le_div_iff₀ hy).mp ht'
  have hcut : ∀ i ∈ (Finset.univ : Finset (Fin m)), b i * t ≤ Real.pi / 2 := by
    intro i hi
    exact (mul_le_mul_of_nonneg_right (hby i) ht).trans hyt
  have hnonneg : 0 ≤ ∏ i, Real.cos (b i * t) := by
    apply Finset.prod_nonneg
    intro i hi
    exact cos_nonneg_first_quadrant (mul_nonneg (hb0 i) ht) (hcut i hi)
  have htail : (∏ i, Real.cos (b i * t)) ≤
      Real.exp (-((1 - x ^ 2) * t ^ 2) / 2) := by
    simpa only [hs, neg_mul] using
      prod_cos_le_gaussian Finset.univ b t ht (fun i _ => hb0 i) hcut
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  calc
    _ ≤ max (Real.cos (x * t)) 0 * ∏ i, Real.cos (b i * t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hnonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (le_max_right _ _)

#print axioms Szarek.head_tail_cosine_bound
end Szarek
