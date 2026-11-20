module

public import Definitions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

@[expose] public section

open scoped Nat

namespace Szarek

theorem haagerupF_even (m : ℕ) (hm : 1 ≤ m) :
    haagerupF (2 * (m : ℝ)) =
      Real.sqrt (2 * (m : ℝ)) * (Nat.choose (2 * m) m : ℝ) / (2 : ℝ) ^ (2 * m) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hfact : (m.factorial : ℝ) = (m : ℝ) * Real.Gamma m := by
    rw [← Real.Gamma_nat_eq_factorial, Real.Gamma_add_one (ne_of_gt hm0)]
  have hdf : (2 * m).factorial = 2 ^ m * m.factorial * (2 * m - 1)‼ := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * m), Nat.doubleFactorial_two_mul] at h
    exact h
  have hchoose : (Nat.choose (2 * m) m : ℝ) * (m.factorial : ℝ) =
      (2 : ℝ) ^ m * ((2 * m - 1)‼ : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * m) (k := m) (by omega)
    rw [show 2 * m - m = m by omega, hdf] at h
    have h' : (Nat.choose (2 * m) m : ℝ) * m.factorial * m.factorial =
        (2 : ℝ) ^ m * m.factorial * ((2 * m - 1)‼ : ℝ) := by exact_mod_cast h
    have hf0 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    apply (mul_right_cancel₀ hf0)
    nlinarith only [h']
  have hGamma : Real.Gamma (m : ℝ) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hm0)
  have hratio : Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma m =
      (m : ℝ) * (Nat.choose (2 * m) m : ℝ) * Real.sqrt Real.pi /
        (2 : ℝ) ^ (2 * m) := by
    rw [Real.Gamma_nat_add_half,
      show (2 : ℝ) ^ (2 * m) = (2 : ℝ) ^ m * (2 : ℝ) ^ m by rw [Nat.two_mul, pow_add]]
    rw [hfact] at hchoose
    field_simp
    nlinarith only [hchoose]
  have hs0 : Real.sqrt (2 * (m : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hpi0 : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * (m : ℝ) by positivity)
  unfold haagerupF
  rw [show (2 * (m : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 by ring,
    show 2 * (m : ℝ) / 2 = m by ring, hratio,
    Real.sqrt_mul Real.pi_pos.le]
  field_simp
  nlinarith only [hs2]

end Szarek
