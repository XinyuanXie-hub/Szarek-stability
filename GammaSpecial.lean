module

public import Definitions
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Szarek

theorem haagerupF_four : haagerupF 4 = (3 : ℝ) / 4 := by
  have hhalf : Real.Gamma ((3 : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
    have h := Real.Gamma_add_one (s := (1 : ℝ) / 2) (by norm_num)
    norm_num [Real.Gamma_one_half_eq] at h
    linarith
  have hfive : Real.Gamma ((5 : ℝ) / 2) = 3 * Real.sqrt Real.pi / 4 := by
    have h := Real.Gamma_add_one (s := (3 : ℝ) / 2) (by norm_num)
    norm_num [hhalf] at h
    linarith
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  unfold haagerupF
  norm_num [hfive, Real.Gamma_two, Real.sqrt_mul Real.pi_pos.le]
  field_simp [hs]

end Szarek
