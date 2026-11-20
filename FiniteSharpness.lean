module

public import Definitions
public import SharpConstant
public import Mathlib.Tactic.FinCases

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Szarek

lemma sum_signs_succ {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ ε, f ε) = ∑ b : Bool, ∑ ε : Fin n → Bool, f (Fin.cons b ε) := by
  calc
    _ = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm f _
        (fun ε => by
          change f ε = f (Fin.cons (ε 0) (Fin.tail ε))
          rw [Fin.cons_self_tail])
    _ = _ := Fintype.sum_prod_type _

lemma fourEqual_four_unit : orderedUnit (fourEqual 4) := by
  have h : fourEqual 4 = fun _ => (1 : ℝ) / 2 := by
    funext i
    simp [fourEqual, i.isLt]
  rw [h]
  constructor
  · intro i j hij
    rfl
  constructor
  · intro i
    norm_num
  · norm_num [Fin.sum_univ_succ]

lemma cons_two {n : ℕ} (b : Bool) (f : Fin (n + 2) → Bool) :
    Fin.cons (α := fun _ : Fin (n + 3) => Bool) b f (2 : Fin (n + 3)) = f 1 := rfl

lemma cons_three {n : ℕ} (b : Bool) (f : Fin (n + 3) → Bool) :
    Fin.cons (α := fun _ : Fin (n + 4) => Bool) b f (3 : Fin (n + 4)) = f 2 := rfl

lemma fourEqual_four_mean : rademacherMean (fourEqual 4) = 3 / 4 := by
  norm_num [rademacherMean, sum_signs_succ, Fin.sum_univ_succ, fourEqual,
    Fintype.sum_bool, Fin.cons_zero, Fin.cons_succ, Fin.cons_one, cons_two, cons_three]

lemma fourEqual_four_distance : extremizerDistance (fourEqual 4) = Real.sqrt (2 - Real.sqrt 2) := by
  unfold extremizerDistance
  congr 1
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hi : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hp)).mpr
    nlinarith
  norm_num [Fin.sum_univ_succ, fourEqual]
  simp only [one_div] at hi
  rw [hi]
  nlinarith

lemma bestConstant_pos : 0 < bestConstant := by
  rw [bestConstant, SzarekSharpConstant.rpow_eq_c]
  exact SzarekSharpConstant.c_pos

lemma fourEqual_four_equality : rademacherMean (fourEqual 4) =
    1 / Real.sqrt 2 + bestConstant * extremizerDistance (fourEqual 4) := by
  rw [fourEqual_four_mean, fourEqual_four_distance, bestConstant,
    SzarekSharpConstant.rpow_eq_c]
  exact SzarekSharpConstant.equality_identity.symm

/-- Upper bound on every possible universal constant; this does not prove admissibility. -/
lemma validConstant_le_bestConstant {k : ℝ} (hk : validConstant k) : k ≤ bestConstant := by
  have h := hk 4 (by norm_num) (fourEqual 4) fourEqual_four_unit
  rw [fourEqual_four_mean, fourEqual_four_distance] at h
  rw [bestConstant, SzarekSharpConstant.rpow_eq_c]
  exact SzarekSharpConstant.coefficient_le h

#print axioms Szarek.validConstant_le_bestConstant
#print axioms Szarek.fourEqual_four_equality
end Szarek
