module

public import FiniteSharpness

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Szarek

lemma sum_signs_snoc {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ ε, f ε) = ∑ b : Bool, ∑ ε : Fin n → Bool, f (Fin.snoc ε b) := by
  calc
    _ = ∑ p : Bool × (Fin n → Bool), f (Fin.snoc p.2 p.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).symm f _
        (fun ε => by
          change f ε = f (Fin.snoc (Fin.init ε) (ε (Fin.last n)))
          rw [Fin.snoc_init_self])
    _ = _ := Fintype.sum_prod_type _

lemma rademacherMean_snoc_zero {n : ℕ} (a : Fin n → ℝ) :
    rademacherMean (Fin.snoc a 0) = rademacherMean a := by
  unfold rademacherMean
  rw [sum_signs_snoc]
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    zero_mul, add_zero]
  simp only [Fintype.sum_bool, pow_succ]
  ring

lemma fourEqual_succ {n : ℕ} (hn : 4 ≤ n) :
    fourEqual (n + 1) = Fin.snoc (fourEqual n) 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [fourEqual, Nat.not_lt.mpr hn]
  · simp [fourEqual]

lemma fourEqual_mean {n : ℕ} (hn : 4 ≤ n) :
    rademacherMean (fourEqual n) = 3 / 4 := by
  induction n, hn using Nat.le_induction with
  | base => exact fourEqual_four_mean
  | succ n hn ih => rw [fourEqual_succ hn, rademacherMean_snoc_zero, ih]

lemma fourEqual_distance {n : ℕ} (hn : 4 ≤ n) :
    extremizerDistance (fourEqual n) = Real.sqrt (2 - Real.sqrt 2) := by
  induction n, hn using Nat.le_induction with
  | base => exact fourEqual_four_distance
  | succ n hn ih =>
    rw [fourEqual_succ hn]
    have h2 : ¬n ≤ 1 := by omega
    simpa [extremizerDistance, Fin.sum_univ_castSucc, h2] using ih

lemma fourEqual_unit {n : ℕ} (hn : 4 ≤ n) : orderedUnit (fourEqual n) := by
  have hsum : ∑ i, (fourEqual n i) ^ 2 = 1 := by
    induction n, hn using Nat.le_induction with
    | base => exact fourEqual_four_unit.2.2
    | succ n hn ih =>
      rw [fourEqual_succ hn]
      simpa [Fin.sum_univ_castSucc] using ih
  refine ⟨?_, ?_, hsum⟩
  · intro i j hij
    simp only [fourEqual]
    split_ifs with hj hi
    · rfl
    · have : i.val < 4 := lt_of_le_of_lt hij hj
      contradiction
    · norm_num
    · rfl
  · intro i
    simp only [fourEqual]
    split_ifs <;> norm_num

lemma fourEqual_equality {n : ℕ} (hn : 4 ≤ n) :
    rademacherMean (fourEqual n) =
      1 / Real.sqrt 2 + bestConstant * extremizerDistance (fourEqual n) := by
  rw [fourEqual_mean hn, fourEqual_distance hn, bestConstant,
    SzarekSharpConstant.rpow_eq_c]
  exact SzarekSharpConstant.equality_identity.symm

#print axioms Szarek.fourEqual_equality
#print axioms Szarek.fourEqual_unit
end Szarek
