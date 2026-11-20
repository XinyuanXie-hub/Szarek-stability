module

public import MainReduction
public import HaagerupEvaluation
public import LemmaThreeFinal
public import CosineTail
public import SmallerCoefficients

@[expose] public section

open scoped BigOperators
noncomputable section
namespace Szarek

/-- Paper Theorem 1: inequality, optimality, and the padded four-coordinate equality case. -/
theorem theorem1_original :
    validConstant bestConstant ∧
    (∀ c : ℝ, validConstant c → c ≤ bestConstant) ∧
    (∀ n : ℕ, 4 ≤ n → orderedUnit (fourEqual n) ∧
      rademacherMean (fourEqual n) =
        1 / Real.sqrt 2 + bestConstant * extremizerDistance (fourEqual n)) := by
  have hb := main_bounds_of_analytic_inputs (fun _ hs => haagerup_integral_eval hs)
    (lemma2_of_cosine_integrals integral_absoluteCosKernel (fun _ hs => cosine_tail_bound hs))
  refine ⟨hb.1, ?_, ?_⟩
  · intro c hc
    exact validConstant_le_bestConstant hc
  · intro n hn
    exact ⟨fourEqual_unit hn, fourEqual_equality hn⟩

/-- Paper Theorem 2: both bounds and every padded even-coordinate equality case. -/
theorem theorem2_original :
    (∀ (n : ℕ), 2 ≤ n → ∀ a : Fin n → ℝ, orderedUnit a → topTwo a ≤ 1 →
      haagerupF (4 / topTwo a ^ 2) ≤ rademacherMean a ∧
      (3 : ℝ) / 4 + (1 - topTwo a ^ 2) / 24 ≤ haagerupF (4 / topTwo a ^ 2)) ∧
    (∀ (n m : ℕ), 2 ≤ m → 2 * m ≤ n →
      orderedUnit (evenEqual n m) ∧ topTwo (evenEqual n m) ≤ 1 ∧
      rademacherMean (evenEqual n m) = haagerupF (4 / topTwo (evenEqual n m) ^ 2)) := by
  have hb := main_bounds_of_analytic_inputs (fun _ hs => haagerup_integral_eval hs)
    (lemma2_of_cosine_integrals integral_absoluteCosKernel (fun _ hs => cosine_tail_bound hs))
  exact ⟨hb.2, theorem2_equality_family⟩

/-- Theorem 1: the greatest stability coefficient and the four-coordinate equality case.
`IsGreatest S c` means both `c ∈ S` and every member of `S` is at most `c`. -/
theorem theorem1 :
    IsGreatest {c : ℝ | ∀ (n : ℕ) (a : Fin (n + 2) → ℝ), orderedUnit a →
      1 / Real.sqrt 2 + c * extremizerDistance a ≤ rademacherMean a}
      ((2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8) ∧
    (∀ n : ℕ, 4 ≤ n →
      let a : Fin n → ℝ := fun i => if i.val < 4 then 1 / 2 else 0
      rademacherMean a = 1 / Real.sqrt 2 +
        ((2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8) * extremizerDistance a) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro n a ha
    exact theorem1_original.1 (n + 2) (by omega) a ha
  · intro c hc
    apply theorem1_original.2.1 c
    intro n hn a ha
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact hc k a ha
  · intro n hn
    exact (theorem1_original.2.2 n hn).2

/-- Theorem 2: both bounds and equality for every padded even-coordinate vector.
The dimension `n + 2` ranges over exactly the integers at least two. -/
theorem theorem2 :
    (∀ (n : ℕ) (a : Fin (n + 2) → ℝ), orderedUnit a → a 0 + a 1 ≤ 1 →
      haagerupF (4 / (a 0 + a 1) ^ 2) ≤ rademacherMean a ∧
      (3 : ℝ) / 4 + (1 - (a 0 + a 1) ^ 2) / 24 ≤
        haagerupF (4 / (a 0 + a 1) ^ 2)) ∧
    (∀ (n m : ℕ), 2 ≤ m → 2 * m ≤ n →
      let a : Fin n → ℝ :=
        fun i => if i.val < 2 * m then 1 / Real.sqrt (2 * (m : ℝ)) else 0
      rademacherMean a = haagerupF (2 * (m : ℝ))) := by
  constructor
  · intro n a ha ht
    simpa only [topTwo_eq] using
      theorem2_original.1 (n + 2) (by omega) a ha (by simpa only [topTwo_eq] using ht)
  · intro n m hm hn
    change rademacherMean (evenEqual n m) = haagerupF (2 * (m : ℝ))
    rw [← evenEqual_argument hm hn]
    exact (theorem2_original.2 n m hm hn).2.2


/-- The revised formulation recovers every conjunct of the previous challenge. -/
theorem theorem1_recovers_original :
    validConstant bestConstant ∧
    (∀ c : ℝ, validConstant c → c ≤ bestConstant) ∧
    (∀ n : ℕ, 4 ≤ n → orderedUnit (fourEqual n) ∧
      rademacherMean (fourEqual n) =
        1 / Real.sqrt 2 + bestConstant * extremizerDistance (fourEqual n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn a ha
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact theorem1.1.1 k a ha
  · intro c hc
    exact theorem1.1.2 (fun n a ha => hc (n + 2) (by omega) a ha)
  · intro n hn
    exact ⟨fourEqual_unit hn, theorem1.2 n hn⟩

/-- The omitted normalization and top-two conditions are automatic for this family. -/
theorem theorem2_recovers_original :
    (∀ (n : ℕ), 2 ≤ n → ∀ a : Fin n → ℝ, orderedUnit a → topTwo a ≤ 1 →
      haagerupF (4 / topTwo a ^ 2) ≤ rademacherMean a ∧
      (3 : ℝ) / 4 + (1 - topTwo a ^ 2) / 24 ≤ haagerupF (4 / topTwo a ^ 2)) ∧
    (∀ (n m : ℕ), 2 ≤ m → 2 * m ≤ n →
      orderedUnit (evenEqual n m) ∧ topTwo (evenEqual n m) ≤ 1 ∧
      rademacherMean (evenEqual n m) = haagerupF (4 / topTwo (evenEqual n m) ^ 2)) := by
  constructor
  · intro n hn a ha ht
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simpa only [topTwo_eq] using theorem2.1 k a ha (by simpa only [topTwo_eq] using ht)
  · intro n m hm hn
    refine ⟨evenEqual_unit hm hn, evenEqual_topTwo_le_one hm hn, ?_⟩
    rw [evenEqual_argument hm hn]
    exact theorem2.2 n m hm hn

#print axioms Szarek.theorem1_recovers_original
#print axioms Szarek.theorem2_recovers_original
#print axioms Szarek.theorem1
#print axioms Szarek.theorem2

end Szarek
