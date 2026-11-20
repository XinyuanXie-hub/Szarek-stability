module

public import EqualSigns
public import EvenGamma
public import EvenGeometry

@[expose] public section

namespace Szarek

theorem theorem2_equality_family (n m : ℕ) (hm : 2 ≤ m) (hn : 2 * m ≤ n) :
    orderedUnit (evenEqual n m) ∧ topTwo (evenEqual n m) ≤ 1 ∧
      rademacherMean (evenEqual n m) = haagerupF (4 / topTwo (evenEqual n m) ^ 2) := by
  refine ⟨evenEqual_unit hm hn, evenEqual_topTwo_le_one hm hn, ?_⟩
  rw [evenEqual_argument hm hn, evenEqual_mean_padding hn,
    rademacherMean_evenEqual_base m (by omega), haagerupF_even m (by omega)]


#print axioms Szarek.theorem2_equality_family
end Szarek
