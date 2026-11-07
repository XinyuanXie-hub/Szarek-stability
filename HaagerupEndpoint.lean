import GammaBounds
import HaagerupConvexity

open Filter Set
open scoped Topology
noncomputable section
namespace Szarek

def inverseFExt : ℝ → ℝ :=
  Function.update (fun u : ℝ => haagerupF (1 / u)) 0 (Real.sqrt (2 / Real.pi))

lemma inverseFExt_pos {u : ℝ} (hu : 0 < u) : inverseFExt u = haagerupF (1 / u) :=
  Function.update_of_ne (ne_of_gt hu) _ _

lemma differentiableAt_inverseF {u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (fun u : ℝ => haagerupF (1 / u)) u := by
  apply DifferentiableAt.comp u (f := fun u : ℝ => 1 / u) (g := haagerupF)
  · exact differentiableAt_haagerupF (one_div_pos.mpr hu)
  · exact (differentiableAt_const 1).div differentiableAt_id hu.ne'

lemma inverseFExt_eventuallyEq {u : ℝ} (hu : 0 < u) :
    inverseFExt =ᶠ[𝓝 u] (fun u : ℝ => haagerupF (1 / u)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hu] with t ht
  exact inverseFExt_pos ht

lemma continuousOn_inverseFExt : ContinuousOn inverseFExt (Ici 0) := by
  intro u hu
  have hu0 : 0 ≤ u := hu
  rcases eq_or_lt_of_le hu0 with rfl | hu
  · apply continuousWithinAt_update_same.mpr
    have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
      ext x
      simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
      constructor
      · rintro ⟨hx, hne⟩
        exact lt_of_le_of_ne hx (Ne.symm hne)
      · intro hx
        exact ⟨hx.le, hx.ne'⟩
    rw [hset]
    simpa only [one_div, Function.comp_def] using tendsto_haagerupF.comp tendsto_inv_nhdsGT_zero
  · exact ((differentiableAt_inverseF hu).congr_of_eventuallyEq
      (inverseFExt_eventuallyEq hu)).continuousAt.continuousWithinAt

lemma convexOn_inverseFExt : ConvexOn ℝ (Ici 0) inverseFExt := by
  have hm := haagerupF_inverse_convex.monotoneOn_deriv (fun u hu => differentiableAt_inverseF hu)
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) continuousOn_inverseFExt
  · intro u hu
    have hu0 : 0 < u := by simpa using hu
    exact ((differentiableAt_inverseF hu0).congr_of_eventuallyEq
      (inverseFExt_eventuallyEq hu0)).differentiableWithinAt
  · intro x hx y hy hxy
    have hx0 : 0 < x := by simpa using hx
    have hy0 : 0 < y := by simpa using hy
    rw [(inverseFExt_eventuallyEq hx0).deriv_eq, (inverseFExt_eventuallyEq hy0).deriv_eq]
    exact hm hx0 hy0 hxy

lemma haagerupF_chord {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    haagerupF (4 / q) ≤ (1 - q) * Real.sqrt (2 / Real.pi) + (3 / 4 : ℝ) * q := by
  have h := convexOn_inverseFExt.2
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show (1 / 4 : ℝ) ∈ Ici 0 by norm_num)
    (show 0 ≤ 1 - q by linarith) hq.le (show 1 - q + q = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  have harg : q * (1 / 4) > 0 := by positivity
  rw [inverseFExt_pos harg] at h
  have hzero : inverseFExt 0 = Real.sqrt (2 / Real.pi) := Function.update_self ..
  have hquarter : inverseFExt (1 / 4) = (3 : ℝ) / 4 := by
    rw [inverseFExt_pos (by norm_num)]
    norm_num [haagerupF_four]
  rw [hzero, hquarter] at h
  have he : 1 / (q * (1 / 4)) = 4 / q := by field_simp
  rw [he] at h
  simpa only [mul_comm q] using h

#print axioms Szarek.haagerupF_chord
#print axioms Szarek.convexOn_inverseFExt
end Szarek
