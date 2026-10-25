-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.IndexedGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedDirections

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem ClosedFiniteFrostman.indexed {δ C : ℝ} {S : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) : IndexedFrostman δ C (fun x : S => (x : Plane)) := by
  intro x r hr
  have heq : (Finset.univ.filter (fun y : S => dist (y : Plane) x ≤ r)).card =
      (S.filter (fun y => dist y x ≤ r)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun y => if dist y x ≤ r then (1 : ℕ) else 0)
  rw [heq, Fintype.card_coe]
  exact hF.filter_closedBall x r hr

/-- Frostman counting bounds the cardinality of any indexed set of small
diameter. The map may have repetitions. -/
theorem IndexedFrostman.card_of_diameter {I : Type*} [Fintype I] {f : I → Plane}
    {δ C r : ℝ} (hF : IndexedFrostman δ C f) (S : Finset I)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hδr : δ ≤ r)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, dist (f i) (f j) ≤ r) :
    (S.card : ℝ) ≤ C * r * (Fintype.card I : ℝ) := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨j, hj⟩ := hS
    have hsub : S ⊆ Finset.univ.filter (fun i => dist (f i) (f j) ≤ r) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiam i hi j hj⟩
    have hc : (S.card : ℝ) ≤ ((Finset.univ.filter (fun i => dist (f i) (f j) ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans (hF (f j) r hδr)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
    positivity

end WangZahlLot.Obl.wz_separated_projection_dichotomy
