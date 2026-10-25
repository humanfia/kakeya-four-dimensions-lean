-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripLocalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripFrostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Strip localization for a finite small-diameter set, with line counting
bounds at every scale, including radii greater than one. -/
theorem exists_small_diameter_strip_localization {E : Finset Plane} (hE : E.Nonempty)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ 1 / 2) {δ ζ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 ≤ ζ) :
    ∃ (n : Plane) (c w : ℝ) (E' : Finset Plane), ‖n‖ = 1 ∧ δ ≤ w ∧ w ≤ 1 ∧
      E' ⊆ E ∧ E'.Nonempty ∧ (∀ x ∈ E', |inner ℝ x n - c| < w) ∧
      w ^ ζ * (E.card : ℝ) / 2 ≤ (E'.card : ℝ) ∧ StripFrostman δ 2 ζ w E' := by
  classical
  obtain ⟨x₀, hx₀⟩ := hE
  let n₀ : {n : Plane // ‖n‖ = 1} := ⟨EuclideanSpace.single 0 1, by simp⟩
  let U (i : {n : Plane // ‖n‖ = 1} × ℝ) (r : ℝ) := Strip i.1.val i.2 r
  have hcover : ∀ x ∈ E, x ∈ U (n₀, inner ℝ x₀ n₀) 1 := by
    intro x hx
    change |inner ℝ x n₀ - inner ℝ x₀ n₀| < 1
    rw [← inner_sub_left]
    calc |inner ℝ (x - x₀) n₀| ≤ ‖x - x₀‖ * ‖(n₀ : Plane)‖ := abs_real_inner_le_norm _ _
      _ = dist x x₀ := by rw [n₀.property, mul_one, dist_eq_norm]
      _ ≤ 1 / 2 := hdiam x hx x₀ hx₀
      _ < 1 := by norm_num
  obtain ⟨i, w, E', hδw, hw1, hE', hret, htwo⟩ :=
    exists_weighted_localization E U (n₀, inner ℝ x₀ n₀) hδ hδ1 hζ hcover
  have hw : 0 < w := hδ.trans_le hδw
  have hEpos : (0 : ℝ) < E.card := by exact_mod_cast Finset.card_pos.mpr ⟨x₀, hx₀⟩
  have hE'pos : (0 : ℝ) < E'.card := (by positivity : 0 < w ^ ζ * (E.card : ℝ) / 2).trans_le hret
  refine ⟨i.1, i.2, w, E', i.1.property, hδw, hw1, ?_, ?_, ?_, hret, ?_⟩
  · intro x hx
    exact ((hE' x).mp hx).1
  · exact Finset.card_pos.mp (by exact_mod_cast hE'pos)
  · intro x hx
    exact ((hE' x).mp hx).2
  · intro n c r hn hδr
    by_cases hr1 : r ≤ 1
    · exact htwo (⟨n, hn⟩, c) r hδr hr1
    · have hr : 1 ≤ r := (lt_of_not_ge hr1).le
      have hratio : 1 ≤ r / w := (one_le_div hw).mpr (hw1.trans hr)
      have hp : 1 ≤ (r / w) ^ ζ := Real.one_le_rpow hratio hζ
      have hc : ((E'.filter (fun x => |inner ℝ x n - c| < r)).card : ℝ) ≤ E'.card := by
        exact_mod_cast Finset.card_filter_le E' _
      exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) E'.card])

end WangZahlLot.Obl.wz_separated_projection_dichotomy
