-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.BallTests.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Grid
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Dyadic

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set Metric
open scoped ENNReal

namespace Grid

abbrev TestIndex := Σ _ : ℕ, Fin 3 → ℤ

noncomputable def spacing (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k / 16

lemma spacing_pos (k : ℕ) : 0 < spacing k := by unfold spacing; positivity

noncomputable def tests (K : ℕ) (R : ℝ) : Finset TestIndex :=
  (Finset.range (K + 1)).sigma fun k =>
    WangZahlLot.Obl.wz_balanced_cluster_cover.box (spacing k) (0 : E) R

noncomputable def testBall (z : TestIndex) : Set E :=
  ball (point (spacing z.1) z.2) (4 * spacing z.1)

lemma testBall_measurable (z : TestIndex) : MeasurableSet (testBall z) := measurableSet_ball

lemma sum_tests_inter_le (K : ℕ) (R : ℝ) (P : Set E) (hP : MeasurableSet P) :
    ∑ z ∈ tests K R, volume (P ∩ testBall z) ≤ (1000 * (K + 1 : ℕ) : ℝ≥0∞) * volume P := by
  unfold tests testBall
  rw [Finset.sum_sigma]
  calc (∑ k ∈ Finset.range (K + 1),
        ∑ g ∈ WangZahlLot.Obl.wz_balanced_cluster_cover.box (spacing k) (0 : E) R,
          volume (P ∩ ball (point (spacing k) g) (4 * spacing k)))
      ≤ ∑ k ∈ Finset.range (K + 1), 1000 * volume P := by
        apply Finset.sum_le_sum
        intro k _
        exact sum_inter_ball_le (spacing_pos k) _ P hP
    _ = _ := by simp [mul_assoc, mul_left_comm]

lemma exists_comparison_test {P : Set E} (hPc : Convex ℝ P)
    {R a : ℝ} (hPbound : P ⊆ closedBall 0 R) (ha : 0 < a)
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ K < 2 * a) {p : E} (hp : p ∈ P)
    {r : ℝ} (har : a ≤ r) (hr1 : r ≤ 1) :
    ∃ z ∈ tests K R, p ∈ testBall z ∧ testBall z ⊆ ball p r ∧
      ENNReal.ofReal (1 / 512 : ℝ) * volume (P ∩ ball p r) ≤ volume (P ∩ testBall z) := by
  obtain ⟨k, hk, hklo, hkhi⟩ := exists_dyadic_between ha hK har hr1
  let g := WangZahlLot.Obl.wz_balanced_cluster_cover.cell (spacing k) p
  have hg : g ∈ WangZahlLot.Obl.wz_balanced_cluster_cover.box (spacing k) (0 : E) R := by
    apply WangZahlLot.Obl.wz_balanced_cluster_cover.cell_mem_box (spacing_pos k)
    simpa only [mem_closedBall, dist_eq_norm] using hPbound hp
  refine ⟨⟨k, g⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), hg⟩, ?_⟩
  exact ball_comparison hPc hp (spacing_pos k)
    (show r / 16 ≤ spacing k by dsimp [spacing]; linarith)
    (show spacing k < r / 8 by dsimp [spacing]; linarith)

end Grid
end WangZahlLot.Obl.wz_regular_transverse_affine_cells
